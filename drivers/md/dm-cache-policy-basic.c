/*
 * Copyright (C) 2012,2013 Red Hat. All rights reserved.
 *
 * This file is released under the GPL.
 *
 * A selection of cache replacement policies for the dm-cache target:
 *   basic
 *   dumb
 *   fifo
 *   filo
 *   lfu
 *   lfu_ws
 *   lru
 *   mfu
 *   mfu_ws
 *   mru
 *   multiqueue
 *   multiqueue_ws
 *   noop
 *   random
 *   q2
 *   twoqueue
 */

#include "dm-cache-policy.h"
#include "dm-cache-policy-internal.h"
#include "dm.h"

#include <linux/btree.h>
#include <linux/hash.h>
#include <linux/list.h>
#include <linux/module.h>
#include <linux/random.h>
#include <linux/slab.h>
#include <linux/vmalloc.h>

#define DM_MSG_PREFIX "cache-policy-basic"

/* Cache input queue defines. */
#define	READ_PROMOTE_THRESHOLD	4U	/* Minimum read cache in queue promote per element threshold. */
#define	WRITE_PROMOTE_THRESHOLD	8U	/* Minimum write cache in queue promote per element threshold. */

/* Default "multiqueue" queue timeout. */
#define	MQ_QUEUE_TMO_DEFAULT	(600UL * HZ)	/* Default seconds queue maximum lifetime per entry. FIXME: dynamic? */

/*----------------------------------------------------------------------------*/
/*
 * Large, sequential ios are probably better left on the origin device since
 * spindles tend to have good bandwidth.
 *
 * The io_tracker tries to spot when the io is in
 * one of these sequential modes.
 *
 * Two thresholds to switch between random and sequential io mode are defaulting
 * as follows and can be adjusted via the targets constructor and message interfaces.
 */
#define RANDOM_THRESHOLD_DEFAULT 4
#define SEQUENTIAL_THRESHOLD_DEFAULT 4 /* Cache blocks */

static struct kmem_cache *basic_entry_cache;
static struct kmem_cache *track_entry_cache;

enum io_pattern {
	PATTERN_SEQUENTIAL,
	PATTERN_RANDOM
};

struct io_tracker {
	sector_t next_start_osector, nr_seq_sectors;

	unsigned nr_rand_samples;
	enum io_pattern pattern;

	unsigned long thresholds[2];
};

static void iot_init(struct io_tracker *t)
{
	t->pattern = PATTERN_RANDOM;
	t->nr_seq_sectors = t->nr_rand_samples = t->next_start_osector = 0;
	t->thresholds[PATTERN_SEQUENTIAL] = SEQUENTIAL_THRESHOLD_DEFAULT;
	t->thresholds[PATTERN_RANDOM] = RANDOM_THRESHOLD_DEFAULT;
}

static bool iot_sequential_pattern(struct io_tracker *t)
{
	return t->pattern == PATTERN_SEQUENTIAL;
}

static void iot_update_stats(struct io_tracker *t, struct bio *bio)
{
	sector_t sectors = bio_sectors(bio);

	if (bio->bi_sector == t->next_start_osector) {
		t->nr_seq_sectors += sectors;

	} else {
		/*
		 * Just one non-sequential IO is
		 * enough to reset the counters.
		 */
		if (t->nr_seq_sectors)
			t->nr_seq_sectors = t->nr_rand_samples = 0;

		t->nr_rand_samples++;
	}

	t->next_start_osector = bio->bi_sector + sectors;
}

static void iot_check_for_pattern_switch(struct io_tracker *t,
					 sector_t block_size)
{
	if (iot_sequential_pattern(t)) {
		if (t->nr_rand_samples >= t->thresholds[PATTERN_RANDOM]) {
			t->pattern = PATTERN_RANDOM;
			t->nr_seq_sectors = t->nr_rand_samples = 0;
		}

	} else if (t->nr_seq_sectors >= t->thresholds[PATTERN_SEQUENTIAL] * block_size) {
		t->pattern = PATTERN_SEQUENTIAL;
		t->nr_seq_sectors = t->nr_rand_samples = 0;
	}
}

/*----------------------------------------------------------------------------*/

/*----------------------------------------------------------------*/

/* The common cache entry part for all policies. */
struct common_entry {
	struct hlist_node hlist;
	struct list_head list;
	dm_oblock_t oblock;
	unsigned count[2][2];
	unsigned tick;
};

/* Cache entry struct. */
struct basic_cache_entry {
	struct common_entry ce;

	struct list_head walk, dirty;
	dm_cblock_t cblock;
	unsigned long expire;
	unsigned saved;
};

/* Pre and post cache queue entry. */
struct track_queue_entry {
	struct common_entry ce;
};

enum policy_type {
	p_dumb,
	p_fifo,
	p_filo,
	p_lru,
	p_mru,
	p_lfu,
	p_lfu_ws,
	p_mfu,
	p_mfu_ws,
	p_multiqueue,
	p_multiqueue_ws,
	p_noop,
	p_random,
	p_q2,
	p_twoqueue,
	p_basic	/* The default selecting one of the above. */
};

struct basic_policy;
typedef void (*queue_add_fn)(struct basic_policy *, struct list_head *);
typedef void (*queue_del_fn)(struct basic_policy *, struct list_head *);
typedef struct list_head * (*queue_evict_fn)(struct basic_policy *);

struct queue_fns {
	queue_add_fn add;
	queue_del_fn del;
	queue_evict_fn evict;
};

static struct list_head *queue_evict_multiqueue(struct basic_policy *);
static void queue_add_noop(struct basic_policy *, struct list_head *);

#define	IS_FILO_MRU(basic)			(basic->queues.fns->add == &queue_add_filo_mru)
#define	IS_MFU(basic)			(basic->queues.fns->del == &queue_del_mfu)

#define	IS_LFU(basic)			(basic->queues.fns->add == &queue_add_lfu)
#define	IS_MULTIQUEUE(basic)		(basic->queues.fns->evict == &queue_evict_multiqueue)
#define	IS_Q2(basic)			(basic->queues.fns->add == &queue_add_q2)
#define	IS_TWOQUEUE(basic)			(basic->queues.fns->add == &queue_add_twoqueue)
#define	IS_DUMB(basic)			(basic->queues.fns->add == &queue_add_dumb)
#define	IS_NOOP(basic)			(basic->queues.fns->add == &queue_add_noop)

#define	IS_FIFO_FILO(basic)			(basic->queues.fns->del == &queue_del_fifo_filo)
#define	IS_Q2_TWOQUEUE(basic)		(basic->queues.fns->evict == &queue_evict_q2_twoqueue)
#define	IS_MULTIQUEUE_Q2_TWOQUEUE(basic)	(basic->queues.fns->del == &queue_del_multiqueue)
#define	IS_LFU_MFU_WS(basic)		(basic->queues.fns->evict == &queue_evict_lfu_mfu)

static unsigned next_power(unsigned n, unsigned min)
{
	return roundup_pow_of_two(max(n, min));
}

struct hash {
	struct hlist_head *table;
	dm_block_t hash_bits;
	unsigned nr_buckets;
};

enum count_type {
	T_SECTORS,
	T_HITS
};
struct track_queue {
	struct hash hash;
	struct track_queue_entry *elts;
	struct list_head used, free;
	unsigned count[2][2], size, nr_elts;
};

struct basic_policy {
	struct dm_cache_policy policy;
	struct mutex lock;

	struct io_tracker tracker;

	sector_t origin_size, block_size;
	unsigned block_shift, promote_threshold[2], hits;

	struct {
		/* add/del/evict entry abstractions. */
		struct queue_fns *fns;

		/* Multiqueue policies. */
		struct list_head *mq;
		unsigned long mq_tmo;

		/* Pre- and post-cache queues. */
		struct track_queue pre, post;
		enum count_type ctype;

		/*
		 * FIXME:
		 * mempool based kernel lib btree used for lfu,mfu,lfu_ws and mfu_ws
		 *
		 * Now preallocating all objects on creation in order to avoid OOM deadlock.
		 *
		 * Replace with priority heap.
		 */
		struct btree_head32 fu_head;
		mempool_t *fu_pool;

		unsigned nr_mqueues, twoqueue_q0_size, twoqueue_q0_max_elts;
		struct list_head free; /* Free cache entry list */
		struct list_head used; /* Used cache entry list */
		struct list_head walk; /* walk_mappings uses this list */
		struct list_head dirty;/* writeback_work    " */
	} queues;

	/* MINORME: allocate only for multiqueue? */
	unsigned long jiffies;

	/*
	 * Keeps track of time, incremented by the core.  We use this to
	 * avoid attributing multiple hits within the same tick.
	 *
	 * tick_extern is the one updated by the core target.
	 * It's copied to tick at the start of the map function.
	 */
	unsigned tick, tick_extern;

	/*
	 * We know exactly how many cblocks will be needed, so we can
	 * allocate them up front.
	 */
	/* FIXME: unify with track_queue? */
	dm_cblock_t cache_size;
	unsigned find_free_nr_words;
	unsigned find_free_last_word;
	struct hash chash;
	unsigned cache_count[2][2];

	/* Cache entry allocation bitset. */
	unsigned long *allocation_bitset;
	dm_cblock_t nr_cblocks_allocated;

	struct basic_cache_entry **tmp_entries;
};

/*----------------------------------------------------------------------------*/
/* Low-level functions. */
static struct basic_policy *to_basic_policy(struct dm_cache_policy *p)
{
	return container_of(p, struct basic_policy, policy);
}

static int to_rw(struct bio *bio)
{
	return (bio_data_dir(bio) == WRITE) ? 1 : 0;
}

/*----------------------------------------------------------------------------*/
/* Low-level queue functions. */
static void queue_init(struct list_head *q)
{
	INIT_LIST_HEAD(q);
}

static bool queue_empty(struct list_head *q)
{
	return list_empty(q);
}

static void queue_add(struct list_head *q, struct list_head *elt)
{
	list_add(elt, q);
}

static void queue_add_tail(struct list_head *q, struct list_head *elt)
{
	list_add_tail(elt, q);
}

static void queue_del(struct list_head *elt)
{
	if (!list_empty(elt))
		list_del_init(elt);
}

static struct list_head *queue_pop(struct list_head *q)
{
	struct list_head *r = q->next;

	BUG_ON(!r);
	list_del(r);

	return r;
}

static void queue_move_tail(struct list_head *q, struct list_head *elt)
{
	list_move_tail(elt, q);
}

/*----------------------------------------------------------------------------*/

/* Allocate/free various resources. */
static int alloc_hash(struct hash *hash, unsigned elts)
{
	hash->nr_buckets = next_power(elts >> 4, 16);
	hash->hash_bits = ffs(hash->nr_buckets) - 1;
	hash->table = vzalloc(sizeof(*hash->table) * hash->nr_buckets);

	return hash->table ? 0 : -ENOMEM;
}

static void free_hash(struct hash *hash)
{
	if (hash->table)
		vfree(hash->table);
}

/* Free/alloc basic cache entry structures. */
static void free_cache_entries(struct basic_policy *basic)
{
	struct basic_cache_entry *e, *tmp;

	list_for_each_entry_safe(e, tmp, &basic->queues.free, ce.list)
		kmem_cache_free(basic_entry_cache, e);

	list_for_each_entry_safe(e, tmp, &basic->queues.walk, walk)
		kmem_cache_free(basic_entry_cache, e);
}

static int alloc_cache_blocks_with_hash(struct basic_policy *basic, unsigned cache_size)
{
	int r = -ENOMEM;
	unsigned u = cache_size;

	basic->nr_cblocks_allocated = to_cblock(0);

	while (u--) {
		struct basic_cache_entry *e = kmem_cache_zalloc(basic_entry_cache, GFP_KERNEL);

		if (!e)
			goto bad_cache_alloc;

		queue_init(&e->dirty);
		queue_add(&basic->queues.free, &e->ce.list);
	}

	/* Cache entries hash. */
	r = alloc_hash(&basic->chash, cache_size);
	if (!r)
		return 0;

bad_cache_alloc:
	free_cache_entries(basic);

	return r;
}

static void free_cache_blocks_and_hash(struct basic_policy *basic)
{
	free_hash(&basic->chash);
	free_cache_entries(basic);
}

static void free_track_queue(struct track_queue *q)
{
	struct track_queue_entry *tqe, *tmp;

	free_hash(&q->hash);

	list_splice(&q->used, &q->free);
	list_for_each_entry_safe(tqe, tmp, &q->free, ce.list)
		kmem_cache_free(track_entry_cache, tqe);
}

static int alloc_track_queue_with_hash(struct track_queue *q, unsigned elts)
{
	int r = -ENOMEM;
	unsigned u = elts;

	while (u--) {
		struct track_queue_entry *tqe = kmem_cache_zalloc(track_entry_cache, GFP_KERNEL);

		if (!tqe)
			goto bad_tq_alloc;

		queue_add(&q->free, &tqe->ce.list);
	}


	r = alloc_hash(&q->hash, elts);
	if (!r)
		return 0;

bad_tq_alloc:
	free_track_queue(q);

	return r;
}

static int alloc_multiqueues(struct basic_policy *basic, unsigned mqueues)
{
	/* Multiqueue heads. */
	basic->queues.nr_mqueues = mqueues;
	basic->queues.mq = vzalloc(sizeof(*basic->queues.mq) * mqueues);
	if (!basic->queues.mq)
		return -ENOMEM;

	while (mqueues--)
		queue_init(&basic->queues.mq[mqueues]);

	return 0;
}

static void free_multiqueues(struct basic_policy *basic)
{
	vfree(basic->queues.mq);
}

static struct basic_cache_entry *alloc_cache_entry(struct basic_policy *basic)
{
	struct basic_cache_entry *e;
	struct list_head *free = &basic->queues.free;

	BUG_ON(from_cblock(basic->nr_cblocks_allocated) >= from_cblock(basic->cache_size));

	if (queue_empty(free))
		e = NULL;

	else {
		e = list_entry(queue_pop(free), struct basic_cache_entry, ce.list);
		basic->nr_cblocks_allocated = to_cblock(from_cblock(basic->nr_cblocks_allocated) + 1);

	}

	return e;
}

static void alloc_cblock(struct basic_policy *basic, dm_cblock_t cblock)
{
	BUG_ON(from_cblock(cblock) >= from_cblock(basic->cache_size));
	BUG_ON(test_bit(from_cblock(cblock), basic->allocation_bitset));
	set_bit(from_cblock(cblock), basic->allocation_bitset);
}

static void free_cblock(struct basic_policy *basic, dm_cblock_t cblock)
{
	BUG_ON(from_cblock(cblock) >= from_cblock(basic->cache_size));
	BUG_ON(!test_bit(from_cblock(cblock), basic->allocation_bitset));
	clear_bit(from_cblock(cblock), basic->allocation_bitset);
}

static void queue_add_twoqueue(struct basic_policy *basic, struct list_head *elt);
static bool any_free_cblocks(struct basic_policy *basic)
{
	if (IS_TWOQUEUE(basic)) {
		/*
		 * Only allow a certain amount of the total cache size in queue 0
		 * (cblocks with hit count 1).
		 */
		if (basic->queues.twoqueue_q0_size == basic->queues.twoqueue_q0_max_elts)
			return false;
	}

	return !queue_empty(&basic->queues.free);
}

/*----------------------------------------------------------------*/

static unsigned bit_set_nr_words(unsigned nr_cblocks)
{
	return dm_div_up(nr_cblocks, BITS_PER_LONG);
}

static unsigned long *alloc_bitset(unsigned nr_cblocks)
{
	return vzalloc(sizeof(unsigned long) * bit_set_nr_words(nr_cblocks));
}

static void free_bitset(unsigned long *bits)
{
	if (bits)
		vfree(bits);
}
/*----------------------------------------------------------------------------*/

/* Hash functions (lookup, insert, remove). */
static struct common_entry *__lookup_common_entry(struct hash *hash, dm_oblock_t oblock)
{
	unsigned h = hash_64(from_oblock(oblock), hash->hash_bits);
	struct common_entry *cur;
	struct hlist_head *bucket = &hash->table[h];

	hlist_for_each_entry(cur, bucket, hlist) {
		if (cur->oblock == oblock) {
			/* Move upfront bucket for faster access. */
			hlist_del(&cur->hlist);
			hlist_add_head(&cur->hlist, bucket);
			return cur;
		}
	}

	return NULL;
}

static struct basic_cache_entry *lookup_cache_entry(struct basic_policy *basic,
						    dm_oblock_t oblock)
{
	struct common_entry *ce = IS_NOOP(basic) ? NULL :
		__lookup_common_entry(&basic->chash, oblock);

	return ce ? container_of(ce, struct basic_cache_entry, ce) : NULL;
}

static void insert_cache_hash_entry(struct basic_policy *basic, struct basic_cache_entry *e)
{
	unsigned h = hash_64(from_oblock(e->ce.oblock), basic->chash.hash_bits);

	hlist_add_head(&e->ce.hlist, &basic->chash.table[h]);
}

static void remove_cache_hash_entry(struct basic_policy *basic, struct basic_cache_entry *e)
{
	hlist_del(&e->ce.hlist);
}

/* Cache track queue. */
static struct track_queue_entry *lookup_track_queue_entry(struct track_queue *q,
							  dm_oblock_t oblock)
{
	struct common_entry *ce = __lookup_common_entry(&q->hash, oblock);

	return ce ? container_of(ce, struct track_queue_entry, ce) : NULL;
}

static void insert_track_queue_hash_entry(struct track_queue *q,
					  struct track_queue_entry *tqe)
{
	unsigned h = hash_64(from_oblock(tqe->ce.oblock), q->hash.hash_bits);

	hlist_add_head(&tqe->ce.hlist, &q->hash.table[h]);
}

static void remove_track_queue_hash_entry(struct track_queue_entry *tqe)
{
	hlist_del(&tqe->ce.hlist);
}
/*----------------------------------------------------------------------------*/

/* Out of cache queue support functions. */
static struct track_queue_entry *pop_track_queue(struct track_queue *q)
{
	struct track_queue_entry *r;

	if (queue_empty(&q->free)) {
		unsigned t, u, end = ARRAY_SIZE(r->ce.count[T_HITS]);

		BUG_ON(queue_empty(&q->used));
		r = list_entry(queue_pop(&q->used), struct track_queue_entry, ce.list);
		remove_track_queue_hash_entry(r);
		q->size--;

		for (t = 0; t < end; t++)
			for (u = 0; u < end; u++)
				q->count[t][u] -= q->count[t][u];

		memset(r, 0, sizeof(*r));

	} else
		r = list_entry(queue_pop(&q->free), struct track_queue_entry, ce.list);

	return r;
}

/* Retrieve track entry from free list _or_ evict one from track queue. */
static struct track_queue_entry *
pop_add_and_insert_track_queue_entry(struct track_queue *q, dm_oblock_t oblock)
{
	struct track_queue_entry *r = pop_track_queue(q);

	r->ce.oblock = oblock;
	queue_add_tail(&q->used, &r->ce.list);
	insert_track_queue_hash_entry(q, r);
	q->size++;

	return r;
}

static unsigned ctype_threshold(struct basic_policy *basic, unsigned th)
{
	return th << (basic->queues.ctype == T_HITS ? 0 : basic->block_shift);
#if 0
	return th << (basic->queues.ctype == T_HITS ? 3 : basic->block_shift + 4);
#endif
}

#define	MAX_TO_AVERAGE	20
static bool sum_up(struct basic_policy *basic, struct basic_cache_entry *e, unsigned *total, unsigned *nr)
{
	unsigned rw;

	for (rw = 0; rw < 2; rw++)
		*total += e->ce.count[basic->queues.ctype][rw];

	return ++*nr == MAX_TO_AVERAGE;
}

static void calculate_rw_threshold(struct basic_policy *basic)
{
	if (++basic->hits > 1024U) {
		unsigned nr = 0, rw, total = 0;
		struct basic_cache_entry *e;

		basic->hits = 0;

		if (IS_MULTIQUEUE(basic)) {
			unsigned queues = basic->queues.nr_mqueues;

			while (queues--) {
				list_for_each_entry_reverse(e, &basic->queues.mq[queues], ce.list)
					if (sum_up(basic, e, &total, &nr))
						goto out;
			}

		} else {
			list_for_each_entry_reverse(e, &basic->queues.walk, walk)
				if (sum_up(basic, e, &total, &nr))
					goto out;
		}

out:
		for (rw = 0; rw < 2; rw++) {
			basic->promote_threshold[rw] = nr ? total / nr : ctype_threshold(basic, rw ? WRITE_PROMOTE_THRESHOLD : READ_PROMOTE_THRESHOLD);

			if (basic->promote_threshold[rw] * nr < total)
				basic->promote_threshold[rw] += ctype_threshold(basic, rw + 1);
		}
#if 0
		pr_alert("promote thresholds = %u/%u queue stats = %u/%u\n",
			 basic->promote_threshold[0], basic->promote_threshold[1], basic->queues.pre.size, basic->queues.post.size);
#endif
	}
}

/*
 * Has this entry already been updated?
 */
static bool updated_this_tick(struct basic_policy *basic, struct common_entry *ce)
{
	return ce->tick == basic->tick;
}
/* Add or update track queue entry. */
static struct track_queue_entry *
update_track_queue(struct basic_policy *basic, struct track_queue *q, dm_oblock_t oblock,
		   int rw, unsigned hits, sector_t sectors)
{
	struct track_queue_entry *r = lookup_track_queue_entry(q, oblock);

#define SINGLE_COUNT	1
/* FIXME: TESTME: */
#if SINGLE_COUNT
rw = 0;
#endif

	if (r) {
		if (updated_this_tick(basic, &r->ce))
			return r;

		queue_move_tail(&q->used, &r->ce.list);

	} else {
		r = pop_add_and_insert_track_queue_entry(q, oblock);
		BUG_ON(!r);
	}

	r->ce.tick = basic->tick;

	r->ce.count[T_HITS][rw] += hits;
	r->ce.count[T_SECTORS][rw] += sectors;
	q->count[T_HITS][rw] += hits;
	q->count[T_SECTORS][rw] += sectors;

	return r;
}

/* Get hit/sector counts from track queue entry if exists and delete the entry. */
static void get_any_counts_from_track_queue(struct track_queue *q,
					    struct basic_cache_entry *e,
					    dm_oblock_t oblock)
{
	struct track_queue_entry *tqe = lookup_track_queue_entry(q, oblock);

	if (tqe) {
		/*
		 * On track queue -> retrieve memorized hit count and sectors
		 * in order to sort into appropriate queue on add_cache_entry().
		 */
		unsigned t, u, end = ARRAY_SIZE(e->ce.count[T_HITS]);

		remove_track_queue_hash_entry(tqe);

		for (t = 0; t < end; t++)
			for (u = 0; u < end; u++) {
				e->ce.count[t][u] += tqe->ce.count[t][u];
				q->count[t][u] -= tqe->ce.count[t][u];
		}

		memset(&tqe->ce.count, 0, sizeof(tqe->ce.count));
		queue_move_tail(&q->free, &tqe->ce.list);
		q->size--;
	}
}

static unsigned sum_count(struct basic_policy *basic, struct common_entry *ce, enum count_type t)
{
	return (ce->count[t][0] + ce->count[t][1]) >> (t == T_HITS ? 0 : basic->block_shift);
}

/*----------------------------------------------------------------------------*/

/* queue_add_.*() functions. */
static void __queue_add_default(struct basic_policy *basic, struct list_head *elt,
				bool to_head)
{
	struct list_head *q = &basic->queues.used;
	struct basic_cache_entry *e = list_entry(elt, struct basic_cache_entry, ce.list);

	to_head ? queue_add(q, elt) : queue_add_tail(q, elt);
	queue_add_tail(&basic->queues.walk, &e->walk);
}

static void queue_add_default(struct basic_policy *basic, struct list_head *elt)
{
	__queue_add_default(basic, elt, true);
}

static void queue_add_default_tail(struct basic_policy *basic, struct list_head *elt)
{
	__queue_add_default(basic, elt, false);
}

static void queue_add_filo_mru(struct basic_policy *basic, struct list_head *elt)
{
	queue_add_default(basic, elt);
}

static u32 __make_key(u32 k, bool is_lfu)
{
	/*
	 * Invert key in case of lfu to allow btree_last() to
	 * retrieve the minimum used list.
	 */
	return is_lfu ? ~k : k;
}

static void __queue_add_lfu_mfu(struct basic_policy *basic, struct list_head *elt,
				bool is_lfu, enum count_type ctype)
{
	struct list_head *head;
	struct basic_cache_entry *e = list_entry(elt, struct basic_cache_entry, ce.list);
	u32 key = __make_key(sum_count(basic, &e->ce, ctype), is_lfu);

	/*
	 * Memorize key for deletion (e->ce.count[T_HITS]/e->ce.count[T_SECTORS]
	 * will have changed before)
	 */
	e->saved = key;

	/*
	 * Key is e->ce.count[T_HITS]/e->ce.count[T_SECTORS] for mfu or
	 * ~e->ce.count[T_HITS]/~e->ce.count[T_SECTORS] for lfu in order to
	 * allow for btree_last() to be able to retrieve the appropriate node.
	 *
	 * A list of cblocks sharing the same hit/sector count is hanging off that node.
	 *
	 * FIXME: replace with priority heap.
	 */
	head = btree_lookup32(&basic->queues.fu_head, key);
	if (head) {
		/* Always add to the end where we'll pop cblocks off */
		queue_add_tail(head, elt);

		if (is_lfu) {
			/*
			 * For lfu, point to added new head, so that
			 * the older entry will get popped first.
			 */
			int r = btree_update32(&basic->queues.fu_head, key, (void *) elt);

			BUG_ON(r);
		}

	} else {
		/* New key, insert into tree. */
		int r = btree_insert32(&basic->queues.fu_head, key, (void *) elt, GFP_KERNEL);

		BUG_ON(r);
		queue_init(elt);
	}

	queue_add_tail(&basic->queues.walk, &e->walk);
}

static void queue_add_lfu(struct basic_policy *basic, struct list_head *elt)
{
	__queue_add_lfu_mfu(basic, elt, true, T_HITS);
}

static void queue_add_mfu(struct basic_policy *basic, struct list_head *elt)
{
	__queue_add_lfu_mfu(basic, elt, false, T_HITS);
}

static void queue_add_lfu_ws(struct basic_policy *basic, struct list_head *elt)
{
	__queue_add_lfu_mfu(basic, elt, true, T_SECTORS);
}

static void queue_add_mfu_ws(struct basic_policy *basic, struct list_head *elt)
{
	__queue_add_lfu_mfu(basic, elt, false, T_SECTORS);
}

static unsigned __select_multiqueue(struct basic_policy *basic, struct basic_cache_entry *e,
				    enum count_type ctype)
{
	return min((unsigned) ilog2(sum_count(basic, &e->ce, ctype)), basic->queues.nr_mqueues - 1U);
}

static unsigned __get_twoqueue(struct basic_policy *basic, struct basic_cache_entry *e)
{
	return sum_count(basic, &e->ce, T_HITS) > 1 ? 1 : 0;
}

static unsigned long __queue_tmo_multiqueue(struct basic_policy *basic)
{
	return basic->jiffies + basic->queues.mq_tmo;
}

static void demote_multiqueues(struct basic_policy *basic)
{
	struct basic_cache_entry *e;
	struct list_head *cur = basic->queues.mq, *end;

	if (!queue_empty(cur))
		return;

	/*
	 * Start with 2nd queue, because we conditionally move
	 * from queue to queue - 1
	 */
	end = cur + basic->queues.nr_mqueues;
	while (++cur < end) {
		while (!queue_empty(cur)) {
			/* Reference head element. */
			e = list_first_entry(cur, struct basic_cache_entry, ce.list);

			/*
			 * If expired, move entry from head of higher prio
			 * queue to tail of lower prio one.
			 */
			if (time_after_eq(basic->jiffies, e->expire)) {
				queue_move_tail(cur - 1, &e->ce.list);
				e->expire = __queue_tmo_multiqueue(basic);

			} else
				break;
		}
	}
}

static void __queue_add_multiqueue(struct basic_policy *basic, struct list_head *elt,
				   enum count_type ctype)
{
	struct basic_cache_entry *e = list_entry(elt, struct basic_cache_entry, ce.list);
	unsigned queue = __select_multiqueue(basic, e, ctype);

	e->expire = __queue_tmo_multiqueue(basic);
	queue_add_tail(&basic->queues.mq[queue], &e->ce.list);
	queue_add_tail(&basic->queues.walk, &e->walk);
}

static void queue_add_multiqueue(struct basic_policy *basic, struct list_head *elt)
{
	__queue_add_multiqueue(basic, elt, T_HITS);
}

static void queue_add_multiqueue_ws(struct basic_policy *basic, struct list_head *elt)
{
	__queue_add_multiqueue(basic, elt, T_SECTORS);
}

static void queue_add_q2(struct basic_policy *basic, struct list_head *elt)
{
	struct basic_cache_entry *e = list_entry(elt, struct basic_cache_entry, ce.list);

	queue_add_tail(&basic->queues.mq[0], &e->ce.list);
	queue_add_tail(&basic->queues.walk, &e->walk);
}

static void queue_add_twoqueue(struct basic_policy *basic, struct list_head *elt)
{
	unsigned queue;
	struct basic_cache_entry *e = list_entry(elt, struct basic_cache_entry, ce.list);

	queue = e->saved = __get_twoqueue(basic, e);
	if (!queue)
		basic->queues.twoqueue_q0_size++;

	queue_add_tail(&basic->queues.mq[queue], &e->ce.list);
	queue_add_tail(&basic->queues.walk, &e->walk);
}

static void queue_add_dumb(struct basic_policy *basic, struct list_head *elt)
{
	queue_add_default_tail(basic, elt);
}

static void queue_add_noop(struct basic_policy *basic, struct list_head *elt)
{
	queue_add_default_tail(basic, elt); /* Never called. */
}
/*----------------------------------------------------------------------------*/

/* queue_del_.*() functions. */
static void queue_del_default(struct basic_policy *basic, struct list_head *elt)
{
	struct basic_cache_entry *e = list_entry(elt, struct basic_cache_entry, ce.list);

	queue_del(&e->ce.list);
	queue_del(&e->walk);
}

static void queue_del_fifo_filo(struct basic_policy *basic, struct list_head *elt)
{
	queue_del_default(basic, elt);
}

static void __queue_del_lfu_mfu(struct basic_policy *basic, struct list_head *elt)
{
	struct list_head *head;
	struct basic_cache_entry *e = list_entry(elt, struct basic_cache_entry, ce.list);
	/* Retrieve saved key which has been saved by queue_add_lfu_mfu(). */
	u32 key = e->saved;

	head = btree_lookup32(&basic->queues.fu_head, key);
	BUG_ON(!head);
	if (head == elt) {
		/* Need to remove head, because it's the only element. */
		if (queue_empty(head)) {
			struct list_head *h = btree_remove32(&basic->queues.fu_head, key);

			BUG_ON(!h);

		} else {
			int r;

			/* Update node to point to next entry as new head. */
			head = head->next;
			queue_del(elt);
			r = btree_update32(&basic->queues.fu_head, key, (void *) head);
			BUG_ON(r);
		}

	} else
		/* If not head, we can simply remove the element from the list. */
		queue_del(elt);

	queue_del(&e->walk);
}

static void queue_del_lfu(struct basic_policy *basic, struct list_head *elt)
{
	return __queue_del_lfu_mfu(basic, elt);
}

static void queue_del_mfu(struct basic_policy *basic, struct list_head *elt)
{
	return __queue_del_lfu_mfu(basic, elt);
}

static void queue_del_multiqueue(struct basic_policy *basic, struct list_head *elt)
{
	struct basic_cache_entry *e = list_entry(elt, struct basic_cache_entry, ce.list);

	if (IS_TWOQUEUE(basic)) {
		unsigned queue = e->saved;

		if (!queue)
			basic->queues.twoqueue_q0_size--;
	}

	queue_del(&e->ce.list);
	queue_del(&e->walk);
}
/*----------------------------------------------------------------------------*/

/* queue_evict_.*() functions. */
static struct list_head *queue_evict_default(struct basic_policy *basic)
{
	struct list_head *r = queue_pop(&basic->queues.used);
	struct basic_cache_entry *e = list_entry(r, struct basic_cache_entry, ce.list);

	queue_del(&e->walk);

	return r;
}

static struct list_head *queue_evict_lfu_mfu(struct basic_policy *basic)
{
	u32 k;
	struct list_head *r;
	struct basic_cache_entry *e;

	/* This'll retrieve lfu/mfu entry because of __make_key(). */
	r = btree_last32(&basic->queues.fu_head, &k);
	BUG_ON(!r);

	if (queue_empty(r))
		r = btree_remove32(&basic->queues.fu_head, k);

	else {
		/* Retrieve last element in order to minimize btree updates. */
		r = r->prev;
		BUG_ON(!r);
		queue_del(r);
	}

	e = list_entry(r, struct basic_cache_entry, ce.list);
	e->saved = 0;
	queue_del(&e->walk);

	return r;
}

static struct list_head *queue_evict_random(struct basic_policy *basic)
{
	struct list_head *r = basic->queues.used.next;
	struct basic_cache_entry *e;
	dm_block_t off = prandom_u32();

	BUG_ON(!r);

	/* FIXME: cblock_t is 32 bit for the time being. */
	/* Be prepared for large caches ;-) */
	if (from_cblock(basic->cache_size) >= UINT_MAX)
		off |= ((dm_block_t) prandom_u32() << 32);

	/* FIXME: overhead walking list. */
	off = do_div(off, from_cblock(basic->cache_size));
	while (off--)
		r = r->next;

	e = list_entry(r, struct basic_cache_entry, ce.list);
	queue_del(r);
	queue_del(&e->walk);

	return r;
}

static struct list_head *queue_evict_multiqueue(struct basic_policy *basic)
{
	struct list_head *cur = basic->queues.mq - 1, /* -1 because of ++cur below. */
			 *end = basic->queues.mq + basic->queues.nr_mqueues;

	while (++cur < end) {
		if (!queue_empty(cur)) {
			struct basic_cache_entry *e;
			struct list_head *r;

			if (IS_TWOQUEUE(basic) && cur == basic->queues.mq)
				basic->queues.twoqueue_q0_size--;

			r = queue_pop(cur);
			e = list_entry(r, struct basic_cache_entry, ce.list);
			queue_del(&e->walk);

			return r;
		}

		if (IS_MULTIQUEUE(basic))
			break;
	}

	return NULL;
}

static struct list_head *queue_evict_q2_twoqueue(struct basic_policy *basic)
{
	return queue_evict_multiqueue(basic);
}

/*----------------------------------------------------------------------------*/

/*
 * This doesn't allocate the block.
 */
static int __find_free_cblock(struct basic_policy *basic, unsigned begin, unsigned end,
			      dm_cblock_t *result, unsigned *last_word)
{
	int r = -ENOSPC;
	unsigned w;

	for (w = begin; w < end; w++) {
		/*
		 * ffz is undefined if no zero exists
		 */
		if (basic->allocation_bitset[w] != ULONG_MAX) {
			*last_word = w;
			*result = to_cblock((w * BITS_PER_LONG) + ffz(basic->allocation_bitset[w]));
			if (from_cblock(*result) < from_cblock(basic->cache_size))
				r = 0;

			break;
		}
	}

	return r;
}

static int find_free_cblock(struct basic_policy *basic, dm_cblock_t *result)
{
	int r = __find_free_cblock(basic, basic->find_free_last_word, basic->find_free_nr_words, result, &basic->find_free_last_word);

	if (r == -ENOSPC && basic->find_free_last_word)
		r = __find_free_cblock(basic, 0, basic->find_free_last_word, result, &basic->find_free_last_word);

	return r;
}

static void alloc_cblock_insert_cache_and_count_entry(struct basic_policy *basic, struct basic_cache_entry *e)
{
	unsigned t, u, end = ARRAY_SIZE(e->ce.count[T_HITS]);

	alloc_cblock(basic, e->cblock);
	// e->ce.tick = basic->tick;
	insert_cache_hash_entry(basic, e);

	if (IS_DUMB(basic) || IS_NOOP(basic))
		return;

	for (t = 0; t < end; t++)
		for (u = 0; u < end; u++)
			basic->cache_count[t][u] += e->ce.count[t][u];
}

static void add_cache_entry(struct basic_policy *basic, struct basic_cache_entry *e)
{
	basic->queues.fns->add(basic, &e->ce.list);
	alloc_cblock_insert_cache_and_count_entry(basic, e);
}


static void remove_cache_entry(struct basic_policy *basic, struct basic_cache_entry *e)
{
	unsigned t, u, end = ARRAY_SIZE(e->ce.count[T_HITS]);

	remove_cache_hash_entry(basic, e);
	free_cblock(basic, e->cblock);

	if (IS_DUMB(basic) || IS_NOOP(basic))
		return;

	for (t = 0; t < end; t++)
		for (u = 0; u < end; u++)
			basic->cache_count[t][u] -= e->ce.count[t][u];
}

static struct basic_cache_entry *evict_cache_entry(struct basic_policy *basic)
{
	struct basic_cache_entry *r;
	struct list_head *elt = basic->queues.fns->evict(basic);

	if (elt) {
		r = list_entry(elt, struct basic_cache_entry, ce.list);
		remove_cache_entry(basic, r);
	} else
		r = NULL;

	return r;
}

static void update_cache_entry(struct basic_policy *basic, struct basic_cache_entry *e,
			       struct bio *bio, struct policy_result *result)
{
	int rw;

	result->op = POLICY_HIT;
	result->cblock = e->cblock;

	if (updated_this_tick(basic, &e->ce))
		return;

	if (IS_DUMB(basic) || IS_NOOP(basic))
		return;

	rw = to_rw(bio);

/* FIXME: TESTME: */
#if SINGLE_COUNT
rw = 0;
#endif

	e->ce.tick = basic->tick;

	e->ce.count[T_HITS][rw]++;
	e->ce.count[T_SECTORS][rw] += bio_sectors(bio);

	/*
	 * No queue deletion and reinsertion needed with fifo/filo; ie.
	 * avoid queue reordering for those.
	 */
	if (!IS_FIFO_FILO(basic)) {
		basic->queues.fns->del(basic, &e->ce.list);
		basic->queues.fns->add(basic, &e->ce.list);
	}
}

static void get_cache_block(struct basic_policy *basic, dm_oblock_t oblock, struct bio *bio,
			    struct policy_result *result)
{
	int rw = to_rw(bio);
	struct basic_cache_entry *e;

/* FIXME: TESTME: */
#if SINGLE_COUNT
rw = 0;
#endif

	if (queue_empty(&basic->queues.free)) {
		if (IS_MULTIQUEUE(basic))
			demote_multiqueues(basic);

		e = evict_cache_entry(basic);
		if (!e)
			return;

		/* Memorize hits and sectors of just evicted entry on out queue. */
		if (!IS_DUMB(basic)) {
			/* Reads. */
			update_track_queue(basic, &basic->queues.post, e->ce.oblock, 0,
					   e->ce.count[T_HITS][0],
					   e->ce.count[T_SECTORS][0]);
			/* Writes. */
			update_track_queue(basic, &basic->queues.post, e->ce.oblock, 1,
					   e->ce.count[T_HITS][1],
					   e->ce.count[T_SECTORS][1]);
		}

		result->old_oblock = e->ce.oblock;
		result->op = POLICY_REPLACE;

	} else {
		int r;

		e = alloc_cache_entry(basic);
		BUG_ON(!e);
		r = find_free_cblock(basic, &e->cblock);
		BUG_ON(r);

		result->op = POLICY_NEW;
	}

	/*
	 * If an entry for oblock exists on track queues ->
	 * retrieve hit counts and sectors from track queues and delete
	 * the respective tracking entries.
	 */
	if (!IS_DUMB(basic)) {
		memset(&e->ce.count, 0, sizeof(e->ce.count));
		e->ce.count[T_HITS][rw] = 1;
		e->ce.count[T_SECTORS][rw] = bio_sectors(bio);
		get_any_counts_from_track_queue(&basic->queues.pre, e, oblock);
		get_any_counts_from_track_queue(&basic->queues.post, e, oblock);
	}

	result->cblock = e->cblock;
	e->ce.oblock = oblock;
	add_cache_entry(basic, e);
}

static bool in_cache(struct basic_policy *basic, dm_oblock_t oblock, struct bio *bio, struct policy_result *result)
{
	struct basic_cache_entry *e = lookup_cache_entry(basic, oblock);

	if (e) {
		/* Cache hit: update entry on queues, increment its hit count */
		update_cache_entry(basic, e, bio, result);
		return true;
	}

	return false;
}

static bool should_promote(struct basic_policy *basic, struct track_queue_entry *tqe,
			   dm_oblock_t oblock, int rw, bool discarded_oblock,
			   struct policy_result *result)
{
	calculate_rw_threshold(basic);

	if (discarded_oblock && any_free_cblocks(basic)) {
		/*
		 * We don't need to do any copying at all, so give this a
		 * very low threshold.  In practice this only triggers
		 * during initial population after a format.
		 */
		return true;
	}

/* FIXME: TESTME: */
#if SINGLE_COUNT
rw = 0;
#endif

	BUG_ON(!tqe);
	return tqe->ce.count[basic->queues.ctype][rw] >= basic->promote_threshold[rw];
}

static void map_prerequisites(struct basic_policy *basic, struct bio *bio)
{
	/* Update io tracker. */
	iot_update_stats(&basic->tracker, bio);
	iot_check_for_pattern_switch(&basic->tracker, basic->block_size);

	/* Get start jiffies needed for time based queue demotion. */
	if (IS_MULTIQUEUE(basic))
		basic->jiffies = get_jiffies_64();
}

static int map(struct basic_policy *basic, dm_oblock_t oblock,
	       bool can_block, bool can_migrate, bool discarded_oblock,
	       struct bio *bio, struct policy_result *result)
{
	int rw = to_rw(bio);
	struct track_queue_entry *tqe = NULL;

	if (IS_NOOP(basic))
		return 0;

	if (in_cache(basic, oblock, bio, result))
		return 0;

	if (!can_migrate)
		return -EWOULDBLOCK;

	if (!IS_DUMB(basic)) {
		if (iot_sequential_pattern(&basic->tracker))
			return -EWOULDBLOCK;

		/* Record hits on pre cache track queue. */
		tqe = update_track_queue(basic, &basic->queues.pre, oblock, rw, 1, bio_sectors(bio));
	}

	if (IS_DUMB(basic) || should_promote(basic, tqe, oblock, rw, discarded_oblock, result))
		get_cache_block(basic, oblock, bio, result);

	return 0;
}

/* Public interface (see dm-cache-policy.h */
static int basic_map(struct dm_cache_policy *p, dm_oblock_t oblock,
		     bool can_block, bool can_migrate, bool discarded_oblock,
		     struct bio *bio, struct policy_result *result)
{
	int r;
	struct basic_policy *basic = to_basic_policy(p);

	result->op = POLICY_MISS;

	if (can_block)
		mutex_lock(&basic->lock);

	else if (!mutex_trylock(&basic->lock))
		return -EWOULDBLOCK;

	smp_rmb();
	basic->tick = basic->tick_extern;

	if (!IS_DUMB(basic) && !IS_NOOP(basic))
		map_prerequisites(basic, bio);

	r = map(basic, oblock, can_block, can_migrate, discarded_oblock, bio, result);

	mutex_unlock(&basic->lock);

	return r;
}

static int basic_lookup(struct dm_cache_policy *p, dm_oblock_t oblock, dm_cblock_t *cblock)
{
	int r;
	struct basic_policy *basic = to_basic_policy(p);
	struct basic_cache_entry *e;

	if (!mutex_trylock(&basic->lock))
		return -EWOULDBLOCK;

	e = lookup_cache_entry(basic, oblock);
	if (e) {
		*cblock = e->cblock;
		r = 0;

	} else
		r = -ENOENT;

	mutex_unlock(&basic->lock);

	return r;
}

static void basic_destroy(struct dm_cache_policy *p)
{
	struct basic_policy *basic = to_basic_policy(p);

	if (IS_LFU_MFU_WS(basic))
		btree_destroy32(&basic->queues.fu_head);

	else if (IS_MULTIQUEUE_Q2_TWOQUEUE(basic))
		free_multiqueues(basic);

	free_track_queue(&basic->queues.post);
	free_track_queue(&basic->queues.pre);
	free_bitset(basic->allocation_bitset);
	free_cache_blocks_and_hash(basic);
	kfree(basic);
}

static void sort_in_cache_entry(struct basic_policy *basic, struct basic_cache_entry *e,
				bool hint_valid)
{
	struct list_head *elt;
	struct basic_cache_entry *cur;

	list_for_each(elt, &basic->queues.used) {
		if (!hint_valid)
			break;

		cur = list_entry(elt, struct basic_cache_entry, ce.list);
		if (e->ce.count[T_HITS][0] > cur->ce.count[T_HITS][0])
			break;
	}

	if (elt == &basic->queues.used)
		queue_add_tail(elt, &e->ce.list);
	else
		queue_add(elt, &e->ce.list);

	queue_add_tail(&basic->queues.walk, &e->walk);
}

static void add_dirty_entry(struct basic_policy *basic, struct basic_cache_entry *e)
{
	if (IS_FILO_MRU(basic) || IS_MFU(basic))
		queue_add(&basic->queues.dirty, &e->dirty);
	else
		queue_add_tail(&basic->queues.dirty, &e->dirty);
}

static int __set_clear_dirty(struct dm_cache_policy *p, dm_oblock_t oblock, bool set)
{
	int r;
	struct basic_policy *basic = to_basic_policy(p);
	struct basic_cache_entry *e;
	const char *caller = set ? "set" : "clear";

	mutex_lock(&basic->lock);

	e = lookup_cache_entry(basic, oblock);
	if (!e) {
		DMWARN("basic_%s_dirty called for a block that isn't in the cache", caller);
		r = -ENOENT;

	} else {
		bool dirty = !queue_empty(&e->dirty);

		queue_del(&e->dirty);

		if (set) {
			add_dirty_entry(basic, e);
			r = dirty ? -EINVAL : 0;

		} else
			r = dirty ? 0 : - EINVAL;

	}

	mutex_unlock(&basic->lock);

	return r;
}

static int basic_set_dirty(struct dm_cache_policy *p, dm_oblock_t oblock)
{
	return __set_clear_dirty(p, oblock, true);
}

static int basic_clear_dirty(struct dm_cache_policy *p, dm_oblock_t oblock)
{
	return __set_clear_dirty(p, oblock, false);
}

static int basic_load_mapping(struct dm_cache_policy *p,
			      dm_oblock_t oblock, dm_cblock_t cblock,
			      void *hint, bool hint_valid)
{
	struct basic_policy *basic = to_basic_policy(p);
	struct basic_cache_entry *e;

	e = alloc_cache_entry(basic);
	if (!e)
		return -ENOMEM;

	e->cblock = cblock;
	e->ce.oblock = oblock;

	if (hint_valid) {
		__le32 *hints = hint;
		unsigned hint_size = dm_cache_policy_get_hint_size(p);

		e->ce.count[T_HITS][0] = le32_to_cpu(hints[0]);

		if (hint_size >= 8)
			e->ce.count[T_HITS][1] = le32_to_cpu(hints[1]);

		if (hint_size == 16) {
			e->ce.count[T_SECTORS][0] = le32_to_cpu(hints[2]);
			e->ce.count[T_SECTORS][1] = le32_to_cpu(hints[3]);
		}
	}

	if (IS_MULTIQUEUE(basic) || IS_TWOQUEUE(basic) || IS_LFU_MFU_WS(basic))
		add_cache_entry(basic, e);

	else {
		sort_in_cache_entry(basic, e, hint_valid);
		alloc_cblock_insert_cache_and_count_entry(basic, e);
	}

	return 0;
}

/* Walk mappings */
static int basic_walk_mappings(struct dm_cache_policy *p, policy_walk_fn fn,
			       void *context)
{
	int r = 0;
	unsigned nr = 0;
	struct basic_policy *basic = to_basic_policy(p);
	struct basic_cache_entry *e;

	mutex_lock(&basic->lock);

	list_for_each_entry(e, &basic->queues.walk, walk) {
		__le32 hints[4];
		unsigned hint_size = dm_cache_policy_get_hint_size(p);

		if (hint_size == 4) {
			unsigned tmp = nr++;

			if (IS_FILO_MRU(basic))
				tmp = from_cblock(basic->cache_size) - tmp - 1;

			hints[0] = cpu_to_le32(tmp);

		} else {
			hints[0] = cpu_to_le32(e->ce.count[T_HITS][0]);
			hints[1] = cpu_to_le32(e->ce.count[T_HITS][1]);

			if (hint_size == 16) {
				hints[2] = cpu_to_le32(e->ce.count[T_SECTORS][0]);
				hints[3] = cpu_to_le32(e->ce.count[T_SECTORS][1]);
			}
		}

		r = fn(context, e->cblock, e->ce.oblock, &hints);
		if (r)
			break;
	}

	mutex_unlock(&basic->lock);
	return r;
}

static struct basic_cache_entry *__basic_remove_invalidate_mapping(struct basic_policy *basic,
								   dm_oblock_t oblock)
{
	struct basic_cache_entry *r = lookup_cache_entry(basic, oblock);

	if (r) {
		basic->queues.fns->del(basic, &r->ce.list);
		remove_cache_entry(basic, r);
	}

	return r;
}

static void add_to_free_list(struct basic_policy *basic, struct basic_cache_entry *e)
{
	queue_del(&e->dirty);
	memset(&e->ce.count, 0, sizeof(e->ce.count));
	queue_add_tail(&basic->queues.free, &e->ce.list);
	BUG_ON(!from_cblock(basic->nr_cblocks_allocated));
	basic->nr_cblocks_allocated = to_cblock(from_cblock(basic->nr_cblocks_allocated) - 1);
}

static void basic_remove_mapping(struct dm_cache_policy *p, dm_oblock_t oblock)
{
	struct basic_policy *basic = to_basic_policy(p);
	struct basic_cache_entry *e;

	mutex_lock(&basic->lock);
	e = __basic_remove_invalidate_mapping(basic, oblock);
	BUG_ON(!e);
	add_to_free_list(basic, e);
	mutex_unlock(&basic->lock);
}

static void basic_force_mapping(struct dm_cache_policy *p,
				dm_oblock_t current_oblock, dm_oblock_t new_oblock)
{
	struct basic_policy *basic = to_basic_policy(p);
	struct basic_cache_entry *e;

	mutex_lock(&basic->lock);
	e = lookup_cache_entry(basic, current_oblock);
	if (e) {
		basic->queues.fns->del(basic, &e->ce.list);
		e->ce.oblock = new_oblock;
		queue_del(&e->dirty);
		add_dirty_entry(basic, e);
		basic->queues.fns->add(basic, &e->ce.list);
	}

	mutex_unlock(&basic->lock);
}

static int basic_invalidate_mapping(struct dm_cache_policy *p, dm_oblock_t *oblock, dm_cblock_t *cblock)
{
	int r;
	struct basic_policy *basic = to_basic_policy(p);
	struct basic_cache_entry *e;

	mutex_lock(&basic->lock);
	e = __basic_remove_invalidate_mapping(basic, *oblock);
	if (e) {
		*cblock = e->cblock;
		queue_del(&e->dirty);
		add_to_free_list(basic, e);
		r = 0;

	} else
		r = -ENOENT;

	mutex_unlock(&basic->lock);

	return r;
}

static int basic_writeback_work(struct dm_cache_policy *p, dm_oblock_t *oblock, dm_cblock_t *cblock)
{
	int r;
	struct basic_policy *basic = to_basic_policy(p);
	struct basic_cache_entry *e;
	struct list_head *dirty = &basic->queues.dirty;

	mutex_lock(&basic->lock);

	/* FIXME: best effort with a dirty list. policy specific functions for optimization. */
	if (!queue_empty(dirty)) {
		e = list_entry(queue_pop(dirty), struct basic_cache_entry, dirty);
		queue_init(&e->dirty);
		*cblock = e->cblock;
		*oblock = e->ce.oblock;
		r = 0;

	} else
		r = -ENODATA;

	mutex_unlock(&basic->lock);

	return r;
}

static dm_cblock_t basic_residency(struct dm_cache_policy *p)
{
	/* FIXME: lock mutex, not sure we can block here. */
	return to_basic_policy(p)->nr_cblocks_allocated;
}

static void basic_tick(struct dm_cache_policy *p)
{
	struct basic_policy *basic = to_basic_policy(p);

	basic->tick_extern++;
	smp_wmb();
}

static int basic_set_config_value(struct dm_cache_policy *p,
				  const char *key, const char *value)
{
	struct basic_policy *basic = to_basic_policy(p);
	unsigned long tmp;

	if (kstrtoul(value, 10, &tmp))
		return -EINVAL;

	if (!strcasecmp(key, "hits")) {
		if (tmp > 1)
			return -EINVAL;

		basic->queues.ctype = tmp ? T_HITS : T_SECTORS;

	} else if (!strcasecmp(key, "multiqueue_timeout")) {
		if (tmp < 1 || tmp > 24*3600*1000) /* 1 day max :) */
			return -EINVAL;

		if (IS_MULTIQUEUE(basic)) {
			/* In milliseconds. */
			unsigned long ticks = tmp * HZ / 1000;

			/* Ensure one tick timeout minimum. */
			basic->queues.mq_tmo = ticks ? ticks : 1;

		}

	} else if (!strcasecmp(key, "random_threshold"))
		basic->tracker.thresholds[PATTERN_RANDOM] = tmp;
	else if (!strcasecmp(key, "sequential_threshold"))
		basic->tracker.thresholds[PATTERN_SEQUENTIAL] = tmp;
	else
		return -EINVAL;

	return 0;
}

static int basic_emit_config_values(struct dm_cache_policy *p, char *result, unsigned maxlen)
{
	ssize_t sz = 0;
	struct basic_policy *basic = to_basic_policy(p);

	DMEMIT("8 hits %u multiqueue_timeout %lu random_threshold %lu sequential_threshold %lu",
	       basic->queues.ctype,
	       basic->queues.mq_tmo,
	       basic->tracker.thresholds[PATTERN_RANDOM],
	       basic->tracker.thresholds[PATTERN_SEQUENTIAL]);

	return 0;
}

/* Init the policy plugin interface function pointers. */
static void init_policy_functions(struct basic_policy *basic)
{
	basic->policy.destroy = basic_destroy;
	basic->policy.map = basic_map;
	basic->policy.lookup = basic_lookup;
	basic->policy.set_dirty = basic_set_dirty;
	basic->policy.clear_dirty = basic_clear_dirty;
	basic->policy.load_mapping = basic_load_mapping;
	basic->policy.walk_mappings = basic_walk_mappings;
	basic->policy.remove_mapping = basic_remove_mapping;
	basic->policy.invalidate_mapping = basic_invalidate_mapping;
	basic->policy.writeback_work = basic_writeback_work;
	basic->policy.force_mapping = basic_force_mapping;
	basic->policy.residency = basic_residency;
	basic->policy.tick = basic_tick;
	basic->policy.emit_config_values = basic_emit_config_values;
	basic->policy.set_config_value = basic_set_config_value;
}

static struct dm_cache_policy *basic_policy_create(dm_cblock_t cache_size,
						   sector_t origin_size,
						   sector_t block_size,
						   enum policy_type type)
{
	int r;
	unsigned mqueues = 0;
	static struct queue_fns queue_fns[] = {
		/* These have to be in 'enum policy_type' order! */
		{ &queue_add_dumb,	    &queue_del_default,		&queue_evict_default },		/* P_dumb */
		{ &queue_add_default_tail,  &queue_del_fifo_filo,	&queue_evict_default },		/* P_fifo */
		{ &queue_add_filo_mru,      &queue_del_fifo_filo,	&queue_evict_default },		/* P_filo */
		{ &queue_add_default_tail,  &queue_del_default,		&queue_evict_default },		/* P_lru */
		{ &queue_add_filo_mru,      &queue_del_default,		&queue_evict_default },		/* P_mru */
		{ &queue_add_lfu,           &queue_del_lfu,		&queue_evict_lfu_mfu },		/* P_lfu */
		{ &queue_add_lfu_ws,        &queue_del_lfu,		&queue_evict_lfu_mfu },		/* P_lfu_ws */
		{ &queue_add_mfu,           &queue_del_mfu,		&queue_evict_lfu_mfu },		/* P_mfu */
		{ &queue_add_mfu_ws,        &queue_del_mfu,		&queue_evict_lfu_mfu },		/* P_mfu_ws */
		{ &queue_add_multiqueue,    &queue_del_multiqueue,	&queue_evict_multiqueue },	/* P_multiqueue */
		{ &queue_add_multiqueue_ws, &queue_del_multiqueue,	&queue_evict_multiqueue },	/* P_multiqueue_ws */
		{ &queue_add_noop,	    NULL,			NULL },				/* P_noop */
		{ &queue_add_default_tail,  &queue_del_default,		&queue_evict_random },		/* P_random */
		{ &queue_add_q2,            &queue_del_multiqueue,	&queue_evict_q2_twoqueue },	/* P_q2 */
		{ &queue_add_twoqueue,      &queue_del_multiqueue,	&queue_evict_q2_twoqueue },	/* P_twoqueue */
	};
	struct basic_policy *basic = kzalloc(sizeof(*basic), GFP_KERNEL);

	if (!basic)
		return NULL;

	/* Set default (aka basic) policy (doesn't need a queue_fns entry above). */
	if (type == p_basic)
		type = p_multiqueue_ws;

	/* Distinguish policies */
	basic->queues.fns = queue_fns + type;

	init_policy_functions(basic);
	iot_init(&basic->tracker);

	basic->cache_size = cache_size;
	basic->find_free_nr_words = bit_set_nr_words(from_cblock(cache_size));
	basic->find_free_last_word = 0;
	basic->block_size = block_size;
	basic->block_shift = ffs(block_size);
	basic->origin_size = origin_size;
	basic->queues.ctype = T_HITS;
	basic->promote_threshold[0] = ctype_threshold(basic, READ_PROMOTE_THRESHOLD);
	basic->promote_threshold[1] = ctype_threshold(basic, WRITE_PROMOTE_THRESHOLD);
	mutex_init(&basic->lock);
	queue_init(&basic->queues.free);
	queue_init(&basic->queues.used);
	queue_init(&basic->queues.walk);
	queue_init(&basic->queues.dirty);
	queue_init(&basic->queues.pre.free);
	queue_init(&basic->queues.pre.used);
	queue_init(&basic->queues.post.free);
	queue_init(&basic->queues.post.used);

	basic->tick_extern = 0;
	basic->tick = 0;

	if (IS_NOOP(basic))
		goto out;

	/* Allocate cache entry structs and add them to free list. */
	r = alloc_cache_blocks_with_hash(basic, from_cblock(cache_size));
	if (r)
		goto bad_free_policy;

	/* Cache allocation bitset. */
	basic->allocation_bitset = alloc_bitset(from_cblock(cache_size));
	if (!basic->allocation_bitset)
		goto bad_free_cache_blocks_and_hash;

	if (IS_DUMB(basic))
		goto out;

	/*
	 * Create in queue to track entries waiting for the
	 * cache in order to stear their promotion.
	 */
	r = alloc_track_queue_with_hash(&basic->queues.pre, max(from_cblock(cache_size), 128U));
	if (r)
		goto bad_free_allocation_bitset;

	/* Create cache_size queue to track evicted cache entries. */
	r = alloc_track_queue_with_hash(&basic->queues.post, max(from_cblock(cache_size) >> 1, 128U));
	if (r)
		goto bad_free_track_queue_pre;

	if (IS_LFU_MFU_WS(basic)) {
		/* FIXME: replace with priority heap. */
		basic->queues.fu_pool = mempool_create(from_cblock(cache_size), btree_alloc, btree_free, NULL);
		if (!basic->queues.fu_pool)
			goto bad_free_track_queue_post;

		btree_init_mempool32(&basic->queues.fu_head, basic->queues.fu_pool);

	} else if (IS_Q2(basic))
		mqueues = 1; /* Not really multiple queues but code can be shared */

	else if (IS_TWOQUEUE(basic)) {
		/*
		 * Just 2 prio queues.
		 *
		 * Only allow 25% of the total cache size maximum in queue 0 (hit count 1).
		 * Ie. 75% minimum is reserved for cblocks with multiple hits.
		 */
		mqueues = 2;
		basic->queues.twoqueue_q0_max_elts =
			min(max(from_cblock(cache_size) >> 2, 16U), from_cblock(cache_size));

	} else if (IS_MULTIQUEUE(basic)) {
		/* Multiple queues. */
		mqueues = min(max((unsigned) ilog2(block_size << 13), 8U), (unsigned) from_cblock(cache_size));
		basic->jiffies = get_jiffies_64();
		basic->queues.mq_tmo = MQ_QUEUE_TMO_DEFAULT;
	}


	if (mqueues) {
		r = alloc_multiqueues(basic, mqueues);
		if (r)
			goto bad_free_track_queue_post;

	}

out:
	return &basic->policy;

bad_free_track_queue_post:
	free_track_queue(&basic->queues.post);
bad_free_track_queue_pre:
	free_track_queue(&basic->queues.pre);
bad_free_allocation_bitset:
	free_bitset(basic->allocation_bitset);
bad_free_cache_blocks_and_hash:
	free_cache_blocks_and_hash(basic);
bad_free_policy:
	kfree(basic);

	return NULL;
}
/*----------------------------------------------------------------------------*/

/* Policy type creation magic. */
#define __CREATE_POLICY(policy) \
static struct dm_cache_policy *policy ## _create(dm_cblock_t cache_size, sector_t origin_size, \
						  sector_t block_size) \
{ \
	return basic_policy_create(cache_size, origin_size, block_size, p_ ## policy); \
}

#define	__POLICY_TYPE(policy, hints_size) \
static struct dm_cache_policy_type policy ## _policy_type = { \
	.name = #policy, \
	.hint_size = hints_size, \
	.owner = THIS_MODULE, \
	.create = policy ## _create, \
	.features = 0 \
};

#define	__CREATE_POLICY_TYPE(policy, hint_size) \
	__CREATE_POLICY(policy); \
	__POLICY_TYPE(policy, hint_size);

/*
 * Create all fifo_create,filo_create,lru_create,... functions and
 * declare and initialize all fifo_policy_type,filo_policy_type,... structures.
 */
__CREATE_POLICY_TYPE(basic, 16);
__CREATE_POLICY_TYPE(dumb, 0);
__CREATE_POLICY_TYPE(fifo, 4);
__CREATE_POLICY_TYPE(filo, 4);
__CREATE_POLICY_TYPE(lfu, 8);
__CREATE_POLICY_TYPE(lfu_ws, 16);
__CREATE_POLICY_TYPE(lru, 4);
__CREATE_POLICY_TYPE(mfu, 8);
__CREATE_POLICY_TYPE(mfu_ws, 16);
__CREATE_POLICY_TYPE(mru, 4);
__CREATE_POLICY_TYPE(multiqueue, 8);
__CREATE_POLICY_TYPE(multiqueue_ws, 16);
__CREATE_POLICY_TYPE(noop, 0);
__CREATE_POLICY_TYPE(random, 0);
__CREATE_POLICY_TYPE(q2, 8);
__CREATE_POLICY_TYPE(twoqueue, 8);

static struct dm_cache_policy_type *policy_types[] = {
	&basic_policy_type,
	&dumb_policy_type,
	&fifo_policy_type,
	&filo_policy_type,
	&lfu_policy_type,
	&lfu_ws_policy_type,
	&lru_policy_type,
	&mfu_policy_type,
	&mfu_ws_policy_type,
	&mru_policy_type,
	&multiqueue_policy_type,
	&multiqueue_ws_policy_type,
	&noop_policy_type,
	&random_policy_type,
	&q2_policy_type,
	&twoqueue_policy_type
};

static int __init basic_init(void)
{
	int i = ARRAY_SIZE(policy_types), r;

	basic_entry_cache = kmem_cache_create("dm_cache_basic_policy",
					      sizeof(struct basic_cache_entry),
					      __alignof__(struct basic_cache_entry),
					      0, NULL);
	if (!basic_entry_cache)
		goto bad_basic_entry_cache;

	track_entry_cache = kmem_cache_create("dm_cache_basic_policy_tq",
					      sizeof(struct track_queue_entry),
					      __alignof__(struct track_queue_entry),
					      0, NULL);
	if (!track_entry_cache)
		goto bad_track_entry_cache;

	while (i--) {
		r = dm_cache_policy_register(policy_types[i]);
		if (r)
			goto bad_policy;
	}

	return 0;

bad_policy:
	kmem_cache_destroy(track_entry_cache);
bad_track_entry_cache:
	kmem_cache_destroy(basic_entry_cache);
bad_basic_entry_cache:
	return -ENOMEM;
}

static void __exit basic_exit(void)
{
	int i = ARRAY_SIZE(policy_types);

	while (i--)
		dm_cache_policy_unregister(policy_types[i]);

	kmem_cache_destroy(track_entry_cache);
	kmem_cache_destroy(basic_entry_cache);
}

module_init(basic_init);
module_exit(basic_exit);

MODULE_AUTHOR("Joe Thornber/Heinz Mauelshagen <dm-devel@redhat.com>");
MODULE_LICENSE("GPL");
MODULE_DESCRIPTION("basic cache policies (fifo, lru, etc)");

MODULE_ALIAS("dm-cache-basic"); /* basic_policy_create() maps "basic" to one of the following: */
MODULE_ALIAS("dm-cache-dumb");
MODULE_ALIAS("dm-cache-fifo");
MODULE_ALIAS("dm-cache-filo");
MODULE_ALIAS("dm-cache-lfu");
MODULE_ALIAS("dm-cache-lfu_ws");
MODULE_ALIAS("dm-cache-lru");
MODULE_ALIAS("dm-cache-mfu");
MODULE_ALIAS("dm-cache-mfu_ws");
MODULE_ALIAS("dm-cache-mru");
MODULE_ALIAS("dm-cache-multiqueue");
MODULE_ALIAS("dm-cache-multiqueue_ws");
MODULE_ALIAS("dm-cache-noop");
MODULE_ALIAS("dm-cache-random");
MODULE_ALIAS("dm-cache-q2");
MODULE_ALIAS("dm-cache-twoqueue");
