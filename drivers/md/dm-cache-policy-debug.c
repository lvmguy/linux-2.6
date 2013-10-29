/*
 * Copyright (C) 2012-2013 Red Hat. All rights reserved.
 *
 * Shim "debug" module for cache replacement policies.
 *
 * This file is released under the GPL.
 */

#include "dm-cache-policy.h"
#include "dm-cache-policy-internal.h"
#include "dm-cache-shim-utils.h"
#include "dm.h"

#include <linux/module.h>
#include <linux/slab.h>
#include <linux/hash.h>
#include <linux/vmalloc.h>

#define	DM_MSG_PREFIX	"dm-cache-debug"

#define	LLU	long long unsigned

static struct kmem_cache *debug_block_cache;

/*----------------------------------------------------------------*/

struct hash {
	struct hlist_head *table;
	dm_block_t hash_bits;
	unsigned nr_buckets;
};

struct debug_entry {
	struct hlist_node ohlist, chlist;
	struct list_head list;
	dm_oblock_t oblock;
	dm_cblock_t cblock;
	enum policy_operation op;
};

struct good_state_counts {
	unsigned hit, map_miss, miss, new, replace, op, lookup, dirty, clean, cblock, load, remove, force, writeback, invalidate, residency;
};

struct bad_state_counts {
	unsigned hit, map_miss, miss, new, replace, op, lookup, dirty, clean, cblock, load, remove, force, writeback, invalidate, residency_larger, residency_invalid;
};

struct debug_policy {
	struct dm_cache_policy policy;
	struct mutex lock;

	struct dm_cache_policy *debug_policy;
	struct list_head free, used;
	struct hash ohash, chash;
	dm_oblock_t origin_blocks;
	dm_cblock_t cache_size;
	unsigned nr_dblocks_allocated, analysed, hit;
	struct good_state_counts good;
	struct bad_state_counts bad;
	unsigned verbose;
};

/*----------------------------------------------------------------------------*/
/* Low-level functions. */
static struct debug_policy *to_debug_policy(struct dm_cache_policy *p)
{
	return container_of(p, struct debug_policy, policy);
}

static unsigned next_power(unsigned n, unsigned min)
{
	return roundup_pow_of_two(max(n, min));
}

static bool test_ok(struct debug_policy *debug)
{
	struct bad_state_counts *b = &debug->bad;

	return b->hit + b->miss + b->new + b->replace + b->op + b->lookup + b->dirty + b->clean + b->cblock + b->load + b->remove + b->force + b->writeback + b->invalidate + b->residency_larger + b->residency_invalid > 0 ? false : true;
}

/*----------------------------------------------------------------------------*/

static struct list_head *list_pop(struct list_head *lh)
{
	struct list_head *r = lh->next;

	BUG_ON(!r);
	list_del_init(r);

	return r;
}

/*----------------------------------------------------------------------------*/

/* Hash functions (lookup, insert, remove). */

/* To create lookup_debug_entry_by_cache_block() and lookup_debug_entry_by_origin_block() */
#define LOOKUP(type, longtype) \
static struct debug_entry *lookup_debug_entry_by_ ## longtype ## _block(struct debug_policy *debug, dm_ ## type ## block_t type ## block) \
{ \
	unsigned h = hash_64(from_ ## type ## block(type ## block), debug->type ## hash.hash_bits); \
	struct debug_entry *cur; \
	struct hlist_head *bucket = debug->type ## hash.table + h; \
\
	hlist_for_each_entry(cur, bucket, type ## hlist) { \
		if (cur->type ## block == type ## block) { \
			/* Move upfront bucket for faster access. */ \
			hlist_del(&cur->type ## hlist); \
			hlist_add_head(&cur->type ## hlist, bucket); \
			return cur; \
		} \
	} \
\
	return NULL; \
}

LOOKUP(o, origin);
LOOKUP(c, cache);
#undef LOOKUP

static void insert_origin_hash_entry(struct debug_policy *debug, struct debug_entry *e)
{
	unsigned h = hash_64(from_oblock(e->oblock), debug->ohash.hash_bits);

	hlist_add_head(&e->ohlist, debug->ohash.table + h);
}

static void insert_cache_hash_entry(struct debug_policy *debug, struct debug_entry *e)
{
	if (from_cblock(e->cblock) < from_cblock(debug->cache_size)) {
		unsigned h = hash_64(from_cblock(e->cblock), debug->chash.hash_bits);

		hlist_add_head(&e->chlist, debug->chash.table + h);
	}
}

static void remove_origin_hash_entry(struct debug_policy *debug, struct debug_entry *e)
{
	hlist_del(&e->ohlist);
}

static void remove_cache_hash_entry(struct debug_policy *debug, struct debug_entry *e)
{
	if (from_cblock(e->cblock) < from_cblock(debug->cache_size))
		hlist_del(&e->chlist);
}

/*----------------------------------------------------------------------------*/

/* Allocate/free hashs and debug blocks. */
static int alloc_hash(struct hash *hash, unsigned elts)
{
	hash->nr_buckets = next_power(elts >> 5, 16);
	hash->hash_bits = ffs(hash->nr_buckets) - 1;
	hash->table = vzalloc(sizeof(*hash->table) * hash->nr_buckets);

	return hash->table ? 0 : -ENOMEM;
}

static void free_hash(struct hash *hash)
{
	vfree(hash->table);
}

static void free_dblocks(struct debug_policy *debug)
{
	struct debug_entry *e, *tmp;

	list_splice_init(&debug->used, &debug->free);
	list_for_each_entry_safe(e, tmp, &debug->free, list)
		kmem_cache_free(debug_block_cache, e);
}

static int alloc_debug_blocks_and_hashs(struct debug_policy *debug, dm_oblock_t origin_blocks, dm_cblock_t cache_size)
{
	int r = -ENOMEM;
	dm_block_t u;
	struct debug_entry *e;

	INIT_LIST_HEAD(&debug->free);
	INIT_LIST_HEAD(&debug->used);

	debug->nr_dblocks_allocated = 0;

	/* FIXME: if we'ld avoid POLICY_MISS checks, we wouldn't need that many. */
	u = from_oblock(origin_blocks);
	while (u--) {
		/* FIXME: use slab. */
		e = kmem_cache_alloc(debug_block_cache, GFP_KERNEL);
		if (!e)
			goto bad_kmem_cache_alloc;

		list_add(&e->list, &debug->free);
	}

	/* Cache entries by oblock hash. */
	r = alloc_hash(&debug->ohash, from_oblock(origin_blocks));
	if (r)
		goto bad_alloc_origin_hash;

	/* Cache entries by cblock hash. */
	r = alloc_hash(&debug->chash, from_cblock(cache_size));
	if (!r)
		return 0;

	free_hash(&debug->ohash);
bad_alloc_origin_hash:
bad_kmem_cache_alloc:
	free_dblocks(debug);

	return r;
}

static void free_debug_blocks_and_hashs(struct debug_policy *debug)
{
	free_hash(&debug->chash);
	free_hash(&debug->ohash);
	free_dblocks(debug);
}

static void remove_debug_entry(struct debug_policy *debug, struct debug_entry *e)
{
	BUG_ON(!e);
	remove_origin_hash_entry(debug, e);
	remove_cache_hash_entry(debug, e);
	e->oblock = 0;
	e->cblock = 0;
	e->op = 0;
	BUG_ON(list_empty(&e->list));
	list_move_tail(&e->list, &debug->free);
	debug->nr_dblocks_allocated--;
}

static struct debug_entry *insert_debug_entry(struct debug_policy *debug,
					      dm_oblock_t oblock, dm_cblock_t cblock)
{
	struct debug_entry *e = list_entry(list_pop(&debug->free), struct debug_entry, list);

	e->oblock = oblock;
	e->cblock = cblock;
	e->op = 0;
	insert_origin_hash_entry(debug, e);
	insert_cache_hash_entry(debug, e);
	list_add(&e->list, &debug->used);
	debug->nr_dblocks_allocated++;

	return e;
}
/*----------------------------------------------------------------------------*/

static void check_op(struct debug_policy *debug, char *name, enum policy_operation op)
{
	if (debug->verbose & 0x4) {
		if (op == POLICY_HIT)
			DMWARN("%s: previous op POLICY_HIT invalid!", name);

		else if (op == POLICY_NEW)
			DMWARN("%s: previous op POLICY_NEW invalid!", name);

		else if (op == POLICY_REPLACE)
			DMWARN("%s: previous op POLICY_REPLACE invalid!", name);
	}
}

static void analyse_map_result(struct debug_policy *debug, dm_oblock_t oblock,
			       int map_ret, struct policy_result *result)
{
	bool cblock_ok = true;
	struct debug_entry *ec = from_cblock(result->cblock) < from_cblock(debug->cache_size) ?
		lookup_debug_entry_by_cache_block(debug, result->cblock) : NULL;
	struct debug_entry *eo = lookup_debug_entry_by_origin_block(debug, oblock);
	const char *name = dm_cache_policy_get_name(debug->policy.child);

	debug->good.op++;

	/* target map thread caller may result in this. */
	if (map_ret == -EWOULDBLOCK) {
		if (result->op != POLICY_MISS) {
			if (debug->verbose & 0x2)
				DMWARN("%s->map: -EWOULDBLOCK: op=%u != POLICY_MISS invalid!", name, eo->op);

			debug->bad.map_miss++;

		} else
			debug->good.map_miss++;

		return;
	}

	switch (result->op) {
	case POLICY_HIT:
		/* POLICY_HIT, POLICY_NEW, POLICY_REPLACE -> POLICY_HIT ok. */
		/* POLICY_MISS -> POLICY_HIT FALSE. */
		if (eo) {
			if (from_cblock(eo->cblock) != from_cblock(result->cblock)) {
				if (debug->verbose & 0x2)
					DMWARN("%s->map: POLICY_HIT: e->oblock=%llu e->cblock=%u != result->cblock=%u invalid!",
					       name,
					       from_oblock(eo->oblock),
					       from_cblock(eo->cblock),
					       from_cblock(result->cblock));

				debug->bad.cblock++;

			} else
				debug->good.cblock++;

			if (eo->op == POLICY_MISS) {
				if (debug->verbose & 0x2)
					DMWARN("%s->map: POLICY_HIT: following POLICY_MISS invalid!", name);

				debug->bad.hit++;

			} else
				debug->good.hit++;
		}

		break;

	case POLICY_NEW:
		/* POLICY_MISS -> POLICY_NEW ok */
		/* POLICY_HIT, POLICY_NEW, POLICY_REPLACE -> POLICY_NEW FALSE. */
		if (ec) {
			if (debug->verbose & 0x2)
				DMWARN("%s->map: POLICY_NEW: oblock=%llu e->cblock=%u already existing invalid!",
				       name, from_oblock(oblock), from_cblock(ec->cblock));

			check_op(debug, "POLICY_NEW", ec->op);
			remove_debug_entry(debug, ec);
			ec = eo = NULL;
			debug->bad.new++;

		} else
			debug->good.new++;


		if (eo) {
			remove_debug_entry(debug, eo);
			ec = eo = NULL;
		}

		break;

	case POLICY_REPLACE:
		/* POLICY_MISS -> POLICY_REPLACE ok */
		/* POLICY_HIT, POLICY_NEW, POLICY_REPLACE -> POLICY_REPLACE FALSE. */
		if (eo) {
			if (from_oblock(result->old_oblock) == from_oblock(oblock)) {
				if (debug->verbose & 0x2)
					DMWARN("%s->map: POLICY_REPLACE: e->cblock=%u e->oblock=%llu = result->old_block=%llu invalid!",
					       name,
					       from_cblock(eo->cblock),
					       (LLU) from_oblock(eo->oblock),
					       (LLU) from_oblock(result->old_oblock));

				debug->bad.replace++;

			} else
				debug->good.replace++;

			check_op(debug, "POLICY_REPLACE", eo->op);
			remove_debug_entry(debug, eo);
			ec = eo = NULL;
		}

		break;

	case POLICY_MISS:
		/* POLICY_MISS -> POLICY_MISS ok. */
		/* POLICY_HIT, POLICY_NEW, POLICY_REPLACE -> POLICY_MISS FALSE. */
		if (eo) {
			check_op(debug, "POLICY_MISS", eo->op);

			if (eo->op != POLICY_MISS) {
				if (debug->verbose & 0x2)
					DMWARN("%s->map: POLICY_MISS: op=%u != POLICY_MISS invalid!", name, eo->op);

				debug->bad.miss++;
			}

		} else
			debug->good.miss++;

		cblock_ok = false;
		break;

	default:
		if (debug->verbose > 1)
			DMWARN("%s->map: invalid op code %u", name, result->op);

		cblock_ok = false;
		debug->good.op--;
		debug->bad.op++;
	}

	eo = eo ? eo : insert_debug_entry(debug, oblock, cblock_ok ? result->cblock : debug->cache_size);
	eo->op = result->op; /* Memorize op for next analysis cycle. */
	debug->analysed++;
}

static void log_stats(struct debug_policy *debug)
{
	if (debug->hit++ > (from_cblock(debug->cache_size) << 3)) {
		debug->hit = 0;
		DMINFO("%s nr_dblocks_allocated/analysed = %u/%u good/bad hit=%u/%u,miss=%u/%u,map_miss=%u/%u,new=%u/%u,replace=%u/%u,op=%u/%u,"
		       "lookup=%u/%u,set_dirty=%u/%u,clear_dirty=%u/%u,"
		       "cblock=%u/%u,load=%u/%u,remove=%u/%u,force=%u/%u,writeback=%u/%u,invalidate=%u/%u residency ok/larger/invalid=%u/%u/%u",
		       dm_cache_policy_get_name(debug->policy.child),
		       debug->nr_dblocks_allocated, debug->analysed,
		       debug->good.hit, debug->bad.hit, debug->good.miss, debug->bad.miss, debug->good.map_miss, debug->bad.map_miss, debug->good.new, debug->bad.new,
		       debug->good.replace, debug->bad.replace, debug->good.op, debug->bad.op,
		       debug->good.lookup, debug->bad.lookup, debug->good.dirty, debug->bad.dirty, debug->good.clean, debug->bad.clean,
		       debug->good.cblock, debug->bad.cblock,
		       debug->good.load, debug->bad.load, debug->good.remove, debug->bad.remove, debug->good.force, debug->bad.force,
		       debug->good.writeback, debug->bad.writeback, debug->good.invalidate, debug->bad.invalidate,
		       debug->good.residency, debug->bad.residency_larger, debug->bad.residency_invalid);
	}
}

/* Public interface (see dm-cache-policy.h */
static int debug_map(struct dm_cache_policy *p, dm_oblock_t oblock,
		     bool can_block, bool can_migrate, bool discarded_oblock,
		     struct bio *bio, struct policy_result *result)
{
	int r;
	struct debug_policy *debug = to_debug_policy(p);

	result->op = POLICY_MISS;

	if (can_block)
		mutex_lock(&debug->lock);

	else if (!mutex_trylock(&debug->lock))
		return -EWOULDBLOCK;

	r = policy_map(p->child, oblock, can_block, can_migrate,
		       discarded_oblock, bio, result);

	/* analyze_map_reult() allocates a debug entry unless -EWOULDBLOCK */
	analyse_map_result(debug, oblock, r, result);

	log_stats(debug);
	mutex_unlock(&debug->lock);

	return r;
}

static int debug_lookup(struct dm_cache_policy *p, dm_oblock_t oblock, dm_cblock_t *cblock)
{
	int r;
	const char *name = dm_cache_policy_get_name(p->child);
	struct debug_policy *debug = to_debug_policy(p);
	struct debug_entry *ec = NULL;

	if (!mutex_trylock(&debug->lock))
		return -EWOULDBLOCK;

	r = policy_lookup(p->child, oblock, cblock);
	if (!r)
		ec = lookup_debug_entry_by_cache_block(debug, *cblock);

	mutex_unlock(&debug->lock);

	if (r) {
		switch (r) {
		case -ENOENT:
		case -EWOULDBLOCK:
			debug->good.lookup++;
			break;

		default:
			debug->bad.lookup++;
			DMWARN("%s->lookup: inalid code %u", name, r);
		}

	} else if (ec) {
		if (*cblock != ec->cblock)
			DMWARN("%s->lookup returned invalid cblock=%llu; %llu expected!",
			       name, (LLU) from_cblock(*cblock), (LLU) from_cblock(ec->cblock));

	} else
			DMWARN("%s->lookup returned non-existing cblock=%llu!",
			       name, (LLU) from_cblock(*cblock));

	return r;
}

static void analyze_set_clear_dirty(struct dm_cache_policy *p,
				    bool dirty, int r, dm_oblock_t oblock)
{
	struct debug_policy *debug = to_debug_policy(p);
	const char *name = dm_cache_policy_get_name(p->child);
	struct debug_entry *eo;

	mutex_lock(&debug->lock);
	eo = lookup_debug_entry_by_origin_block(debug, oblock);
	mutex_unlock(&debug->lock);

	BUG_ON(!eo);
	BUG_ON(eo->oblock != oblock);

	switch (r) {
	case 0:
	case 1:
	case -ENOENT:
	case -EOPNOTSUPP:
		dirty ? debug->good.dirty++ : debug->good.clean++;
		break;

	case -EINVAL:
		DMWARN("%s->%s_dirty no state change on cblock=%u/oblock=%llu [%d]",
		       name, dirty ? "set" : "clear", eo->cblock, oblock, r);
		dirty ? debug->bad.dirty++ : debug->bad.clean++;
		break;

	default:
		DMWARN("%s->%s_dirty invalid return=%d", name, dirty ? "set" : "clear", r);
		dirty ? debug->bad.dirty++ : debug->bad.clean++;
	}
}

static int debug_set_dirty(struct dm_cache_policy *p, dm_oblock_t oblock)
{
	int r = policy_set_dirty(p->child, oblock);

	analyze_set_clear_dirty(p, true, r, oblock);
	return r;
}

static int debug_clear_dirty(struct dm_cache_policy *p, dm_oblock_t oblock)
{
	int r = policy_clear_dirty(p->child, oblock);

	analyze_set_clear_dirty(p, false, r, oblock);
	return r;
}


static void debug_destroy(struct dm_cache_policy *p)
{
	struct debug_policy *debug = to_debug_policy(p);

	debug->hit = ~0U;
	log_stats(debug);

	DMINFO("Test %s", test_ok(debug) ? "ok" : "FAILED");

	free_debug_blocks_and_hashs(debug);
	kfree(debug);
}

static int debug_load_mapping(struct dm_cache_policy *p,
			      dm_oblock_t oblock, dm_cblock_t cblock,
			      void *hint, bool hint_valid)
{
	int r;
	struct debug_policy *debug = to_debug_policy(p);
	struct debug_entry *eo, *ec;

	mutex_lock(&debug->lock);
	eo = lookup_debug_entry_by_origin_block(debug, oblock);
	ec = lookup_debug_entry_by_cache_block(debug, cblock);
	if (eo || ec) {
		if (debug->verbose & 0x2)
			DMWARN("%s->load_mapping: oblock=%llu/cblock=%u already existing invalid!",
				dm_cache_policy_get_name(p->child), (LLU) from_oblock(oblock), from_cblock(cblock));

		remove_debug_entry(debug, eo ? eo : ec);
		debug->bad.load++;

	} else {
		insert_debug_entry(debug, oblock, cblock);
		debug->good.load++;
	}

	r = policy_load_mapping(p->child, oblock, cblock, hint, hint_valid);
	mutex_unlock(&debug->lock);

	return r;
}

static int debug_walk_mappings(struct dm_cache_policy *p, policy_walk_fn fn, void *context)
{
	int r = policy_walk_mappings(p->child, fn, context);

	if (r)
		DMWARN("%s->walk_mapping returned %d", dm_cache_policy_get_name(p->child), r);

	return r;
}

static void debug_remove_mapping(struct dm_cache_policy *p, dm_oblock_t oblock)
{
	struct debug_policy *debug = to_debug_policy(p);
	struct debug_entry *e;

	mutex_lock(&debug->lock);
	e = lookup_debug_entry_by_origin_block(debug, oblock);
	if (e) {
		remove_debug_entry(debug, e);
		debug->good.remove++;

	} else {
		if (debug->verbose & 0x2)
			DMWARN("%s->remove_mapping: no entry for oblock=%llu invalid!",
			       dm_cache_policy_get_name(p->child), (LLU) from_oblock(oblock));

		debug->bad.remove++;
	}

	policy_remove_mapping(p->child, oblock);
	mutex_unlock(&debug->lock);
}

static void debug_force_mapping(struct dm_cache_policy *p,
				dm_oblock_t current_oblock, dm_oblock_t new_oblock)
{
	struct debug_policy *debug = to_debug_policy(p);
	struct debug_entry *e;

	mutex_lock(&debug->lock);
	e = lookup_debug_entry_by_origin_block(debug, current_oblock);
	if (e) {
		enum policy_operation op = e->op;
		dm_cblock_t cblock = e->cblock;

		/* Replace with new information .*/
		remove_debug_entry(debug, e);
		e = insert_debug_entry(debug, new_oblock, cblock);
		e->op = op;
		debug->good.force++;

	} else {
		if (debug->verbose & 0x2)
			DMWARN("%s->force_mapping: current_oblock=%llu/oblock=%llu invalid!",
			       dm_cache_policy_get_name(p->child),
			       (LLU) from_oblock(current_oblock), (LLU) from_oblock(new_oblock));

		debug->bad.force++;
	}

	policy_force_mapping(p->child, current_oblock, new_oblock);
	mutex_unlock(&debug->lock);
}

static void analyze_wb_im_result(struct debug_policy *debug, bool writeback_work, int r,
				 dm_cblock_t *cblock, dm_oblock_t *oblock)
{
	bool err = false;
	const char *name = dm_cache_policy_get_name(debug->policy.child);
	const char *caller = writeback_work ? "writeback_work" : "invalidate_mapping";

	if (r) {
		if (r != (writeback_work ? -ENODATA : -ENOENT)) {
			DMWARN("%s->%s return code %d invalid!", name, caller, r);
			err = true;
		}

	} else {
		struct debug_entry *ec;

		mutex_lock(&debug->lock);
		ec = lookup_debug_entry_by_cache_block(debug, *cblock);
		if (!ec)
			DMWARN("%s->%s cblock=%u/oblock=%llu unknown to debug", name, caller,
			       from_cblock(*cblock), from_oblock(*oblock));
		mutex_unlock(&debug->lock);

		if (from_cblock(*cblock) >= from_cblock(debug->cache_size)) {
			DMWARN("%s->%s cblock=%u invalid!", name, caller, from_cblock(*cblock));
			err = true;
		}

		if (from_oblock(*oblock) >= from_oblock(debug->origin_blocks)) {
			DMWARN("%s->%s oblock=%llu invalid!", name, caller, (LLU) from_oblock(*oblock));
			err = true;
		}

	}

	if (err)
		writeback_work ? debug->bad.writeback++ : debug->bad.invalidate++;
	else
		writeback_work ? debug->good.writeback++ : debug->good.invalidate++;
}

static int debug_writeback_work(struct dm_cache_policy *p,
				dm_oblock_t *oblock, dm_cblock_t *cblock)
{
	struct debug_policy *debug = to_debug_policy(p);
	int r = policy_writeback_work(p->child, oblock, cblock);

	analyze_wb_im_result(debug, true, r, cblock, oblock);

	return r;
}

static int debug_invalidate_mapping(struct dm_cache_policy *p,
				    dm_oblock_t *oblock, dm_cblock_t *cblock)
{
	struct debug_policy *debug = to_debug_policy(p);
	int r = policy_invalidate_mapping(p->child, oblock, cblock);

	analyze_wb_im_result(debug, false, r, cblock, oblock);

	return r;
}

static dm_cblock_t debug_residency(struct dm_cache_policy *p)
{
	struct debug_policy *debug = to_debug_policy(p);
	bool ok = true;
	const char *name = dm_cache_policy_get_name(p->child);
	dm_cblock_t r = policy_residency(p->child);

	if (from_cblock(r) > from_cblock(debug->cache_size)) {
		if (debug->verbose & 0x1)
			DMWARN("%s->residency: %u claimed larger than cache size=%u!",
			       name, from_cblock(r), from_cblock(debug->cache_size));

		debug->bad.residency_larger++;
		ok = false;
	}

	if (from_cblock(r) != debug->good.new) {
		if (debug->verbose & 0x1)
			DMWARN("%s->residenc: claimed residency=%u invalid vs. %u allocated",
			       name, from_cblock(r), debug->nr_dblocks_allocated);

		debug->bad.residency_invalid++;
		ok = false;
	}

	if (ok)
		debug->good.residency++;

	return r;
}

static void debug_tick(struct dm_cache_policy *p)
{
	policy_tick(p->child);
}

static const char *verbose_str = "verbose";

static int debug_set_config_value(struct dm_cache_policy *p,
				  const char *key, const char *value)
{
	struct debug_policy *debug = to_debug_policy(p);
	int r;

	if (!strcasecmp(key, verbose_str)) {
		unsigned long tmp;

		if (kstrtoul(value, 10, &tmp) || tmp > 7)
			return -EINVAL;

		debug->verbose = tmp;
		smp_wmb();
		r = 0;

	} else {
		r = policy_set_config_value(p->child, key, value);
		if (r && r != -EINVAL)
			DMWARN("%s->set_config_value returned %d",
			       dm_cache_policy_get_name(p->child), r);
	}

	return r;
}

static int debug_emit_config_values(struct dm_cache_policy *p, char *result, unsigned maxlen)
{
	struct debug_policy *debug = to_debug_policy(p);
	int r;
	ssize_t sz = 0;

	DMEMIT("2 %s %x ", verbose_str, debug->verbose);

	r = policy_emit_config_values(p->child, result, maxlen);
	if (r && r != -EINVAL)
		DMWARN("%s->emit_config_values returned %d",
		       dm_cache_policy_get_name(p->child), r);

	return r;
}

/* Init the policy plugin interface function pointers. */
static void init_policy_functions(struct debug_policy *debug)
{
	dm_cache_shim_utils_init_shim_policy(&debug->policy);
	debug->policy.destroy = debug_destroy;
	debug->policy.map = debug_map;
	debug->policy.lookup = debug_lookup;
	debug->policy.set_dirty = debug_set_dirty;
	debug->policy.clear_dirty = debug_clear_dirty;
	debug->policy.load_mapping = debug_load_mapping;
	debug->policy.walk_mappings = debug_walk_mappings;
	debug->policy.remove_mapping = debug_remove_mapping;
	debug->policy.force_mapping = debug_force_mapping;
	debug->policy.invalidate_mapping = debug_invalidate_mapping;
	debug->policy.writeback_work = debug_writeback_work;
	debug->policy.residency = debug_residency;
	debug->policy.tick = debug_tick;
	debug->policy.emit_config_values = debug_emit_config_values;
	debug->policy.set_config_value = debug_set_config_value;
}

static struct dm_cache_policy *debug_create(dm_cblock_t cache_size,
					    sector_t origin_sectors,
					    sector_t block_sectors)
{
	int r;
	uint64_t origin_blocks = origin_sectors;
	struct debug_policy *debug = kzalloc(sizeof(*debug), GFP_KERNEL);

	if (!debug)
		return NULL;

	init_policy_functions(debug);

	do_div(origin_blocks, block_sectors);
	debug->cache_size = cache_size;
	debug->origin_blocks = to_oblock(origin_blocks);
	mutex_init(&debug->lock);

	r = alloc_debug_blocks_and_hashs(debug, debug->origin_blocks, cache_size);
	if (!r)
		return &debug->policy;

	DMWARN("blocks_and_hashs memory allocation failed");
	kfree(debug);
	return NULL;
}
/*----------------------------------------------------------------------------*/

static struct dm_cache_policy_type dbg_policy_type = {
	.name = "dbg",
	.version = {1, 0, 0},
	.owner = THIS_MODULE,
	.create = debug_create,
	.features = DM_CACHE_POLICY_SHIM
};

static struct dm_cache_policy_type debug_policy_type = {
	.name = "debug",
	.version = {1, 0, 0},
	.owner = THIS_MODULE,
	.create = debug_create,
	.features = DM_CACHE_POLICY_SHIM
};

static int __init debug_init(void)
{
	int r;

	debug_block_cache = KMEM_CACHE(debug_entry, 0);
	if (!debug_block_cache)
		return -ENOMEM;

	r = dm_cache_policy_register(&dbg_policy_type);
	if (r)
		goto bad_kmem_cache_destroy;

	r = dm_cache_policy_register(&debug_policy_type);
	if (r)
		goto bad_dbg_unregister;

	DMINFO("version %u.%u.%u loaded",
	       debug_policy_type.version[0],
	       debug_policy_type.version[1],
	       debug_policy_type.version[2]);

	return 0;

bad_dbg_unregister:
	dm_cache_policy_unregister(&dbg_policy_type);
bad_kmem_cache_destroy:
	kmem_cache_destroy(debug_block_cache);
	return r;
}

static void __exit debug_exit(void)
{
	kmem_cache_destroy(debug_block_cache);
	dm_cache_policy_unregister(&debug_policy_type);
	dm_cache_policy_unregister(&dbg_policy_type);
}

module_init(debug_init);
module_exit(debug_exit);

MODULE_AUTHOR("Heinz Mauelshagen <dm-devel@redhat.com>");
MODULE_LICENSE("GPL");
MODULE_DESCRIPTION("debug cache policy shim");

MODULE_ALIAS("dm-cache-dbg");
/*----------------------------------------------------------------*/
