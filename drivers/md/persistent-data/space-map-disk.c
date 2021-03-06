#include <linux/list.h>
#include <linux/slab.h>
#include <asm-generic/bitops/le.h>

#include "space-map-disk.h"
#include "btree-internal.h"

/*----------------------------------------------------------------*/

/* on disk data */
struct sm_root {
	__le64 nr_blocks;
	__le64 nr_allocated;
	__le64 bitmap_root;
	__le64 ref_count_root;
};

/* FIXME: add a spinlock to protect the in core structure */
struct sm_disk {
	struct transaction_manager *tm;

	struct btree_info bitmap_info;
	struct btree_info ref_count_info;

	uint32_t block_size;
	uint32_t entries_per_block;
	block_t nr_blocks;
	block_t nr_allocated;
	block_t bitmap_root;
	block_t ref_count_root;
};

struct index_entry {
	__le64 b;
	__le32 nr_free;
        __le32 none_free_before;
};

#define ENTRIES_PER_BYTE 4

/*----------------------------------------------------------------*/

static uint64_t div_up(uint64_t v, uint64_t n)
{
	uint64_t t = v;
	uint64_t rem = do_div(t, n);
	return t + (rem > 0 ? 1 : 0);
}

static uint64_t mod64(uint64_t n, uint64_t d)
{
	return do_div(n, d);
}

/*
 * On disk format
 *
 * We hold 2 bits per block, which represent UNUSED = 0, REF_COUNT = 1,
 * REF_COUNT = 2 and REF_COUNT = many.  A separate btree holds ref counts
 * for blocks that are over 2.
 */
#define ENTRIES_PER_WORD 32
static unsigned lookup_bitmap_(void *addr, block_t b)
{
	unsigned val = 0;
	__le64 *words = (__le64 *) addr;
	__le64 *w = words + (b / ENTRIES_PER_WORD);
	b %= ENTRIES_PER_WORD;

	val = generic_test_le_bit(b * 2, (void *) w) ? 1 : 0;
	val <<= 1;
	val |= generic_test_le_bit(b * 2 + 1, (void *) w) ? 1 : 0;
	return val;
}

static void set_bitmap_(void *addr, block_t b, unsigned val)
{
	__le64 *words = (__le64 *) addr;
	__le64 *w = words + (b / ENTRIES_PER_WORD);
	b %= ENTRIES_PER_WORD;

	if (val & 2)
		generic___set_le_bit(b * 2, (void *) w);
	else
		generic___clear_le_bit(b * 2, (void *) w);

	if (val & 1)
		generic___set_le_bit(b * 2 + 1, (void *) w);
	else
		generic___clear_le_bit(b * 2 + 1, (void *) w);
}

static int find_free_(void *addr, unsigned begin, unsigned end, unsigned *position)
{
	/* FIXME: slow, find a quicker way in Hackers Delight */
	while (begin < end) {
		if (!lookup_bitmap_(addr, begin)) {
			*position = begin;
			return 0;
		}
		begin++;
	}

	return -ENOSPC;
}

static inline block_t min_block(block_t b1, block_t b2)
{
	return (b1 <= b2) ? b1 : b2;
}

static inline block_t max_block(block_t b1, block_t b2)
{
	return (b1 >= b2) ? b1 : b2;
}

static struct sm_disk *alloc_smd(struct transaction_manager *tm)
{
	return kmalloc(sizeof(struct sm_disk), GFP_KERNEL);
}

static int io_init(struct sm_disk *io,
		   struct transaction_manager *tm)
{
	io->tm = tm;
	io->bitmap_info.tm = tm;
	io->bitmap_info.levels = 1;

	/*
	 * Because the new bitmap blocks are created via a shadow
	 * operation, the old entry has already had it's reference count
	 * decremented.  So we don't need the btree to do any book
	 * keeping.
	 */
	io->bitmap_info.value_type.size = sizeof(struct index_entry);
	io->bitmap_info.value_type.copy = NULL;
	io->bitmap_info.value_type.del = NULL;
	io->bitmap_info.value_type.equal = NULL;

	io->ref_count_info.tm = tm;
	io->ref_count_info.levels = 1;
	io->ref_count_info.value_type.size = sizeof(uint32_t);
	io->ref_count_info.value_type.copy = NULL;
	io->ref_count_info.value_type.del = NULL;
	io->ref_count_info.value_type.equal = NULL;

	io->block_size = bm_block_size(tm_get_bm(tm));

	if (io->block_size > (1 << 30)) {
		printk(KERN_ALERT "block size too big to hold bitmaps");
		return -1;
	}
	io->entries_per_block = io->block_size * 4;
	io->nr_blocks = 0;
	io->bitmap_root = 0;
	io->ref_count_root = 0;

	return 0;
}

static int io_new(struct sm_disk *io, struct transaction_manager *tm, block_t nr_blocks)
{
	int r;
	block_t i;
	unsigned blocks;

	r = io_init(io, tm);
	if (r < 0)
		return r;

	io->nr_blocks = nr_blocks;
	io->nr_allocated = 0;
	r = btree_empty(&io->bitmap_info, &io->bitmap_root);
	if (r < 0)
		return r;

	blocks = div_up(nr_blocks, io->entries_per_block);
	for (i = 0; i < blocks; i++) {
		struct block *b;
		struct index_entry idx;

		r = tm_new_block(tm, &b);
		if (r < 0)
			return r;
		idx.b = __cpu_to_le64(block_location(b));

		r = tm_unlock(tm, b);
		if (r < 0)
			return r;

		idx.nr_free = __cpu_to_le32(io->entries_per_block);
		idx.none_free_before = 0;

		r = btree_insert(&io->bitmap_info, io->bitmap_root,
				 &i, &idx, &io->bitmap_root);
		if (r < 0)
			return r;
	}

	r = btree_empty(&io->ref_count_info, &io->ref_count_root);
	if (r < 0) {
		/* FIXME: put back in when non-recursive del written */
		// btree_del(&bitmap_info, bitmap_root);
		return r;
	}

	return 0;
}

static int io_open(struct sm_disk *io,
		   struct transaction_manager *tm,
		   void *root,
		   size_t len)
{
	int r;
	struct sm_root *smr = (struct sm_root *) root;

	if (len < sizeof(struct sm_root)) {
		printk(KERN_ALERT "sm_disk root too small");
		return -ENOMEM;
	}

	r = io_init(io, tm);
	if (r < 0)
		return r;

	io->nr_blocks = __le64_to_cpu(smr->nr_blocks);
	io->nr_allocated = __le64_to_cpu(smr->nr_allocated);
	io->bitmap_root = __le64_to_cpu(smr->bitmap_root);
	io->ref_count_root = __le64_to_cpu(smr->ref_count_root);

	return 0;
}

static int io_lookup(struct sm_disk *io, block_t b, uint32_t *result)
{
	int r;
	block_t index = b;
	struct index_entry ie;
	do_div(index, io->entries_per_block);

	r = btree_lookup_equal(&io->bitmap_info, io->bitmap_root, &index, &ie);
	if (r < 0)
		return r;

	{
		struct block *blk;
		r = tm_read_lock(io->tm, __le64_to_cpu(ie.b), &blk);
		if (r < 0)
			return r;

		*result = lookup_bitmap_(block_data(blk), mod64(b, io->entries_per_block));
		r = tm_unlock(io->tm, blk);
		if (r < 0) {
			return r;
		}
	}

	if (*result == 3) {
		__le32 le_rc;
		r = btree_lookup_equal(&io->ref_count_info,
				       io->ref_count_root,
				       &b, &le_rc);
		if (r < 0)
			return r;

		*result = __le32_to_cpu(le_rc);
	}

	return 0;
}

static int
io_find_unused(struct sm_disk *io, block_t begin, block_t end, block_t *result)
{
	int r;
	block_t index_begin = begin;
	block_t index_end = div_up(end, io->entries_per_block);
	struct index_entry ie;
	block_t i;

	do_div(index_begin, io->entries_per_block);
	for (i = index_begin; i < index_end; i++, begin = 0) {
		r = btree_lookup_equal(&io->bitmap_info, io->bitmap_root, &i, &ie);
		if (r < 0)
			return r;

		if (__le32_to_cpu(ie.nr_free) > 0) {
			struct block *blk;
			unsigned position;

			uint32_t bit_end =
				i == index_end - 1 ?
				mod64(end, io->entries_per_block) :
				io->entries_per_block;

			r = tm_read_lock(io->tm, __le64_to_cpu(ie.b), &blk);
			if (r < 0)
				return r;

			r = find_free_(block_data(blk),
				       mod64(begin, io->entries_per_block),
				       bit_end, &position);
			if (r < 0) {
				tm_unlock(io->tm, blk);
				return r;
			}

			*result = i * io->entries_per_block + position;

			r = tm_unlock(io->tm, blk);
			if (r < 0)
				return r;

			BUG_ON(*result >= io->nr_blocks);
			return 0;
		}
	}

	return -ENOSPC;
}

static int io_insert(struct sm_disk *io, block_t b, uint32_t ref_count)
{
	int r;
	uint32_t bit, old;
	struct block *nb;
	block_t index = b;
	struct index_entry ie;
	void *bm;
	int inc;

	do_div(index, io->entries_per_block);
	r = btree_lookup_equal(&io->bitmap_info, io->bitmap_root, &index, &ie);
	if (r < 0)
		return r;

	r = tm_shadow_block(io->tm, __le64_to_cpu(ie.b), &nb, &inc);
	if (r < 0) {
		printk(KERN_ALERT "shadow failed");
		return r;
	}

	bm = block_data(nb);
	bit = mod64(b, io->entries_per_block);
	old = lookup_bitmap_(bm, bit);

	if (ref_count <= 2) {
		set_bitmap_(bm, bit, ref_count);

		{
			unsigned v = lookup_bitmap_(bm, bit);
			BUG_ON(v != ref_count);
		}

		if (old > 2) {
#if 0
			if (!btree_remove(&io->ref_count_info, io->ref_count_root, &b, &io->ref_count_root))
				abort();
#endif
		}
	} else {
		__le32 le_rc = __cpu_to_le32(ref_count);
		set_bitmap_(bm, bit, 3);
		r = btree_insert(&io->ref_count_info, io->ref_count_root, &b, &le_rc, &io->ref_count_root);
		if (r < 0) {
			tm_unlock(io->tm, nb);
			/* FIXME: release shadow? or assume the whole transaction will be ditched */
			printk(KERN_ALERT "ref count insert failed");
			return r;
		}
	}

	r = tm_unlock(io->tm, nb);
	if (r < 0)
		return r;

	if (ref_count && !old) {
		io->nr_allocated++;
		ie.nr_free = __cpu_to_le32(__le32_to_cpu(ie.nr_free) - 1);
		if (__le32_to_cpu(ie.none_free_before) == b)
			ie.none_free_before = __cpu_to_le32(b + 1);

	} else if (old && !ref_count) {
		io->nr_allocated--;
		ie.nr_free = __cpu_to_le32(__le32_to_cpu(ie.nr_free) + 1);
		ie.none_free_before = __cpu_to_le32(min_block(__le32_to_cpu(ie.none_free_before), b));
	}

	/*
	 * FIXME: we have a race here, since another thread may have
	 * altered |ie| in the meantime.  Not important yet.
	 */
	ie.b = __cpu_to_le64(block_location(nb));
	r = btree_insert(&io->bitmap_info, io->bitmap_root, &index, &ie, &io->bitmap_root);
	if (r < 0)
		return r;

	return 0;
}

/*----------------------------------------------------------------*/

static void destroy(void *context)
{
	struct sm_disk *smd = (struct sm_disk *) context;
	printk(KERN_ALERT "sm_disk allocated %u blocks",
	       (unsigned) smd->nr_allocated);
	kfree(smd);
}

static int get_nr_blocks(void *context, block_t *count)
{
	struct sm_disk *smd = (struct sm_disk *) context;
	*count = smd->nr_blocks;
	return 0;
}

static int get_count(void *context, block_t b, uint32_t *result)
{
	struct sm_disk *smd = (struct sm_disk *) context;
	return io_lookup(smd, b, result);
}

static int set_count_(void *context, block_t b, uint32_t count)
{
	struct sm_disk *smd = (struct sm_disk *) context;
	return io_insert(smd, b, count);
}

static int set_count(void *context, block_t b, uint32_t count)
{
	int r;
	struct sm_disk *smd = (struct sm_disk *) context;
	unsigned held = bm_locks_held(tm_get_bm(smd->tm));
	r = set_count_(context, b, count);
	BUG_ON(bm_locks_held(tm_get_bm(smd->tm)) != held);
	return r;
}

static int get_free_(void *context, block_t low, block_t high, block_t *b)
{
	struct sm_disk *smd = (struct sm_disk *) context;
	int r;

	high = min(high, smd->nr_blocks);
	if (low >= high)
		return -ENOSPC;

	r = io_find_unused(smd, low, high, b);
	if (r == -ENODATA)
		return -ENOSPC;

	else if (r < 0)
		return r;

	return 0;
}

static int get_free(void *context, block_t *b)
{
	struct sm_disk *smd = (struct sm_disk *) context;
	return get_free_(context, 0, smd->nr_blocks, b);
}

static int get_free_in_range(void *context, block_t low, block_t high, block_t *b)
{
	return get_free_(context, low, high, b);
}

static int commit(void *context)
{
	/*
	 * We don't need to do anything here other than drop all held block
	 * locks.
	 */
	return 0;
}

static int root_size(void *context, size_t *result)
{
	*result = sizeof(struct sm_root);
	return 0;
}

static int copy_root(void *context, void *where, size_t max)
{
	struct sm_disk *smd = (struct sm_disk *) context;
	struct sm_root root;

	root.nr_blocks = __cpu_to_le64(smd->nr_blocks);
	root.nr_allocated = __cpu_to_le64(smd->nr_allocated);
	root.bitmap_root = __cpu_to_le64(smd->bitmap_root);
	root.ref_count_root = __cpu_to_le64(smd->ref_count_root);

	if (max < sizeof(root))
		return -ENOSPC;

	memcpy(where, &root, sizeof(root));
	return 0;
}

/*----------------------------------------------------------------*/

static struct space_map_ops ops_ = {
	.destroy = destroy,
	.get_nr_blocks = get_nr_blocks,
	.get_count = get_count,
	.set_count = set_count,
	.get_free = get_free,
	.get_free_in_range = get_free_in_range,
	.commit = commit,
	.root_size = root_size,
	.copy_root = copy_root
};

struct space_map *sm_disk_create(struct transaction_manager *tm,
				 block_t nr_blocks)
{
	struct space_map *sm = NULL;
	struct sm_disk *smd = alloc_smd(tm);
	if (smd) {
		int r;
		r = io_new(smd, tm, nr_blocks);
		if (r < 0) {
			kfree(smd);
			return NULL;
		}

		sm = kmalloc(sizeof(*sm), GFP_KERNEL);
		if (!sm) {
			kfree(smd);
		} else {
			sm->ops = &ops_;
			sm->context = smd;
		}
	}

	return sm;
}
EXPORT_SYMBOL_GPL(sm_disk_create);

struct space_map *sm_disk_open(struct transaction_manager *tm,
			       void *root, size_t len)
{
	struct space_map *sm = NULL;
	struct sm_disk *smd = alloc_smd(tm);
	if (smd) {
		int r;
		r = io_open(smd, tm, root, len);
		if (r < 0) {
			kfree(smd);
			return NULL;
		}

		sm = kmalloc(sizeof(*sm), GFP_KERNEL);
		if (!sm) {
			kfree(smd);
		} else {
			sm->ops = &ops_;
			sm->context = smd;
		}
	}

	return sm;
}
EXPORT_SYMBOL_GPL(sm_disk_open);

