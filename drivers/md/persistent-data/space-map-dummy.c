#include "space-map-staged.h"

/*----------------------------------------------------------------*/

struct sm_dummy {
	block_t nr_blocks;
};

static void destroy(void *context)
{
	kfree(context);
}

static int get_nr_blocks(void *context, block_t *count)
{
	struct sm_dummy *sm = (struct sm_dummy *) context;
	*count = sm->nr_blocks;
	return 0;
}

static int get_count(void *context, block_t b, uint32_t *result)
{
	*result = 0;
	return 0;
}

static int set_count(void *context, block_t b, uint32_t count)
{
	BUG_ON(1);
	return -1;
}

static int get_free_in_range(void *context, block_t low, block_t high, block_t *b)
{
	*b = low;
	return 0;
}
static int get_free(void *context, block_t *b)
{
	BUG_ON(1);
	return -1;
}

static int root_size(void *context, size_t *result)
{
	BUG_ON(1);
	return -1;
}

static int copy_root(void *context, void *copy_to_here, size_t len)
{
	BUG_ON(1);
	return -1;
}

static int commit(void *context)
{
	BUG_ON(1);
	return -1;
}


static struct space_map_ops ops_ = {
	.destroy = destroy,
	.get_nr_blocks = get_nr_blocks,
	.get_count = get_count,
	.set_count = set_count,
	.get_free = get_free,
	.get_free_in_range = get_free_in_range,
	.root_size = root_size,
	.copy_root = copy_root,
	.commit = commit,
};

struct space_map *sm_dummy_create(block_t nr_blocks)
{
	struct space_map *sm = NULL;
	struct sm_dummy *smc = kmalloc(sizeof(*smc), GFP_KERNEL);
	if (smc) {
		smc->nr_blocks = nr_blocks;
		sm = kmalloc(sizeof(*sm), GFP_KERNEL);
		if (!sm) {
			kfree(smc);
		} else {
			sm->ops = &ops_;
			sm->context = smc;
		}
	}

	return sm;
}
EXPORT_SYMBOL_GPL(sm_dummy_create);

/*----------------------------------------------------------------*/
