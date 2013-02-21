/*
 * Copyright (C) 2013 Red Hat. All rights reserved.
 *
 * Stackable background write cache replacement policy module.
 *
 * This file is released under the GPL.
 */

#include "dm-cache-policy.h"
#include "dm-cache-policy-internal.h"
#include "dm.h"

#include <linux/module.h>
#include <linux/moduleparam.h>

#define	LLU	long long unsigned

/*----------------------------------------------------------------*/

struct policy {
	struct dm_cache_policy policy;

	struct dm_cache_policy *real_policy;
	dm_cblock_t cache_blocks, threshold;
	int threshold_arg;
	atomic_t nr_dirty;
};

/*----------------------------------------------------------------------------*/
/* Low-level functions. */
static struct policy *to_policy(struct dm_cache_policy *pe)
{
	return container_of(pe, struct policy, policy);
}

/*----------------------------------------------------------------------------*/

/* Public interface (see dm-cache-policy.h */
static void background_destroy(struct dm_cache_policy *pe)
{
	struct policy *p = to_policy(pe);

	dm_cache_policy_destroy(p->real_policy);
	kfree(p);
}

static int background_map(struct dm_cache_policy *pe, dm_oblock_t oblock,
		     bool can_block, bool can_migrate, bool discarded_oblock,
		     struct bio *bio, struct policy_result *result)
{
	return policy_map(to_policy(pe)->real_policy, oblock, can_block, can_migrate,
			  discarded_oblock, bio, result);
}

static int background_lookup(struct dm_cache_policy *pe, dm_oblock_t oblock, dm_cblock_t *cblock)
{
	return policy_lookup(to_policy(pe)->real_policy, oblock, cblock);
}

static int background_set_dirty(struct dm_cache_policy *pe, dm_oblock_t oblock)
{
	int r;
	struct policy *p = to_policy(pe);

	r = policy_set_dirty(p->real_policy, oblock);
	BUG_ON(r < 0);
	if (!r) {
		BUG_ON(atomic_read(&p->nr_dirty) > from_cblock(p->cache_blocks));
		atomic_inc(&p->nr_dirty);
	}

	return r;
}

static int background_clear_dirty(struct dm_cache_policy *pe, dm_oblock_t oblock)
{
	int r;
	struct policy *p = to_policy(pe);

	r = policy_clear_dirty(p->real_policy, oblock);
	BUG_ON(r < 0);
	if (r) {
		BUG_ON(!atomic_read(&p->nr_dirty));
		atomic_dec(&p->nr_dirty);
	}

	return r;
}

static int background_load_mapping(struct dm_cache_policy *pe,
				   dm_oblock_t oblock, dm_cblock_t cblock,
				   uint32_t hint, bool hint_valid)
{
	return policy_load_mapping(to_policy(pe)->real_policy, oblock, cblock, hint, hint_valid);
}

static int background_walk_mappings(struct dm_cache_policy *pe, policy_walk_fn fn, void *context)
{
	return policy_walk_mappings(to_policy(pe)->real_policy, fn, context);
}

static void background_remove_mapping(struct dm_cache_policy *pe, dm_oblock_t oblock)
{
	policy_remove_mapping(to_policy(pe)->real_policy, oblock);
}

static void background_force_mapping(struct dm_cache_policy *pe,
				     dm_oblock_t current_oblock, dm_oblock_t oblock)
{
	policy_force_mapping(to_policy(pe)->real_policy, current_oblock, oblock);
}

static int background_writeback_work(struct dm_cache_policy *pe,
				     dm_oblock_t *oblock, dm_cblock_t *cblock)
{
	int r;
	struct policy *p = to_policy(pe);

	if (from_cblock(p->cache_blocks) - atomic_read(&p->nr_dirty) < from_cblock(p->threshold)) {
		r = policy_next_dirty_block(p->real_policy, oblock, cblock);
		if (!r) {
			BUG_ON(atomic_read(&p->nr_dirty) > from_cblock(p->cache_blocks));
			BUG_ON(!atomic_read(&p->nr_dirty));
			atomic_dec(&p->nr_dirty);
		}

	} else
		r = -ENOENT;

	return r;
}

static dm_cblock_t background_residency(struct dm_cache_policy *pe)
{
	return policy_residency(to_policy(pe)->real_policy);
}

static void background_tick(struct dm_cache_policy *pe)
{
	policy_tick(to_policy(pe)->real_policy);
}

static const char *threshold_string = "clean_block_pool_size";
static int background_status(struct dm_cache_policy *pe, status_type_t type,
			unsigned status_flags, char *result, unsigned maxlen)
{
	int r = 0;
	ssize_t sz = 0;
	struct policy *p = to_policy(pe);

	switch (type) {
	case STATUSTYPE_INFO:
		DMEMIT(" <r>%u</r>", atomic_read(&p->nr_dirty)); /* REMOVEME: only for development */
		break;

	case STATUSTYPE_TABLE:
		if (p->threshold_arg > -1)
			DMEMIT("%s %u ", threshold_string, p->threshold_arg);

		DMEMIT("%s ", dm_cache_policy_get_name(p->real_policy));
	}

	if (sz < maxlen)
		r = policy_status(p->real_policy, type, status_flags,
				  result + sz, maxlen - sz);

	return r;
}

#define	NOT_BACKGROUND_OPTION	1

static int process_config_option(struct policy *p, char **argv, bool set_ctr_arg)
{
	if (!strcasecmp(argv[0], threshold_string)) {
		unsigned long tmp;

		if (kstrtoul(argv[1], 10, &tmp) ||
		    tmp > from_cblock(p->cache_blocks))
			return -EINVAL;

		if (set_ctr_arg) {
			if (p->threshold_arg > -1)
				return -EINVAL;

			p->threshold_arg = tmp;
		}

		p->threshold = to_cblock(tmp);

		return 0;
	}

	return NOT_BACKGROUND_OPTION; /* Inform caller it's not our option. */
}

static int background_message(struct dm_cache_policy *pe, unsigned argc, char **argv)
{
	int r;
	struct policy *p = to_policy(pe);

	if (argc != 2)
		return -EINVAL;

	r = process_config_option(p, argv, false);

	return (r == NOT_BACKGROUND_OPTION) ? policy_message(p->real_policy, argc, argv) : r;
}

/* Init the policy plugin interface function pointers. */
static void init_policy_functions(struct policy *p)
{
	p->policy.destroy = background_destroy;
	p->policy.map = background_map;
	p->policy.lookup = background_lookup;
	p->policy.set_dirty = background_set_dirty;
	p->policy.clear_dirty = background_clear_dirty;
	p->policy.load_mapping = background_load_mapping;
	p->policy.walk_mappings = background_walk_mappings;
	p->policy.remove_mapping = background_remove_mapping;
	p->policy.force_mapping = background_force_mapping;
	p->policy.writeback_work = background_writeback_work;
	p->policy.next_dirty_block = NULL;
	p->policy.residency = background_residency;
	p->policy.tick = background_tick;
	p->policy.status = background_status;
	p->policy.message = background_message;
}

#define	MIN_ARG	3
static struct dm_cache_policy *background_create(dm_cblock_t cache_blocks,
						 sector_t origin_sectors,
						 sector_t block_sectors,
						 int argc, char **argv)
{
	int r;
	struct policy *p = kzalloc(sizeof(*p), GFP_KERNEL);

	if (!p)
		return NULL;

	if (argc < MIN_ARG)
		goto bad;

	init_policy_functions(p);

	p->cache_blocks = cache_blocks;
	p->threshold = 0;
	p->threshold_arg = -1;
	atomic_set(&p->nr_dirty, 0);

	r = process_config_option(p, argv, true);
	if (r)
		goto bad;

	p->real_policy = dm_cache_policy_create(argv[MIN_ARG - 1], cache_blocks,
						origin_sectors, block_sectors,
						argc - MIN_ARG, argv + MIN_ARG);
	if (p->real_policy)
		return &p->policy;

bad:
	kfree(p);
	return NULL;
}

/*----------------------------------------------------------------------------*/

static struct dm_cache_policy_type background_policy_type = {
	.name = "background",
	.owner = THIS_MODULE,
        .create = background_create
};

static int __init background_init(void)
{
	return dm_cache_policy_register(&background_policy_type);
}

static void __exit background_exit(void)
{
	dm_cache_policy_unregister(&background_policy_type);
}

module_init(background_init);
module_exit(background_exit);

MODULE_AUTHOR("Heinz Mauelshagen");
MODULE_LICENSE("GPL");
MODULE_DESCRIPTION("stackable background write cache replacement policy");

/*----------------------------------------------------------------------------*/
