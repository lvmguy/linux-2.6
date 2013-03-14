/*
 * Copyright (C) 2013 Red Hat. All rights reserved.
 *
 * Stackable background write cache replacement policy module.
 *
 * This file is released under the GPL.
 */

#include "dm-cache-policy-internal.h"

#include <linux/module.h>

/*----------------------------------------------------------------*/

struct policy {
	struct dm_cache_policy policy;
	struct dm_cache_policy *real_policy;

	dm_cblock_t threshold;
	atomic_t nr_dirty;

	dm_cblock_t cache_blocks;
	sector_t origin_sectors;
	sector_t block_sectors;
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

	if (p->real_policy)
		dm_cache_policy_destroy(p->real_policy);

	kfree(p);
}

static int background_map(struct dm_cache_policy *pe, dm_oblock_t oblock,
		     bool can_block, bool can_migrate, bool discarded_oblock,
		     struct bio *bio, struct policy_result *result)
{
	struct policy *p = to_policy(pe);

	if (p->real_policy)
		return policy_map(p->real_policy, oblock, can_block, can_migrate,
				  discarded_oblock, bio, result);
	else {
		result->op = POLICY_MISS;
		return 0;
	}
}

static int background_lookup(struct dm_cache_policy *pe, dm_oblock_t oblock, dm_cblock_t *cblock)
{
	struct policy *p = to_policy(pe);

	return p->real_policy ? policy_lookup(p->real_policy, oblock, cblock) : -ENOENT;
}

static int _set_clear_dirty(struct dm_cache_policy *pe,
			     int (*fn)(struct dm_cache_policy*, dm_oblock_t),
			     dm_oblock_t oblock)
{
	int r;
	struct policy *p = to_policy(pe);

	if (p->real_policy) {
		r = fn(p->real_policy, oblock);
		if (r > 0) {
			int nr = atomic_read(&p->nr_dirty);

			if (fn == policy_set_dirty) {
				if (nr == from_cblock(p->cache_blocks))
					pr_alert("nr_dirty already max!\n");
				else
					atomic_inc(&p->nr_dirty);

			} else {
				if (nr)
					atomic_dec(&p->nr_dirty);
				else
					pr_alert("nr_dirty already 0!\n");
			}
		}

	} else
		r = -EOPNOTSUPP;

	return r;
}

static int background_set_dirty(struct dm_cache_policy *pe, dm_oblock_t oblock)
{
	return _set_clear_dirty(pe, policy_set_dirty, oblock);
}

static int background_clear_dirty(struct dm_cache_policy *pe, dm_oblock_t oblock)
{
	return _set_clear_dirty(pe, policy_clear_dirty, oblock);
}

static int background_load_mapping(struct dm_cache_policy *pe,
				   dm_oblock_t oblock, dm_cblock_t cblock,
				   void *hint, bool hint_valid)
{
	struct policy *p = to_policy(pe);

	return p->real_policy ? policy_load_mapping(p->real_policy, oblock, cblock, hint, hint_valid) :
				-EOPNOTSUPP;
}

static int background_walk_mappings(struct dm_cache_policy *pe, policy_walk_fn fn, void *context)
{
	struct policy *p = to_policy(pe);

	return p->real_policy ? policy_walk_mappings(p->real_policy, fn, context) : 0;
}

static void background_remove_mapping(struct dm_cache_policy *pe, dm_oblock_t oblock)
{
	struct policy *p = to_policy(pe);

	if (p->real_policy)
		policy_remove_mapping(p->real_policy, oblock);
}

static void background_force_mapping(struct dm_cache_policy *pe,
				     dm_oblock_t current_oblock, dm_oblock_t oblock)
{
	struct policy *p = to_policy(pe);

	if (p->real_policy)
		policy_force_mapping(p->real_policy, current_oblock, oblock);
}

static int background_writeback_work(struct dm_cache_policy *pe,
				     dm_oblock_t *oblock, dm_cblock_t *cblock)
{
	int r;
	struct policy *p = to_policy(pe);

	if (from_cblock(p->cache_blocks) - atomic_read(&p->nr_dirty) > from_cblock(p->threshold))
		return -ENOENT;

	r =  policy_next_dirty_block(p->real_policy, oblock, cblock);
	if (!r) {
		if (atomic_read(&p->nr_dirty))
			atomic_dec(&p->nr_dirty);
		else
			pr_alert("nr_dirty already 0!\n");
	}

	return r;
}

static dm_cblock_t background_residency(struct dm_cache_policy *pe)
{
	struct policy *p = to_policy(pe);

	return p->real_policy ? policy_residency(p->real_policy) : 0;
}

static void background_tick(struct dm_cache_policy *pe)
{
	policy_tick(to_policy(pe)->real_policy);
}

static const char *clean_block_str = "clean_block_pool_size";
static const char *policy_str = "policy";

static int background_emit_config_values(struct dm_cache_policy *pe, char *result, unsigned maxlen)
{
	ssize_t sz = 0;
	struct policy *p = to_policy(pe);

	DMEMIT("4 %s %u %s %s ",
	       clean_block_str,  p->threshold,
	       policy_str, dm_cache_policy_get_name(p->real_policy));

	return sz < maxlen ? policy_emit_config_values(to_policy(pe)->real_policy, result + sz, maxlen - sz) : 0;
}

static void init_policy_functions(struct policy *p, bool create);

static int background_set_config_value(struct dm_cache_policy *pe,
				       const char *key, const char *value)
{
	struct policy *p = to_policy(pe);

	if (!strcasecmp(key, clean_block_str)) {
		if (!strcmp(value, "-1"))
			p->threshold = p->cache_blocks;
		else {
			unsigned long tmp;

			if (kstrtoul(value, 10, &tmp) ||
			    tmp > from_cblock(p->cache_blocks))
				return -EINVAL;

			p->threshold = to_cblock(tmp);
		}

	} else if (!strcasecmp(key, policy_str)) {
		if (p->real_policy)
			return -EPERM;

		p->real_policy = dm_cache_policy_create(value, p->cache_blocks,
							p->origin_sectors, p->block_sectors);
		if (!p->real_policy)
			return -ENOMEM;

		init_policy_functions(p, false);

	} else
		return p->real_policy ? policy_set_config_value(p->real_policy, key, value) : -EINVAL;

	return 0;
}

/* Init the policy plugin interface function pointers. */
static void init_policy_functions(struct policy *p, bool create)
{
	if (create) {
		p->policy.destroy = background_destroy;
		p->policy.map = background_map;
		p->policy.lookup = background_lookup;
		p->policy.load_mapping = background_load_mapping;
		p->policy.next_dirty_block = NULL;
		p->policy.remove_mapping = background_remove_mapping;
		p->policy.force_mapping = background_force_mapping;
		p->policy.residency = background_residency;
		p->policy.set_config_value = background_set_config_value;

	} else {
		/* These have NULL checks in the interface inlines. */
		p->policy.set_dirty = background_set_dirty;
		p->policy.clear_dirty = background_clear_dirty;
		p->policy.walk_mappings = background_walk_mappings;
		p->policy.writeback_work = background_writeback_work;
		p->policy.tick = background_tick;
		p->policy.emit_config_values = background_emit_config_values;
	}
}

static struct dm_cache_policy *background_create(dm_cblock_t cache_blocks,
						 sector_t origin_sectors,
						 sector_t block_sectors)
{
	struct policy *p = kzalloc(sizeof(*p), GFP_KERNEL);

	if (!p)
		return NULL;

	init_policy_functions(p, true);
	p->threshold = 0;
	atomic_set(&p->nr_dirty, 0);

	p->cache_blocks = cache_blocks;

	/* Save for set_config_value() stacked policy creation. */
	p->origin_sectors = origin_sectors;
	p->block_sectors = block_sectors;

	return &p->policy;
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
