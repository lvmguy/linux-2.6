/*
 i Copyright (C) 2013 Red Hat. All rights reserved.
 *
 * Shim "background" write cache replacement policy module.
 *
 * Confgure on top of any policy supporting the writeback_work method.
 *
 * This file is released under the GPL.
 */

#include "dm-cache-policy.h"
#include "dm-cache-policy-internal.h"
#include "dm-cache-shim-utils.h"
#include "dm.h"

#include <linux/module.h>
#include <linux/moduleparam.h>

#define DM_MSG_PREFIX	"cache-policy-background" 

#define	DEFAULT_CLEAN_POOL_SIZE	100

/*----------------------------------------------------------------*/

struct background_policy {
	struct dm_cache_policy policy;

	dm_cblock_t cache_size;

	unsigned clean_pool_size;
	atomic_t dirty_cblocks;
};

/*----------------------------------------------------------------------------*/
static struct background_policy *to_bg_policy(struct dm_cache_policy *p)
{
	return container_of(p, struct background_policy, policy);
}

/*----------------------------------------------------------------------------*/

/* Public interface (see dm-cache-policy.h */
static void background_destroy(struct dm_cache_policy *p)
{
	struct background_policy *bg = to_bg_policy(p);

	kfree(bg);
}

static int background_set_dirty(struct dm_cache_policy *p, dm_oblock_t oblock)
{
	struct background_policy *bg = to_bg_policy(p);
	int r = policy_set_dirty(p->child, oblock);

	if (!r) /* 0 -> policy has set block to dirty. */
		atomic_inc(&bg->dirty_cblocks);

	return r;
}

static int background_clear_dirty(struct dm_cache_policy *p, dm_oblock_t oblock)
{
	struct background_policy *bg = to_bg_policy(p);
	int r = policy_clear_dirty(p->child, oblock);

	if (!r) { /* 0 -> policy has set block to clean. */
		BUG_ON(!atomic_read(&bg->dirty_cblocks));
		atomic_dec(&bg->dirty_cblocks);
	}

	return r;
}

static void background_force_mapping(struct dm_cache_policy *p,
				     dm_oblock_t current_oblock, dm_oblock_t new_oblock)
{
	struct background_policy *bg = to_bg_policy(p);

	policy_force_mapping(p->child, current_oblock, new_oblock);
	atomic_inc(&bg->dirty_cblocks);
}

static int background_writeback_work(struct dm_cache_policy *p,
				     dm_oblock_t *oblock, dm_cblock_t *cblock)
{
	int r;
	struct background_policy *bg = to_bg_policy(p);

	smp_rmb();
	if (from_cblock(bg->cache_size) - atomic_read(&bg->dirty_cblocks) < bg->clean_pool_size) {
		r = policy_writeback_work(p->child, oblock, cblock);
		if (!r)
			atomic_dec(&bg->dirty_cblocks);

	} else
		r = -ENODATA;

	return r;
}

static const char *clean_block_str = "clean_block_pool_size";

static int background_emit_config_values(struct dm_cache_policy *p, char *result, unsigned maxlen)
{
	ssize_t sz = 0;
	struct background_policy *bg = to_bg_policy(p);

	/* FIXME: REMOVEME: 3rd config value 'dirty_cblocks'. */
	DMEMIT("2 %s %u *%d* ", clean_block_str, bg->clean_pool_size, atomic_read(&bg->dirty_cblocks));

	return sz < maxlen ? policy_emit_config_values(p->child, result + sz, maxlen - sz) : 0;
}

static int background_set_config_value(struct dm_cache_policy *p,
				       const char *key, const char *value)
{
	struct background_policy *bg = to_bg_policy(p);

	if (!strcasecmp(key, clean_block_str)) {
		unsigned long tmp;

		if (!strcasecmp(value, "max"))
			tmp = from_cblock(bg->cache_size);

		else if (kstrtoul(value, 10, &tmp) ||
		    tmp > from_cblock(bg->cache_size))
			return -EINVAL;

		bg->clean_pool_size = tmp;
		smp_wmb();

	} else
		return policy_set_config_value(p->child, key, value);

	return 0;
}

/* Init the policy plugin interface function pointers. */
static void init_policy_functions(struct background_policy *bg)
{
	dm_cache_shim_utils_init_shim_policy(&bg->policy);
	bg->policy.destroy = background_destroy;
	bg->policy.set_dirty = background_set_dirty;
	bg->policy.clear_dirty = background_clear_dirty;
	bg->policy.force_mapping = background_force_mapping;
	bg->policy.writeback_work = background_writeback_work;
	bg->policy.emit_config_values = background_emit_config_values;
	bg->policy.set_config_value = background_set_config_value;
}

static struct dm_cache_policy *background_create(dm_cblock_t cache_size,
						 sector_t origin_sectors,
						 sector_t block_sectors)
{
	struct background_policy *bg = kzalloc(sizeof(*bg), GFP_KERNEL);
	unsigned cps;

	if (!bg)
		return NULL;

	init_policy_functions(bg);
	bg->cache_size = cache_size;
	cps = from_cblock(cache_size) / 4;
	bg->clean_pool_size = cps < DEFAULT_CLEAN_POOL_SIZE ? cps : DEFAULT_CLEAN_POOL_SIZE;
	atomic_set(&bg->dirty_cblocks, 0);

	return &bg->policy;
}

/*----------------------------------------------------------------------------*/

static struct dm_cache_policy_type bg_policy_type = {
	.name = "bg",
	.version = {1, 0, 0},
	.hint_size = 0,
	.owner = THIS_MODULE,
        .create = background_create,
	.features = DM_CACHE_POLICY_SHIM
};

static struct dm_cache_policy_type background_policy_type = {
	.name = "background",
	.version = {1, 0, 0},
	.hint_size = 0,
	.owner = THIS_MODULE,
        .create = background_create,
	.features = DM_CACHE_POLICY_SHIM
};

static int __init background_init(void)
{
	struct dm_cache_policy_type *t = &bg_policy_type;
	int r = dm_cache_policy_register(t);

	if (r)
		goto err;

	t = &background_policy_type;
	r = dm_cache_policy_register(t);
	if (r)
		goto err_unregister_bg;

	DMINFO("version %u.%u.%u loaded",
	       background_policy_type.version[0],
	       background_policy_type.version[1],
	       background_policy_type.version[2]);

	return 0;

err_unregister_bg:
	dm_cache_policy_unregister(&bg_policy_type);
err:
	DMERR("register failed %d as '%s'", r, t->name);
	return r;
}

static void __exit background_exit(void)
{
	dm_cache_policy_unregister(&background_policy_type);
	dm_cache_policy_unregister(&bg_policy_type);
}

module_init(background_init);
module_exit(background_exit);

MODULE_AUTHOR("Heinz Mauelshagen");
MODULE_LICENSE("GPL");
MODULE_DESCRIPTION("background write cache policy shim");

MODULE_ALIAS("dm-cache-bg");
/*----------------------------------------------------------------------------*/
