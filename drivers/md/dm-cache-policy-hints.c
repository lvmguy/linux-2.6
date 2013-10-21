/*
 * Copyright (C) 2013 Red Hat. All rights reserved.
 *
 * This file is released under the GPL.
 *
 * TESTING! NOT FOR PRODUCTION USE!
 *
 * "hints" cache replacement policy to test variable hint size.
 */

#include "dm.h"
#include "dm-cache-policy.h"
#include "dm-cache-policy-internal.h"
#include "dm-cache-shim-utils.h"

#include <linux/hash.h>
#include <linux/list.h>
#include <linux/module.h>

#define DM_MSG_PREFIX "cache-policy-hints"

/*----------------------------------------------------------------*/

#define	DEFAULT_HINT_SIZE DM_CACHE_POLICY_MAX_HINT_SIZE

struct hints_policy {
	struct dm_cache_policy policy;

	void *hints_buffer;
	unsigned hint_counter[4];

	/* Flag to block (re)setting hint_size via the message interface */
	bool hint_size_set;
};

/*----------------------------------------------------------------------------*/
static struct hints_policy *to_policy(struct dm_cache_policy *ext)
{
	return container_of(ext, struct hints_policy, policy);
}

/*----------------------------------------------------------------*/

static void hints_destroy(struct dm_cache_policy *ext)
{
	struct hints_policy *p = to_policy(ext);

	kfree(p);
}

/*----------------------------------------------------------------------------*/

/* Hints endianess conversions */
#define __le8 uint8_t
struct hints_ptrs {
	__le64 *le64_hints;
	__le32 *le32_hints;
	__le16 *le16_hints;
	__le8  *le8_hints;

	uint64_t *u64_hints;
	uint32_t *u32_hints;
	uint16_t *u16_hints;
	uint8_t  *u8_hints;
};

typedef int (*hints_xfer_fn_t) (struct hints_ptrs*, unsigned, unsigned, bool);

#define cpu_to_le8(x) (x)
#define le8_to_cpu(x) (x)

#define HINTS_XFER(width) \
static int hints_ ## width ## _xfer(struct hints_ptrs *p, unsigned idx, unsigned val, bool to_disk) \
{ \
	if (to_disk) \
		p->le ## width ## _hints[idx] = cpu_to_le ## width(val); \
\
	else { \
		p->u ## width ## _hints[idx] = le ## width ## _to_cpu(p->le ## width ## _hints[idx]); \
		if (p->u ## width ## _hints[idx] != val) { \
			DMERR_LIMIT("%s -- hint value %llu != %u", __func__, \
				    (long long unsigned) p->u ## width ## _hints[idx], val); \
			return -EINVAL; \
		} \
	} \
\
	return 0; \
}

HINTS_XFER(64)
HINTS_XFER(32)
HINTS_XFER(16)
HINTS_XFER(8)

static void calc_hint_value_counters(struct hints_policy *p)
{
	unsigned div, rest = dm_cache_policy_get_hint_size(&p->policy), u;

	for (u = 3, div = sizeof(uint64_t); rest; u--, div >>= 1) {
		p->hint_counter[u] = rest / div;
		rest -= p->hint_counter[u] * div;
	}
}

/* Macro to set hint ptr for width on LHS based on RHS width<<1 */
#define PTR_INC(lhs, rhs, c) \
	inc = 2 * p->hint_counter[c]; \
	ptrs->le ## lhs ## _hints = (__le ## lhs  *) ptrs->le ## rhs ## _hints + inc; \
	ptrs->u ## lhs ## _hints  = (uint ## lhs ## _t *) ptrs->u ## rhs ## _hints  + inc;

static void set_hints_ptrs(struct hints_policy *p, struct hints_ptrs *ptrs)
{
	unsigned inc;

	ptrs->le64_hints = p->hints_buffer;
	ptrs->u64_hints  = p->hints_buffer;

	PTR_INC(32, 64, 3)
	PTR_INC(16, 32, 2)
	PTR_INC(8,  16, 1)
}

static void __hints_xfer_disk(struct hints_policy *p, bool to_disk)
{
	unsigned idx, u, val;
	hints_xfer_fn_t hints_xfer_fns[] = {
		hints_8_xfer,
		hints_16_xfer,
		hints_32_xfer,
		hints_64_xfer
	};

	struct hints_ptrs hints_ptrs;

	smp_rmb();
	if (!p->hint_size_set) {
		calc_hint_value_counters(p);
		p->hint_size_set = true;
	}

	/* Must happen after calc_hint_value_counters()! */
	set_hints_ptrs(p, &hints_ptrs);

	val = 1;
	u = ARRAY_SIZE(hints_xfer_fns);
	while (u--) {
		for (idx = 0; idx < p->hint_counter[u]; idx++) {
			/*
			 * val only suitable because of 128 hint size limitation.
			 *
			 * An uint8_t maxes at 255, so we could theoretically
			 * test hint sizes up to 2023 bytes with this limitation.
			 */
			if (hints_xfer_fns[u](&hints_ptrs, idx, val, to_disk))
				return;

			val++;
		}
	}

	return;
}

static void hints_preset_and_to_disk(struct hints_policy *p)
{
	__hints_xfer_disk(p, true);
}

static void hints_from_disk_and_check(struct hints_policy *p)
{
	__hints_xfer_disk(p, false);
}

static int hints_load_mapping(struct dm_cache_policy *ext,
			      dm_oblock_t oblock, dm_cblock_t cblock,
			      void *hint, bool hint_valid)
{
	struct hints_policy *p = to_policy(ext);
	int r = policy_load_mapping(ext->child, oblock, cblock, hint + dm_cache_policy_get_hint_size(ext), hint_valid);

	if (!r && hint_valid) {
		void *tmp = p->hints_buffer;

		p->hints_buffer = hint;
		hints_from_disk_and_check(p);
		p->hints_buffer = tmp;

	} else
		DMWARN_LIMIT("hints for cblock=%u/oblock=%llu invalid",
			     from_cblock(cblock), from_oblock(oblock));

	return 0;
}

/* shim callback. */
static void *hints_buffer_to_hint(struct shim_walk_map_ctx *ctx,
				  dm_cblock_t cblock, dm_oblock_t oblock)
{
	struct hints_policy *p = to_policy(ctx->my_policy);

	hints_preset_and_to_disk(p);
	return p->hints_buffer;
}

/* Walk mappings */
static int hints_walk_mappings(struct dm_cache_policy *ext, policy_walk_fn fn, void *context)
{
	return dm_cache_shim_utils_walk_map(ext, fn, context, hints_buffer_to_hint);
}

/* Set config values. */
static int hints_set_config_value(struct dm_cache_policy *ext,
				  const char *key, const char *value)
{
	if (!strcasecmp(key, "hint_size")) {
		struct hints_policy *p = to_policy(ext);

		if (p->hint_size_set)
			return -EPERM;

		else {
			unsigned tmp;

			if (kstrtou32(value, 10, &tmp))
				return -EINVAL;

			else {
				int r = dm_cache_policy_set_hint_size(ext, tmp);

				if (!r) {
					calc_hint_value_counters(p);
					p->hint_size_set = true;
					smp_wmb();
				}

				return r;
			}
		}
	}

	return policy_set_config_value(ext->child, key, value);
}

/* Emit config values. */
static int hints_emit_config_values(struct dm_cache_policy *ext, char *result, unsigned maxlen)
{
	ssize_t sz = 0;

	DMEMIT("2 hint_size %llu", (long long unsigned) dm_cache_policy_get_hint_size(ext));
	return policy_emit_config_values(ext->child, result + sz, maxlen - sz);
}

static void init_policy_functions(struct hints_policy *p)
{
	dm_cache_shim_utils_init_shim_policy(&p->policy);
	p->policy.destroy = hints_destroy;
	p->policy.walk_mappings = hints_walk_mappings;
	p->policy.load_mapping = hints_load_mapping;
	p->policy.emit_config_values = hints_emit_config_values;
	p->policy.set_config_value = hints_set_config_value;
}

static struct dm_cache_policy *hints_policy_create(dm_cblock_t cache_size,
						   sector_t origin_size,
						   sector_t block_size)
{
	int r;
	struct hints_policy *p;

	BUILD_BUG_ON(DEFAULT_HINT_SIZE > 2023);

	p = kzalloc(sizeof(*p), GFP_KERNEL);
	if (!p)
		return NULL;

	init_policy_functions(p);
	return &p->policy;
}

/*----------------------------------------------------------------------------*/
static struct dm_cache_policy_type hints_policy_type = {
	.name = "hints",
	.version = {1, 0, 0},
	.hint_size = DEFAULT_HINT_SIZE,
	.owner = THIS_MODULE,
	.create = hints_policy_create,
	.shim = true /* FIXME: bit field */
};

static int __init hints_init(void)
{
	int r = dm_cache_policy_register(&hints_policy_type);

	if (!r)
		DMINFO("version %u.%u.%u loaded",
		       hints_policy_type.version[0],
		       hints_policy_type.version[1],
		       hints_policy_type.version[2]);

	return r;
}

static void __exit hints_exit(void)
{
	dm_cache_policy_unregister(&hints_policy_type);
}

module_init(hints_init);
module_exit(hints_exit);

MODULE_AUTHOR("Heinz Mauelshagen <dm-devel@redhat.com>");
MODULE_LICENSE("GPL");
MODULE_DESCRIPTION("hint size test cache policy");
