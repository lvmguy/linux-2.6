/*
 * Copyright 2013 Red Hat, Inc. All Rights Reserved
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Gentrcl Public License as published by the
 * Free Software Foundation; either version 2 of the License, or (at your
 * option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Gentrcl Public License
 * for more details
 *
 */

#include "dm.h"

#include <linux/random.h>
#include <linux/kernel.h>
#include <linux/module.h>

#define DM_MSG_PREFIX "cache-timing-tests"

static unsigned amount = 10000000;
static DEFINE_SPINLOCK(spinlock);
static DEFINE_MUTEX(mutex);
static DEFINE_SEMAPHORE(worker_sem);
static DEFINE_SEMAPHORE(sem);
static DECLARE_RWSEM(rwsem);
static struct workqueue_struct *wq = NULL;
static struct work_struct worker1, worker2;

static void enforce_local(void)
{
	preempt_disable();
	local_irq_disable();
}

static void disable_local(void)
{
	local_irq_enable();
	preempt_enable();
}

static void __tst_func(void)
{
	return;
}

static void (*f)(void) = __tst_func;
static struct bio global_bio;

static unsigned long test_spin_lock(unsigned c)
{
	unsigned v;
	unsigned long start;

	start = jiffies;
	while (c--) {
		spin_lock(&spinlock);
		v = c;
		spin_unlock(&spinlock);
	}

	return jiffies - start;
}

static unsigned long test_spin_lock_irq(unsigned c)
{
	unsigned v;
	unsigned long start;

	start = jiffies;
	while (c--) {
		spin_lock_irq(&spinlock);
		v = c;
		spin_unlock_irq(&spinlock);
	}

	return jiffies - start;
}

static unsigned long test_spin_lock_irqsave(unsigned c)
{
	unsigned v;
	unsigned long flags, start;

	/* spin_lock() */
	start = jiffies;
	while (c--) {
		spin_lock_irqsave(&spinlock, flags);
		v = c;
		spin_unlock_irqrestore(&spinlock, flags);
	}

	return jiffies - start;
}

static unsigned long test_mutex_lock(unsigned c)
{
	unsigned v;
	unsigned long start;

	start = jiffies;
	while (c--) {
		mutex_lock(&mutex);
		v = c;
		mutex_unlock(&mutex);
	}

	return jiffies - start;
}

static unsigned long test_down(unsigned c)
{
	unsigned v;
	unsigned long start;

	start = jiffies;
	while (c--) {
		down(&sem);
		v = c;
		up(&sem);
	}

	return jiffies - start;
}

static unsigned long test_down_read(unsigned c)
{
	unsigned v;
	unsigned long start;

	start = jiffies;
	while (c--) {
		down_read(&rwsem);
		v = c;
		up_read(&rwsem);
	}

	return jiffies - start;
}

static unsigned long test_down_write(unsigned c)
{
	unsigned v;
	unsigned long start;

	start = jiffies;
	while (c--) {
		down_write(&rwsem);
		v = c;
		up_write(&rwsem);
	}

	return jiffies - start;
}

static unsigned long test_smp_wmb(unsigned c)
{
	unsigned v;
	unsigned long start;

	start = jiffies;
	while (c--) {
		smp_rmb();
		v = c;
		smp_wmb();
	}

	return jiffies - start;
}

static unsigned long test_function_pointer_call_ext(unsigned c)
{
	unsigned long r, start;

	enforce_local();

	start = jiffies;
	while (c--)
		f();

	r = jiffies - start;

	disable_local();

	return r;
}

static unsigned long test_function_pointer_call_int(unsigned c)
{
	unsigned long r, start;
	void (*f)(void) = __tst_func;

	enforce_local();

	start = jiffies;
	while (c--)
		f();

	r = jiffies - start;

	disable_local();

	return r;
}

static unsigned long test_function_call(unsigned c)
{
	unsigned long r, start = jiffies;

	enforce_local();

	while (c--)
		__tst_func();

	r = jiffies - start;

	disable_local();

	return r;
}

struct cache {
	unsigned sectors_per_block_shift;
};

static struct cache cache = {
	.sectors_per_block_shift = -1,
};

static bool block_size_is_power_of_two(struct cache *cache)
{
	return cache->sectors_per_block_shift >= 0;
}

static unsigned long test_conditional(unsigned c)
{
	unsigned long start, r;
	struct bio *bio = &global_bio;

	enforce_local();

	start = jiffies;
	while (c--) {
		if (block_size_is_power_of_two(&cache))
			bio->bi_sector = 0;
		else
			bio->bi_sector = 1;
	}

	r = jiffies - start;

	disable_local();

	return r;
}

static const unsigned long m1 = 0x9e37fffffffc0001UL;
static const unsigned bits = 18U;

/* Joe's 1st hash function. */
static uint64_t hash1(uint32_t b)
{
	// return (ffs(b) << m1) >> bits;
	return (b * m1) >> bits;
}

/* Joe's 2nd hash function. */
static uint64_t hash2(uint32_t b)
{
	uint32_t n = b;

	n = n ^ (n >> 16);
	n = n * 0x85ebca6bu;
	n = n ^ (n >> 13);
	n = n * 0xc2b2ae35u;
	n = n ^ (n >> 16);

	return n;
}

/* Bloom fnv */
static uint64_t hash3(uint32_t b)
{
	uint64_t n = 0xcbf29ce484222325ULL;
	const uint64_t magic_prime = 0x00000100000001b3ULL;
 
	const uint8_t *p = (uint8_t*) &b, *end = p + 4;

	while (p < end)
		n = (n ^ *(p++)) * magic_prime;
#if 0
		n ^= *(p++), n *= magic_prime;
#endif

	return n;
}

/* 64 bit Murmur 3 */
static uint64_t hash4(uint64_t b)
{
	uint64_t n = b;

	n ^= n >> 33;
	n *= 0xff51afd7ed558ccdUL;
	n ^= n >> 33;
	n *= 0xc4ceb9fe1a85ec53UL;
	n ^= n >> 33;

	return n;
}


static unsigned long test_joes_bloom_hash1(unsigned c)
{
	unsigned long start, r;
	uint64_t bs = 0;
	unsigned long *pbs = (unsigned long *) &bs;

	enforce_local();

	start = jiffies;
	while (c--)
		set_bit(hash1(64) & 0x0F, pbs);

	r = jiffies - start;

	disable_local();

	return r;
}

static unsigned long test_joes_bloom_hash2(unsigned c)
{
	unsigned long start, r;
	uint64_t bs = 0;
	unsigned long *pbs = (unsigned long *) &bs;

	enforce_local();

	start = jiffies;
	while (c--)
		set_bit(hash2(64) & 0x0F, pbs);

	r = jiffies - start;

	disable_local();

	return r;
}

static unsigned long test_joes_bloom_hash1and2(unsigned c)
{
	unsigned long start, r;
	uint64_t bs = 0;
	unsigned long *pbs = (unsigned long *) &bs;

	enforce_local();

	start = jiffies;
	while (c--) {
		set_bit(hash1(64) & 0x0F, pbs);
		set_bit(hash2(64) & 0x0F, pbs);
	}

	r = jiffies - start;

	disable_local();

	return r;
}

static unsigned long test_bloom_fnv_hash(unsigned c)
{
	unsigned long start, r;
	uint64_t bs = 0;
	unsigned long *pbs = (unsigned long *) &bs;

	enforce_local();

	start = jiffies;
	while (c--)
		set_bit(hash3(64) & 0x0F, pbs);

	r = jiffies - start;

	disable_local();

	return r;
}

static unsigned long test_64bit_murmur3(unsigned c)
{
	unsigned long start, r;
	uint64_t bs = 0;
	unsigned long *pbs = (unsigned long *) &bs;

	enforce_local();

	start = jiffies;
	while (c--)
		set_bit(hash4(64) & 0x0F, pbs);

	r = jiffies - start;

	disable_local();

	return r;
}

static unsigned long test_512m_array_linear(unsigned c)
{
	unsigned long start, r;
	uint32_t *a;
	const unsigned m = 512 * 1024 * 1024 / sizeof(*a);
	unsigned i = m;

	a = vmalloc(sizeof(*a) * m);
	if (!a)
		return ~0UL;

	enforce_local();

	start = jiffies;
	while (c--) {
		i--;
		a[i] = i;

		if (unlikely(!i))
			i = m;
	}

	r = jiffies - start;

	disable_local();

	vfree(a);

	return r;
}

static unsigned long test_512m_array_random(unsigned c)
{
	unsigned long start, r;
	uint32_t *a;
	const unsigned m = 512 * 1024 * 1024 / sizeof(*a);
	unsigned i = m, end = m - 1;

	a = vmalloc(sizeof(*a) * m);
	if (!a)
		return ~0UL;

	enforce_local();

	start = jiffies;
	while (c--) {
		i = min(end, prandom_u32());
		a[i] = i;
	}

	r = jiffies - start;

	disable_local();

	vfree(a);

	return r;
}

static void perform_tests(const char *caller)
{
	DMINFO("%s - *** performing tests %u times ***", caller, amount);
	DMINFO("%s - functon call()=%lu jiffies", caller, test_function_call(amount * 10));
	DMINFO("%s - functon pointer call with internal pointer()=%lu jiffies", caller, test_function_pointer_call_int(amount * 10));
	DMINFO("%s - functon pointer call with external pointer()=%lu jiffies", caller, test_function_pointer_call_ext(amount * 10));
	DMINFO("%s - conditional=%lu jiffies", caller, test_conditional(amount * 10));
	amount *= 10;
	DMINFO("%s - *** performing tests %u times ***", caller, amount);
	DMINFO("%s - Joe's bloom hash1=%lu jiffies", caller, test_joes_bloom_hash1(amount));
	DMINFO("%s - Joe's bloom hash2=%lu jiffies", caller, test_joes_bloom_hash2(amount));
	DMINFO("%s - Joe's bloom hash1and2=%lu jiffies", caller, test_joes_bloom_hash1and2(amount));
	DMINFO("%s - 64bit Murmur 3 hash=%lu jiffies", caller, test_64bit_murmur3(amount));
	DMINFO("%s - bloom fnv hash=%lu jiffies", caller, test_bloom_fnv_hash(amount));
	DMINFO("%s - 512MB array linear access=%lu jiffies", caller, test_512m_array_linear(amount));
	DMINFO("%s - 512MB array random access=%lu jiffies", caller, test_512m_array_random(amount));
return; 
	DMINFO("%s - spin_lock()=%lu jiffies", caller,  test_spin_lock(amount));
	DMINFO("%s - spin_lock_irq()=%lu jiffies", caller, test_spin_lock_irq(amount));
	DMINFO("%s - spin_lock_irqsave()=%lu jiffies", caller, test_spin_lock_irqsave(amount));
	DMINFO("%s - mutex_lock()=%lu jiffies", caller, test_mutex_lock(amount));
	DMINFO("%s - down()=%lu jiffies", caller, test_down(amount));
	DMINFO("%s - down_read()=%lu jiffies", caller, test_down_read(amount));
	DMINFO("%s - down_write()=%lu jiffies", caller, test_down_write(amount));
	DMINFO("%s - smp_wmb()=%lu jiffies", caller, test_smp_wmb(amount));
}

static void do_work(struct work_struct *ws)
{
	char caller[128];

	sprintf(caller, "worker%u (in parallel with worker%u)", ws == &worker1 ? 1 : 2, ws == &worker1 ? 2 : 1);
	down(&worker_sem);
	perform_tests(caller);
	up(&worker_sem);
	
}

static int __init timing_tests_init(void)
{
	wq = alloc_workqueue("dm-" DM_MSG_PREFIX, WQ_UNBOUND, 2);
	if (!wq) {
		DMERR("could not create workqueue");
		return -ENOMEM;
	}

	DMINFO("%s - --> starting tests <--", __func__);
	smp_wmb();
	perform_tests("init (standalone)");
return 0;
	INIT_WORK(&worker1, do_work);
	INIT_WORK(&worker2, do_work);
	smp_wmb();
	down(&worker_sem);
	queue_work(wq, &worker1);
	queue_work(wq, &worker2);
	up(&worker_sem);
	up(&worker_sem);
	return 0;
}

static void __exit timing_tests_exit(void)
{
	destroy_workqueue(wq);
}

module_init(timing_tests_init);
module_exit(timing_tests_exit);

MODULE_AUTHOR("Heinz Mauelshagen <dm-devel@redhat.com>");
MODULE_LICENSE("GPL");
MODULE_DESCRIPTION("lock timing tests module");
