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

static void perform_tests(const char *caller)
{
	DMINFO("%s - *** performing tests %u times ***", caller, amount);
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
