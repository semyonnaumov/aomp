package com.naumov.lock.queue;

import com.naumov.lock.Lock;

import java.util.concurrent.atomic.AtomicInteger;

/**
 * - Mutex
 * - Deadlock-Free
 * - Starvation-Free
 * - First-Come-First-Served
 * - лучше BackoffLock, не простаивает по времени, но жрет лишнюю память и нужно знать кол-во потоков
 * - Can overflow?!
 */
public class AndersonLock implements Lock {
    private final ThreadLocal<Integer> mySlotIndex = ThreadLocal.withInitial(() -> 0);
    private final AtomicInteger tail;
    private volatile boolean[] flag; // volatile to disable Java optimizations
    private final int size;

    public AndersonLock(int capacity) {
        this.size = capacity;
        this.tail = new AtomicInteger(0);
        flag = new boolean[capacity];
        flag[0] = true;
    }

    @Override
    public void lock() {
        int slot = tail.getAndIncrement() % size; // may overflow???
        mySlotIndex.set(slot);

        // spin "locally"
        while (!flag[slot]) {
        }
    }

    @Override
    public void unlock() {
        int slot = mySlotIndex.get();
        flag[slot] = false; // release my slot

        flag[(slot + 1) % size] = true; // notify next thread
    }
}
