package com.naumov.lock.backoff;

import com.naumov.lock.Lock;

import java.util.concurrent.atomic.AtomicBoolean;

/**
 * - Mutex
 * - Deadlock-Free
 * - O(1) space for N threads
 * - лучше TATAS, так как гораздо меньше contention
 */
public class BackoffLock implements Lock {
    private static final int MIN_TIMEOUT = 1, MAX_TIMEOUT = 1000;
    private final AtomicBoolean atomicBoolean = new AtomicBoolean(false);

    @Override
    public void lock() {
        Backoff backoff = new Backoff(MIN_TIMEOUT, MAX_TIMEOUT);

        while (true) {
            while (atomicBoolean.get()) {
            }

            if (!atomicBoolean.getAndSet(true)) {
                return; // acquired lock
            } else {
                backoff.backoff();
            }
        }
    }

    @Override
    public void unlock() {
        atomicBoolean.set(false);
    }
}
