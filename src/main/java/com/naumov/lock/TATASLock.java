package com.naumov.lock;

import com.naumov.thread.NumberedThreadAware;

import java.util.concurrent.atomic.AtomicBoolean;

/**
 * - Mutex
 * - Deadlock-Free
 * - O(1) space for N threads
 * - не так плох, как TAS, но все еще далек от идеала
 */
public class TATASLock extends NumberedThreadAware implements Lock {
    private final AtomicBoolean atomicBoolean = new AtomicBoolean();

    @Override
    public void lock() {
        while (true) {
            while (atomicBoolean.get()) {
            }

            if (atomicBoolean.getAndSet(true)) return; // acquired lock
        }
    }

    @Override
    public void unlock() {
        atomicBoolean.set(false);
    }
}