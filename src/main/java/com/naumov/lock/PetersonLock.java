package com.naumov.lock;

import com.naumov.thread.NumberedThreadAware;

/**
 * It is a mutex, deadlock-free, starvation-free
 */
public class PetersonLock extends NumberedThreadAware implements Lock {
    private final boolean[] interestedThreads = new boolean[2];
    private volatile int victim; // have to be volatile to be consistent for both threads

    @Override
    public void lock() {
        int me = currentThreadId();
        int other = 1 - currentThreadId();

        interestedThreads[me] = true; // I'm interested
        victim = me; // you go first

        // wait
        while (interestedThreads[other] && victim == me) {}
    }

    @Override
    public void unlock() {
        interestedThreads[currentThreadId()] = false; // I'm not interested
    }
}
