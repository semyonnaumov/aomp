package com.naumov.lock;

import static com.naumov.thread.NumberedThread.currentThreadId;

/**
 * It is a mutex, but it is not deadlock-free
 * Лочится, когда оба потока ставят себе true, при этом ни один не успевает добраться до проверки цикла
 */
public class FirstLock implements Lock {
    private final boolean[] flags = new boolean[2];

    @Override
    public void lock() {
        flags[currentThreadId()] = true;

        // wait until other thread releases the lock
        while (flags[1 - currentThreadId()]) {}
    }

    @Override
    public void unlock() {
        flags[currentThreadId()] = false;
    }
}
