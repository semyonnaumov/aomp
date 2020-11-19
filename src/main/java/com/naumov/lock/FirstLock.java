package com.naumov.lock;

import static com.naumov.thread.NumberedThread.currentThreadId;

/**
 * It is a mutex, but it is not deadlock-free
 * Лочится, когда оба потока ставят себе true, при этом ни один не успевает добраться до проверки цикла
 */
public class FirstLock implements Lock {
    private final boolean[] interestedThreads = new boolean[2];

    @Override
    public void lock() {
        int me = currentThreadId();
        int other = 1 - currentThreadId();
        interestedThreads[me] = true;

        // wait until other thread releases the lock
        while (interestedThreads[other]) {}
    }

    @Override
    public void unlock() {
        interestedThreads[currentThreadId()] = false;
    }
}
