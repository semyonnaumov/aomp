package com.naumov.lock.theory;

import com.naumov.lock.Lock;
import com.naumov.thread.NumberedThreadAware;

/**
 * - Mutex
 * - NOT Deadlock-Free
 */
public class SecondLock extends NumberedThreadAware implements Lock {
    private volatile int victim; // have to be volatile to be consistent for both threads

    @Override
    public void lock() {
        victim = currentThreadId();

        // deadlocks here when
        //     1. There's no other threads to be the victim
        //     2. Other threads have finished and will not come to be the victim
        while (victim == currentThreadId()) {} // wait until other thread comes and gets the victim
    }

    @Override
    public void unlock() {
        // nothing to do here
    }
}
