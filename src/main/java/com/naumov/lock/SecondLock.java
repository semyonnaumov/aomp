package com.naumov.lock;

import com.naumov.thread.ThreadIdAware;

/**
 * It is a mutex, but it is not deadlock-free
 * Лочится когда исполнение становится однопоточным: когда один поток закончил выполнение, второй сразу повисает
 */
public class SecondLock extends ThreadIdAware implements Lock {
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
