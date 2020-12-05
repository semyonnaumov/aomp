package com.naumov.lock;

import com.naumov.thread.ThreadIdAware;

/**
 * It is a mutex, but it is not deadlock-free
 * Лочится, когда оба потока ставят себе true, при этом ни один не успевает добраться до проверки цикла
 */
public class FirstLock extends ThreadIdAware implements Lock {
    private final boolean[] interestedThreads = new boolean[2];

    @Override
    public void lock() {
        int me = currentThreadId();
        int other = 1 - currentThreadId();
        interestedThreads[me] = true;

        // deadlocks here when
        //     write_0(interestedThreads[0] = true) -> write_1(interestedThreads[1] = true) -> read_0(interestedThreads[1] == true)
        //     and
        //     write_0(interestedThreads[0] = true) -> write_1(interestedThreads[1] = true) -> read_1(interestedThreads[0] == true)
        while (interestedThreads[other]) {}  // wait until other thread releases the lock
    }

    @Override
    public void unlock() {
        interestedThreads[currentThreadId()] = false;
    }
}
