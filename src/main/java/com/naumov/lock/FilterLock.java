package com.naumov.lock;

import static com.naumov.thread.NumberedThread.currentThreadId;

public class FilterLock implements Lock {
    private final int numberOfThreads;
    private final int[] level;
    private final int[] victim;

    public FilterLock(int numberOfThreads) {
        this.numberOfThreads = numberOfThreads;
        this.level = new int[numberOfThreads];
        this.victim = new int[numberOfThreads];
    }

    @Override
    public void lock() {
        int me = currentThreadId();

        // traverse levels
        for (int myLevel = 1; myLevel < numberOfThreads; myLevel++) {
            this.level[me] = myLevel;
            victim[myLevel] = me;

            // spin while conflicts exist
            while (cannotGoFurther(me, myLevel)) {}
        }

    }

    @Override
    public void unlock() {
        level[currentThreadId()] = 0; // I quit filter
    }

    private boolean cannotGoFurther(int me, int myLevel) {
        for (int other = 0; other < numberOfThreads; other++) {
            if (other != me && level[other] >= myLevel && victim[myLevel] == me) return true;
        }
        return false;
    }
}
