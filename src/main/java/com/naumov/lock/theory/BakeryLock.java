package com.naumov.lock.theory;

import com.naumov.lock.Lock;
import com.naumov.thread.NumberedThreadAware;

import java.util.Arrays;

/**
 * - Mutex
 * - Deadlock-Free
 * - Starvation-Free
 * - First-Come-First-Served
 *
 * Can overflow!!!
 */
public class BakeryLock extends NumberedThreadAware implements Lock {
    private final int numberOfThreads;
    private final boolean[] interestedThreads;
    private final long[] label;

    public BakeryLock(int numberOfThreads) {
        this.numberOfThreads = numberOfThreads;
        this.interestedThreads = new boolean[numberOfThreads]; // initially all = false
        this.label = new long[numberOfThreads]; // initially all = 0
    }

    @Override
    public void lock() {
        int me = currentThreadId();

        interestedThreads[me] = true;
        label[me] = Arrays.stream(label)
                .max()
                .orElseThrow(() -> new IllegalStateException("Wrong label.")) + 1;
        System.out.println(printLogPrefix() + "curr max = " + label[me]);

        // spin while conflicts exist
        while (cannotGoFurther(me)) {}
    }

    private boolean cannotGoFurther(int me) {
        for (int other = 0; other < numberOfThreads; other++) {
            if (other != me && interestedThreads[other]
                    && (label[other] < label[me] || (label[other] == label[me] && other < me))) return true;
        }
        return false;
    }

    @Override
    public void unlock() {
        interestedThreads[currentThreadId()] = false;
    }
}
