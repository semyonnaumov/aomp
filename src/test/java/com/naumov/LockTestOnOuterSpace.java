package com.naumov;

import com.naumov.cs.space.OuterSpace;
import com.naumov.lock.backoff.BackoffLock;
import com.naumov.lock.queue.AndersonLock;
import com.naumov.lock.tas.TASLock;
import com.naumov.lock.tas.TATASLock;
import com.naumov.lock.theory.*;
import com.naumov.thread.NumberedThread;
import com.naumov.thread.NumberedThreadAware;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

class LockTestOnOuterSpace extends NumberedThreadAware {

    @Test
    public void testFirstLock() {
        OuterSpace outerSpace = new OuterSpace(new FirstLock());
        // deadlocks
        runSpaceWalks(outerSpace, 2, 10);
    }

    @Test
    public void testSecondLock() {
        OuterSpace outerSpace = new OuterSpace(new SecondLock());
        // deadlocks
        runSpaceWalks(outerSpace, 2, 10);
    }

    @Test
    public void testPetersonLock() {
        OuterSpace outerSpace = new OuterSpace(new PetersonLock());
        runSpaceWalks(outerSpace, 2, 10);
    }

    @Test
    public void testFilterLock() {
        int threadNumber = 5;
        OuterSpace outerSpace = new OuterSpace(new FilterLock(threadNumber));
        runSpaceWalks(outerSpace, threadNumber, 10);
    }

    @Test
    public void testBakeryLock() {
        int threadNumber = 5;
        OuterSpace outerSpace = new OuterSpace(new BakeryLock(threadNumber));
        runSpaceWalks(outerSpace, threadNumber, 10);
    }

    @Test
    public void testTasLock() {
        int threadNumber = 5;
        OuterSpace outerSpace = new OuterSpace(new TASLock());
        runSpaceWalks(outerSpace, threadNumber, 10);
    }

    @Test
    public void testTaTasLock() {
        int threadNumber = 5;
        OuterSpace outerSpace = new OuterSpace(new TATASLock());
        runSpaceWalks(outerSpace, threadNumber, 10);
    }

    @Test
    public void testBackoffLock() {
        int threadNumber = 5;
        OuterSpace outerSpace = new OuterSpace(new BackoffLock());
        runSpaceWalks(outerSpace, threadNumber, 10);
    }

    @Test
    public void testAndersonLock() {
        int threadNumber = 5;
        OuterSpace outerSpace = new OuterSpace(new AndersonLock(threadNumber));
        runSpaceWalks(outerSpace, threadNumber, 10);
    }

    void runSpaceWalks(OuterSpace outerSpace, int threadNumber, int iterations) {
        Runnable runnable = () -> {
            System.out.println(printLogPrefix() + "start");
            for (int i = iterations; i > 0; i--) {
                outerSpace.spaceWalk();
//                System.out.println(printLogPrefix() + "finished " + i + "th iteration.");
            }
        };

        List<NumberedThread> threads = new ArrayList<>(threadNumber);
        // All thread id's must be from 0 to n-1 (for n threads) for locks to work properly!
        for (int i = 0; i < threadNumber; i++) {
            threads.add(new NumberedThread(i, runnable));
        }

        threads.forEach(Thread::start);

        try {
            for (NumberedThread thread : threads) {
                thread.join();
            }
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }

}