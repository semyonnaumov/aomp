package com.naumov;

import com.naumov.lock.FilterLock;
import com.naumov.lock.FirstLock;
import com.naumov.lock.PetersonLock;
import com.naumov.lock.SecondLock;
import com.naumov.sc.space.OuterSpace;
import com.naumov.thread.NumberedThread;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static com.naumov.thread.NumberedThread.currentThreadId;

class LockTestOnOuterSpace {

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

    void runSpaceWalks(OuterSpace outerSpace, int threadNumber, int iterations) {
        Runnable runnable = () -> {
            System.out.println("Thread " + currentThreadId() + " start");
            for (int i = iterations; i > 0; i--) {
                outerSpace.spaceWalk();
//                System.out.println("Thread " + currentThreadId() + " finished " + i + "th iteration.");
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