package com.naumov;

import com.naumov.lock.FirstLock;
import com.naumov.lock.SecondLock;
import com.naumov.sc.space.OuterSpace;
import com.naumov.thread.NumberedThread;
import org.junit.jupiter.api.Test;

import static com.naumov.thread.NumberedThread.currentThreadId;

class LockTestOnOuterSpace {

    @Test
    public void testSecondLock() {
        OuterSpace outerSpace = new OuterSpace(new SecondLock());
        // deadlocks
        runSpaceWalks(outerSpace, 10);
    }

    @Test
    public void testFirstLock() {
        OuterSpace outerSpace = new OuterSpace(new FirstLock());
        // deadlocks
        runSpaceWalks(outerSpace, 10);
    }

    void runSpaceWalks(OuterSpace outerSpace, int iterations) {
        Runnable runnable = () -> {
            System.out.println("Thread " + currentThreadId() + " start");
            for (int i = iterations; i > 0; i--) {
                outerSpace.spaceWalk();
//                System.out.println("Thread " + currentThreadId() + " finished " + i + "th iteration.");
            }
        };

        Thread th1 = new NumberedThread(0, runnable);
        Thread th2 = new NumberedThread(1, runnable);

        th1.start();
        th2.start();

        try {
            th1.join();
            th2.join();
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }

}