package com.naumov.sc.space;

import com.naumov.lock.Lock;

import java.util.EmptyStackException;
import java.util.Stack;

import static com.naumov.thread.NumberedThread.currentThreadId;

public class OuterSpace {
    private final Stack<Object> spaceSuitHolder;
    private final Lock lock;

    public OuterSpace(Lock lock) {
        this.spaceSuitHolder = new Stack<>();
        spaceSuitHolder.push(new Object());
        this.lock = lock;
    }

    public void spaceWalk() {
        lock.lock();
        try {
            int threadNumber = currentThreadId();
            Object suit = spaceSuitHolder.pop();
            System.out.println(threadNumber + ": Having nice spacewalk!");
            spaceSuitHolder.push(suit);
        } catch (EmptyStackException e) {
            int threadNumber = currentThreadId();
            System.out.println(threadNumber + ": Oh shit, no spacesuit!");
        } finally {
            lock.unlock();
        }
    }
}
