package com.naumov.cs.space;

import com.naumov.lock.Lock;
import com.naumov.thread.NumberedThreadAware;

import java.util.EmptyStackException;
import java.util.Stack;

public class OuterSpace extends NumberedThreadAware {
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
            System.out.println(printLogPrefix() + "Having nice spacewalk!");
            spaceSuitHolder.push(suit);
        } catch (EmptyStackException e) {
            int threadNumber = currentThreadId();
            System.out.println(printLogPrefix() + "Oh shit, no spacesuit!");
        } finally {
            lock.unlock();
        }
    }
}
