package com.naumov.thread;

public class NumberedThreadAware {
    protected int currentThreadId() {
        return NumberedThread.currentThreadId();
    }

    public String printLogPrefix() {
        return "Thread " + currentThreadId() + ": ";
    }
}
