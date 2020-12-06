package com.naumov.thread;

public class ThreadIdAware {
    protected int currentThreadId() {
        return NumberedThread.currentThreadId();
    }

    public String printLogPrefix() {
        return "Thread " + currentThreadId() + ": ";
    }
}
