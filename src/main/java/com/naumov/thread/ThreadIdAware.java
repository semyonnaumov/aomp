package com.naumov.thread;

public class ThreadIdAware {
    protected int currentThreadId() {
        return NumberedThread.currentThreadId();
    }
}
