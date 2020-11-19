package com.naumov.thread;

public class NumberedThread extends Thread {
    private final int number;

    public static int currentThreadId() {
        Thread current = Thread.currentThread();
        if (current.getClass().equals(NumberedThread.class)) {
            return ((NumberedThread) current).getNumber();
        } else {
            throw new IllegalStateException("Got thread class different from " + NumberedThread.class.getSimpleName() + ".");
        }
    }

    public NumberedThread(int number) {
        this.number = number;
    }

    public NumberedThread(int number, Runnable target) {
        super(target);
        this.number = number;
    }

    public int getNumber() {
        return number;
    }
}
