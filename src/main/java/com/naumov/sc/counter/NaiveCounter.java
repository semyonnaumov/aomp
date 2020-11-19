package com.naumov.sc.counter;

public class NaiveCounter implements Counter {
    private int value;
    public NaiveCounter(int c) {
        value = c;
    }

    @Override
    public int getAndIncrement() {
        int temp = value; // start of danger zone
        value = value + 1; // end of danger zone
        return temp;
    }
}
