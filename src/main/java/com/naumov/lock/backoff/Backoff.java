package com.naumov.lock.backoff;

import java.util.Random;

public class Backoff {
    private final int minTimeout, maxTimeout;
    private int limit;
    private final Random random;

    public Backoff(int min, int max) {
        this.minTimeout = min;
        this.maxTimeout = max;
        this.limit = minTimeout;
        this.random = new Random();
    }

    public void backoff() {
        int timeout = random.nextInt(limit);
        limit = Math.min(limit * 2, maxTimeout);
        try {
            Thread.sleep(timeout);
        } catch (InterruptedException e) {
            // handle properly in practice
            e.printStackTrace();
        }
    }
}
