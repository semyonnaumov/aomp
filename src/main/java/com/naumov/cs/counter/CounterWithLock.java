package com.naumov.cs.counter;

import com.naumov.lock.Lock;

public class CounterWithLock implements Counter {
    private int value;
    private Lock lock;

    public CounterWithLock(int value, Lock lock) {
        this.value = value;
        this.lock = lock;
    }

    @Override
    public int getAndIncrement() {
        lock.lock();

        try {
            int temp = value;
            value = value + 1;
            return temp;
        } finally { // we need to leave the lock even if some exception occurs to let other threads go on!
            lock.unlock();
        }
    }
}
