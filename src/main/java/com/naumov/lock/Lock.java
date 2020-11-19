package com.naumov.lock;

public interface Lock {
    /**
     * Acquire lock before entering critical section
     */
    void lock();

    /**
     * Release lock after leaving critical section
     */
    void unlock();
}
