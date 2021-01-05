package com.naumov.lock.queue;

import com.naumov.lock.Lock;

import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;

/**
 * - Mutex
 * - Deadlock-Free
 * - Starvation-Free
 * - First-Come-First-Served
 * - лучше AndersonLock, использует меньше памяти, отпукание лока влияет только на предшественника
 * - не работает на uncached NUMA
 */
public class CLHLock implements Lock {
    private final AtomicReference<QNode> tail;
    private final ThreadLocal<QNode> myPred;
    private final ThreadLocal<QNode> myNode;

    public CLHLock() {
        // в книге опечатка, нужно инициализировать именно так
        tail = new AtomicReference<>(new QNode());
        myPred = ThreadLocal.withInitial(() -> null);
        myNode = ThreadLocal.withInitial(QNode::new);
    }

    @Override
    public void lock() {
        QNode pred = announceAcquiring();
        myPred.set(pred);
        spinLocally(pred);
    }

    private QNode announceAcquiring() {
        QNode qNode = myNode.get();
        qNode.lock();
        return tail.getAndSet(qNode);
    }

    private void spinLocally(QNode pred) {
        while (pred.isLocked()) {
        }
    }

    @Override
    public void unlock() {
        myNode.get().unlock(); // release
        myNode.set(myPred.get()); // reuse predecessor node
    }

    private static class QNode {
        private final AtomicBoolean locked = new AtomicBoolean(false);

        public boolean isLocked() {
            return locked.get();
        }

        public void lock() {
            locked.set(true);
        }

        public void unlock() {
            locked.set(false);
        }
    }
}
