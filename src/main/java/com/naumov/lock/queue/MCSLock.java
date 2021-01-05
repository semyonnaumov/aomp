package com.naumov.lock.queue;

import com.naumov.lock.Lock;

import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;

/**
 * - Mutex
 * - Deadlock-Free
 * - Starvation-Free
 * - First-Come-First-Served
 * - лучше чем CLHLock, работает с NUMA
 */
public class MCSLock implements Lock {
    private final AtomicReference<QNode> tail;
    private final ThreadLocal<QNode> myNode;

    public MCSLock() {
        tail = new AtomicReference<>(null);
        myNode = ThreadLocal.withInitial(QNode::new);
    }

    @Override
    public void lock() {
        QNode qNode = myNode.get();
        QNode pred = registerGlobally(qNode);

        if (queueIsEmpty(pred)) return;

        announceAndRegister(qNode, pred);
        waitForNotification(pred);

    }

    private QNode registerGlobally(QNode qNode) {
        return tail.getAndSet(qNode);
    }

    private boolean queueIsEmpty(QNode pred) {
        return pred == null;
    }

    private void announceAndRegister(QNode qNode, QNode pred) {
        qNode.setLocked(true);
        pred.setNext(qNode);
    }

    private void waitForNotification(QNode pred) {
        while (pred.isLocked()) {
        }
    }

    @Override
    public void unlock() {
        QNode qNode = myNode.get();
        if (qNode.getNext() == null) {
            if (isTheLastOne(qNode)) return;
            waitForSuccessor(qNode);
        }
        releaseAndNotify(qNode);
    }

    private boolean isTheLastOne(QNode qNode) {
        return tail.compareAndSet(qNode, null);
    }

    private void waitForSuccessor(QNode qNode) {
        // минимальная вероятность задержки, так как кто-то уже зарегистрировался глобально,
        // и скоро зарегистрируется локально
        while (qNode.getNext() == null) {
        }
    }

    private void releaseAndNotify(QNode qNode) {
        qNode.getNext().setLocked(false);
        qNode.setNext(null);
    }

    private static class QNode {
        private final AtomicBoolean locked = new AtomicBoolean(false);
        private final AtomicReference<QNode> next = new AtomicReference<>(null);

        public boolean isLocked() {
            return locked.get();
        }

        public void setLocked(boolean locked) {
            this.locked.set(locked);
        }

        public QNode getNext() {
            return this.next.get();
        }

        public void setNext(QNode next) {
            this.next.set(next);
        }
    }
}
