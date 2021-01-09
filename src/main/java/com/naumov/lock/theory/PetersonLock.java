package com.naumov.lock.theory;

import com.naumov.lock.Lock;
import com.naumov.thread.NumberedThreadAware;

/**
 * - Mutex
 * - Deadlock-Free
 * - Starvation-Free
 */
public class PetersonLock extends NumberedThreadAware implements Lock {
    private final boolean[] interestedThreads = new boolean[2];
    private volatile int victim; // have to be volatile to be consistent for both threads

    @Override
    public void lock() {
        int me = currentThreadId();
        int other = 1 - currentThreadId();

        interestedThreads[me] = true; // I'm interested
        victim = me; // you go first

        // wait
        while (interestedThreads[other] && victim == me) {}
    }

    @Override
    public void unlock() {
        interestedThreads[currentThreadId()] = false; // I'm not interested
    }
}

//----------------------------- MODULE PetersonLock -----------------------------
//
//        EXTENDS Integers, FiniteSets
//
//        CONSTANT threads
//        VARIABLES flags, tstate, victim, cs
//
//        \* thread states: idle, aquiring, aquired, finished
//
//        TypeOK == /\ flags \in [threads -> {TRUE, FALSE}]
//        /\ victim \in threads
//        /\ cs \subseteq threads
//
//        Init == /\ tstate = [t \in threads |-> 0]
//        /\ flags = [t \in threads |-> FALSE]
//        /\ cs = {}
//        /\ victim = CHOOSE x \in threads : TRUE
//
//        RaiseFlag(t) ==
//        /\ tstate[t]= 0
//        /\ flags = [flags EXCEPT ![t] = TRUE]
//        /\ tstate = [tstate EXCEPT ![t] = 1]
//        /\ UNCHANGED victim
//        /\ UNCHANGED cs
//
//        BecameVictim(t) ==
//        /\ tstate[t]= 1
//        /\ UNCHANGED flags
//        /\ tstate = [tstate EXCEPT ![t] = 2]
//        /\ victim = t
//        /\ UNCHANGED cs
//
//        Enter(t) ==
//        /\ tstate[t]= 2
//        /\ ~(\A s \in threads \ {t} : flags[s] /\ victim = t)
//        /\ UNCHANGED flags
//        /\ UNCHANGED victim
//        /\ tstate = [tstate EXCEPT ![t] = 3]
//        /\ cs' = cs \cup {t}
//
//        Unlock(t) ==
//        /\ tstate[t]= 3
//        /\ flags = [flags EXCEPT ![t] = FALSE]
//        /\ tstate = [tstate EXCEPT ![t] = 0]
//        /\ cs' = cs \ {t}
//        /\ UNCHANGED victim
//
//        Next == \A t \in threads : \/ RaiseFlag(t)
//        \/ BecameVictim(t)
//        \/ Enter(t)
//        \/ Unlock(t)
//
//        Mutex == Cardinality(cs) < 2
//
//        =============================================================================
//        \* Modification History
//        \* Last modified Sat Jan 09 22:32:44 MSK 2021 by u17773014
//        \* Created Sat Jan 09 21:30:43 MSK 2021 by u17773014

