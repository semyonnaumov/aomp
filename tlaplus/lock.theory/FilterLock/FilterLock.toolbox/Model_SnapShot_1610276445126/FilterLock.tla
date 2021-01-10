----------------------------- MODULE FilterLock -----------------------------

EXTENDS Integers, FiniteSets

CONSTANT THREAD_NUM
CONSTANT THREADS

VARIABLES level, victim, tstate, threads_in_cs

\* thread states:
\* 0 - idle
\* 1 - just level-upped, must declare itself a victim next step
\* 2 - declared itself a victim after level-up
\* 3 - in cs

TypeOK == 
        /\ level \in [THREADS -> 0..(THREAD_NUM - 1)] \* threadId -> levelNum
        /\ victim \in [0..(THREAD_NUM - 1) -> THREADS] \* levelNum -> threadId
        /\ tstate \in [THREADS -> 0..3] \* threadId -> stateNum
        /\ threads_in_cs \subseteq THREADS

Init == /\ level = [t \in THREADS |-> 0]
        /\ LET vict == CHOOSE s \in THREADS : TRUE
           IN /\ victim = [l \in 0..(THREAD_NUM - 1) |-> vict]
        /\ tstate = [t \in THREADS |-> 0]   
        /\ threads_in_cs = {}
        
CannotGoFurther(t, l) ==
        /\ victim[l] = t 
        /\ \E s \in THREADS : (~(s = t) /\ level[s] >= level[t])
        
\* Increment thread's level when possible
LevelUp(t) ==
        /\ (tstate[t] = 0 \/ tstate[t] = 2) \* idle or declared victims can go up
        /\ ~(level[t] = THREAD_NUM - 1) \* not at the last level
        /\ ~(CannotGoFurther(t, level[t]))
        /\ level' = [level EXCEPT ![t] = level[t] + 1]
        /\ UNCHANGED victim
        /\ tstate' = [tstate EXCEPT ![t] = 1]
        /\ UNCHANGED threads_in_cs
        
\* After level up, a thread must declare itself a victim
BecomeVictim(t) ==
        /\ tstate[t] = 1
        /\ UNCHANGED level
        /\ victim' = [victim EXCEPT ![level[t]] = t]
        /\ tstate' = [tstate EXCEPT ![t] = 2]
        /\ UNCHANGED threads_in_cs 
        
\* When at the last level and declared itself a victim = is in the cs
Lock(t) ==    
        /\ level[t] = THREAD_NUM - 1 \* at the last level
        /\ tstate[t] = 2 \* victim
        /\ UNCHANGED level
        /\ UNCHANGED victim
        /\ tstate' = [tstate EXCEPT ![t] = 3]
        /\ threads_in_cs' = threads_in_cs \cup {t}

Unlock(t) ==         
        /\ tstate[t] = 3
        /\ level' = [level EXCEPT ![t] = 0]
        /\ UNCHANGED victim
        /\ tstate' = [tstate EXCEPT ![t] = 0]
        /\ threads_in_cs' = threads_in_cs \ {t}
        
Next == \E t \in THREADS : 
            \/ LevelUp(t)
            \/ BecomeVictim(t)
            \/ Lock(t)
            \/ Unlock(t)
          
Mutex == Cardinality(threads_in_cs) < 2        

=============================================================================
\* Modification History
\* Last modified Sun Jan 10 13:33:08 MSK 2021 by u17773014
\* Created Sat Jan 09 21:30:43 MSK 2021 by u17773014
