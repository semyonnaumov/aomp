---------------------------- MODULE PetersonLock ----------------------------

EXTENDS Integers, FiniteSets

CONSTANT THREADS
VARIABLES flags, tstate, victim, cs

TypeOK == /\ tstate \in [THREADS -> 0..3]
          /\ flags \in [THREADS -> {TRUE, FALSE}] 
          /\ victim \in THREADS
          /\ cs \subseteq THREADS

Init == /\ tstate = [t \in THREADS |-> 0]
        /\ flags = [t \in THREADS |-> FALSE]
        /\ cs = {}
        /\ victim = CHOOSE x \in THREADS : TRUE
        
RaiseFlag(t) == 
        /\ tstate[t] = 0
        /\ flags' = [flags EXCEPT ![t] = TRUE]
        /\ tstate' = [tstate EXCEPT ![t] = 1]
        /\ UNCHANGED victim
        /\ UNCHANGED cs
        
BecameVictim(t) ==
        /\ tstate[t]= 1
        /\ UNCHANGED flags
        /\ tstate' = [tstate EXCEPT ![t] = 2]
        /\ victim' = t
        /\ UNCHANGED cs
        
Enter(t) ==
        /\ tstate[t] = 2
        /\ ~(\A s \in THREADS \ {t} : flags[s] /\ victim = t) 
        /\ UNCHANGED flags
        /\ UNCHANGED victim
        /\ tstate' = [tstate EXCEPT ![t] = 3]
        /\ cs' = cs \cup {t}
        
Unlock(t) ==
        /\ tstate[t] = 3
        /\ flags' = [flags EXCEPT ![t] = FALSE]
        /\ tstate' = [tstate EXCEPT ![t] = 0]
        /\ cs' = cs \ {t}
        /\ UNCHANGED victim
        
Next == \E t \in THREADS : \/ RaiseFlag(t)
                     \/ BecameVictim(t)
                     \/ Enter(t)
                     \/ Unlock(t)
          
Mutex == Cardinality(cs) < 2        

=============================================================================
\* Modification History
\* Last modified Sun Jan 10 00:10:03 MSK 2021 by u17773014
\* Created Sat Jan 09 23:49:08 MSK 2021 by u17773014
