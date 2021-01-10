-------------------------- MODULE ManualResetEvent --------------------------
\* https://deadlockempire.github.io/#H1-ManualResetEvent

EXTENDS Integers

\* thread 0:
\*
\*    while (true) {
\*      sync.Wait();
\*      if (counter % 2 == 1) {
\*        Debug.Assert(false);
\*      }
\*    }   

\* thread 1:
\*
\*    while (true) {
\*      sync.Reset();
\*      counter++;
\*      counter++;
\*      sync.Set();
\*    }

VARIABLES sync, counter, first, second, failure

TypeOK == 
        /\ sync \in {"nonsignaled", "signaled"}
        /\ counter \in Int
        /\ first \in {
                        0, \* iteration start = finish waiting
                        1  \* can check "if" condition
                     }
        /\ second \in {
                        0, \* iteration start = ready to reset
                        1, \* ready to increment 
                        2, \* ready to increment again
                        3  \* ready to set
                      }
        /\ failure \in {TRUE, FALSE}
        
Init == /\ sync = "nonsignaled"
        /\ counter = 0
        /\ first = 0
        /\ second = 0
        /\ failure = FALSE
            
FirstProceeds ==
        /\ first = 0
        /\ sync = "signaled"
        /\ UNCHANGED sync
        /\ UNCHANGED counter
        /\ first' = 1
        /\ UNCHANGED second
        /\ UNCHANGED failure
        
FirstCheckCondition ==
        /\ first = 1
        /\ IF (counter % 2 = 1)
              THEN /\ failure' = TRUE
              ELSE /\ UNCHANGED failure
        /\ UNCHANGED sync
        /\ UNCHANGED counter
        /\ first' = 0
        /\ UNCHANGED second

SecondReset ==
        /\ second = 0
        /\ sync' = "nonsignaled"
        /\ UNCHANGED counter
        /\ UNCHANGED first
        /\ second' = 1
        /\ UNCHANGED failure

SecondIncrement1 ==
        /\ second = 1
        /\ UNCHANGED sync
        /\ counter' = counter + 1
        /\ UNCHANGED first
        /\ second' = 2
        /\ UNCHANGED failure

SecondIncrement2 ==
        /\ second = 2
        /\ UNCHANGED sync
        /\ counter' = counter + 1
        /\ UNCHANGED first
        /\ second' = 3
        /\ UNCHANGED failure
        
SecondSet ==
        /\ second = 3
        /\ sync' = "signaled"
        /\ UNCHANGED counter
        /\ UNCHANGED first
        /\ second' = 0
        /\ UNCHANGED failure       

Next == \/ FirstProceeds
        \/ FirstCheckCondition
        \/ SecondReset
        \/ SecondIncrement1
        \/ SecondIncrement2
        \/ SecondSet

Failure == failure = FALSE

=============================================================================
\* Modification History
\* Last modified Sun Jan 10 17:33:25 MSK 2021 by u17773014
\* Created Sun Jan 10 16:08:45 MSK 2021 by u17773014
