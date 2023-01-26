------------------------------ MODULE threads ------------------------------
EXTENDS TLC, Sequences, Integers
CONSTANT NULL

NumThreads == 2
Threads == 1..NumThreads

(* --algorithm threads

variables
    counter = 0;
    lock = NULL;
    
define
    AllDone ==
        \A t \in Threads: pc[t] = "Done"

    Correct ==
        AllDone => counter = NumThreads
end define;

process thread \in Threads
variables tmp = 0;
begin
    IncCounter:
        counter := counter + 1;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "ddf345" /\ chksum(tla) = "fd964471")
VARIABLES counter, lock, pc

(* define statement *)
AllDone ==
    \A t \in Threads: pc[t] = "Done"

Correct ==
    AllDone => counter = NumThreads

VARIABLE tmp

vars == << counter, lock, pc, tmp >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ counter = 0
        /\ lock = NULL
        (* Process thread *)
        /\ tmp = [self \in Threads |-> 0]
        /\ pc = [self \in ProcSet |-> "IncCounter"]

IncCounter(self) == /\ pc[self] = "IncCounter"
                    /\ counter' = counter + 1
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << lock, tmp >>

thread(self) == IncCounter(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Threads: thread(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
TypeInvariant ==
    /\ counter \in 0..NumThreads
    /\ tmp \in [Threads -> 0..NumThreads]
    /\ lock \in Threads \union {NULL}
CounterNotLtTmp2 ==
    \A t \in Threads:
        tmp[t] <= counter
=============================================================================
\* Modification History
\* Last modified Wed Jan 25 21:43:04 MST 2023 by jamai
\* Created Sun Jan 22 18:15:41 MST 2023 by jamai
