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
    Liveness2 ==
        <>[](counter = NumThreads)
        
    Liveness ==
        \A t \in Threads:
            <>(lock = t)

    CounterOnlyIncreases ==
        [][counter' >= counter]_counter

    LockCantBeStolen ==
        [][lock # NULL => lock' = NULL]_lock
end define;

process thread \in Threads
variables tmp = 0;
begin
    GetLock:
\*        await lock = NULL;
        lock := self;
    GetCounter:
        tmp := counter;
    IncCounter:
        counter := tmp + 1;
    ReleaseLock:
        assert lock = self;
        lock := NULL;
\*    Reset:
\*        goto GetLock;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "e423a244" /\ chksum(tla) = "3e205078")
VARIABLES counter, lock, pc

(* define statement *)
Liveness2 ==
    <>[](counter = NumThreads)

Liveness ==
    \A t \in Threads:
        <>(lock = t)

CounterOnlyIncreases ==
    [][counter' >= counter]_counter

LockCantBeStolen ==
    [][lock # NULL => lock' = NULL]_lock

VARIABLE tmp

vars == << counter, lock, pc, tmp >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ counter = 0
        /\ lock = NULL
        (* Process thread *)
        /\ tmp = [self \in Threads |-> 0]
        /\ pc = [self \in ProcSet |-> "GetLock"]

GetLock(self) == /\ pc[self] = "GetLock"
                 /\ lock' = self
                 /\ pc' = [pc EXCEPT ![self] = "GetCounter"]
                 /\ UNCHANGED << counter, tmp >>

GetCounter(self) == /\ pc[self] = "GetCounter"
                    /\ tmp' = [tmp EXCEPT ![self] = counter]
                    /\ pc' = [pc EXCEPT ![self] = "IncCounter"]
                    /\ UNCHANGED << counter, lock >>

IncCounter(self) == /\ pc[self] = "IncCounter"
                    /\ counter' = tmp[self] + 1
                    /\ pc' = [pc EXCEPT ![self] = "ReleaseLock"]
                    /\ UNCHANGED << lock, tmp >>

ReleaseLock(self) == /\ pc[self] = "ReleaseLock"
                     /\ Assert(lock = self, 
                               "Failure of assertion at line 40, column 9.")
                     /\ lock' = NULL
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << counter, tmp >>

thread(self) == GetLock(self) \/ GetCounter(self) \/ IncCounter(self)
                   \/ ReleaseLock(self)

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
\* Last modified Wed Jan 25 21:07:41 MST 2023 by jamai
\* Created Sun Jan 22 18:15:41 MST 2023 by jamai
