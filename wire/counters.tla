------------------------------ MODULE counters ------------------------------
EXTENDS Integers

Counters == {1, 2}
(* --algorithm counters
variables
    values = [i \in Counters |-> 0];

define
    CounterOnlyIncreases ==
        [][\A c \in Counters: values[c]' >= values[c]]_values
end define;

macro increment() begin
    values[self] := values[self] + 1;
end macro

process counter \in Counters
begin
    A:
        increment();
    B:
        increment();
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "ace1df44" /\ chksum(tla) = "791a37da")
VARIABLES values, pc

(* define statement *)
CounterOnlyIncreases ==
    [][\A c \in Counters: values[c]' >= values[c]]_values


vars == << values, pc >>

ProcSet == (Counters)

Init == (* Global variables *)
        /\ values = [i \in Counters |-> 0]
        /\ pc = [self \in ProcSet |-> "A"]

A(self) == /\ pc[self] = "A"
           /\ values' = [values EXCEPT ![self] = values[self] + 1]
           /\ pc' = [pc EXCEPT ![self] = "B"]

B(self) == /\ pc[self] = "B"
           /\ values' = [values EXCEPT ![self] = values[self] + 1]
           /\ pc' = [pc EXCEPT ![self] = "Done"]

counter(self) == A(self) \/ B(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Counters: counter(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Wed Jan 25 21:04:06 MST 2023 by jamai
\* Created Tue Jan 24 19:12:25 MST 2023 by jamai
