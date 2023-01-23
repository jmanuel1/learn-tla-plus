--------------------------- MODULE reader_writer ---------------------------
EXTENDS Integers, Sequences, TLC

Writers == {1, 2, 3}

(* --algorithm reader_writer
variables
    queue = <<>>;
    total = 0;
    i = 0;
    
process writer \in Writers
begin
    AddToQueue:
        (* From Learn TLA+: await interacts a little oddly with variable updates— it will be based on the updated value
        if directly embedded but not if the variable is used via a defined operator. This is due to the PlusCal->TLA+
        translation grammar. As a general precaution, don’t use updated variables in await statements. *)
        await queue = <<>>;
\*        while i < 2 do
            queue := Append(queue, self);
\*            i := i + 1;
\*        end while;
end process;

process reader = 0
\* To use self in this singly-defined process, write \in {0} instead of = 0
begin
    ReadFromQueue:
\*        if queue # <<>> then
        await queue # <<>>;
            total := total + Head(queue);
            queue := Tail(queue);
\*        end if;
        goto ReadFromQueue;
end process;
end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "4920081f" /\ chksum(tla) = "cdc0a20a")
VARIABLES queue, total, i, pc

vars == << queue, total, i, pc >>

ProcSet == (Writers) \cup {0}

Init == (* Global variables *)
        /\ queue = <<>>
        /\ total = 0
        /\ i = 0
        /\ pc = [self \in ProcSet |-> CASE self \in Writers -> "AddToQueue"
                                        [] self = 0 -> "ReadFromQueue"]

AddToQueue(self) == /\ pc[self] = "AddToQueue"
                    /\ queue = <<>>
                    /\ queue' = Append(queue, self)
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << total, i >>

writer(self) == AddToQueue(self)

ReadFromQueue == /\ pc[0] = "ReadFromQueue"
                 /\ queue # <<>>
                 /\ total' = total + Head(queue)
                 /\ queue' = Tail(queue)
                 /\ pc' = [pc EXCEPT ![0] = "ReadFromQueue"]
                 /\ i' = i

reader == ReadFromQueue

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == reader
           \/ (\E self \in Writers: writer(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sun Jan 22 18:10:59 MST 2023 by jamai
\* Created Sun Jan 22 17:36:57 MST 2023 by jamai
