---------------------------- MODULE orchestrator ----------------------------
EXTENDS Integers, TLC, FiniteSets

Servers == {"s1", "s2"}

(*--algorithm threads
variables
    online = Servers;

define
    Invariant == \E s \in Servers: s \in online
    Safety == \E s \in Servers: [](s \in online)
    (* Learn TLA+: ~[] formally means "In every behavior, there is at least one state where
    P is false." *)
    Liveness == ~[](online = Servers)
end define;

fair process orchestrator = "orchestrator"
begin
    Change:
        while TRUE do
            with s \in Servers do
                either
                    await s \notin online;
                    online := online \union {s};
                or
                    await s \in online;
                    await Cardinality(online) > 1;
                    online := online \ {s};
                end either;
            end with;
        end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "224ae564" /\ chksum(tla) = "95c7632b")
VARIABLE online

(* define statement *)
Invariant == \E s \in Servers: s \in online
Safety == \E s \in Servers: [](s \in online)


Liveness == ~[](online = Servers)


vars == << online >>

ProcSet == {"orchestrator"}

Init == (* Global variables *)
        /\ online = Servers

orchestrator == \E s \in Servers:
                  \/ /\ s \notin online
                     /\ online' = (online \union {s})
                  \/ /\ s \in online
                     /\ Cardinality(online) > 1
                     /\ online' = online \ {s}

Next == orchestrator

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(orchestrator)

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sun Jan 22 18:53:03 MST 2023 by jamai
\* Created Sun Jan 22 18:37:31 MST 2023 by jamai
