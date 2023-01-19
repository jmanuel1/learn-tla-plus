----------------------------- MODULE duplicates -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets

S == 1..10

(*--algorithm dup
    variable seq \in S \X S \X S \X S;
    index = 1;
    seen = {};
    is_unique = TRUE;
    
 define
    TypeInvariant == \*is_unique = TRUE
        /\ is_unique \in BOOLEAN
        /\ seen \subseteq S
        /\ index \in 1..Len(seq)+1
    IsUnique(s) == \*Cardinality(seen) = Len(s)
        \A i, j \in 1..Len(s):
            i # j => s[i] # s[j]
    IsCorrect == pc = "Done" => is_unique = IsUnique(seq)

 end define;

 begin
    Iterate:
        while index <= Len(seq) do
            if seq[index] \notin seen then
                seen := seen \union {seq[index]}
            else
                is_unique := FALSE;
            end if;
            index := index + 1
        end while;
 end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "9eaf8f8e" /\ chksum(tla) = "99796512")
VARIABLES seq, index, seen, is_unique, pc

(* define statement *)
TypeInvariant ==
    /\ is_unique \in BOOLEAN
    /\ seen \subseteq S
    /\ index \in 1..Len(seq)+1
IsUnique(s) ==
    \A i, j \in 1..Len(s):
        i # j => s[i] # s[j]
IsCorrect == pc = "Done" => is_unique = IsUnique(seq)


vars == << seq, index, seen, is_unique, pc >>

Init == (* Global variables *)
        /\ seq \in S \X S \X S \X S
        /\ index = 1
        /\ seen = {}
        /\ is_unique = TRUE
        /\ pc = "Iterate"

Iterate == /\ pc = "Iterate"
           /\ IF index <= Len(seq)
                 THEN /\ IF seq[index] \notin seen
                            THEN /\ seen' = (seen \union {seq[index]})
                                 /\ UNCHANGED is_unique
                            ELSE /\ is_unique' = FALSE
                                 /\ seen' = seen
                      /\ index' = index + 1
                      /\ pc' = "Iterate"
                 ELSE /\ pc' = "Done"
                      /\ UNCHANGED << index, seen, is_unique >>
           /\ seq' = seq

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Iterate
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Thu Jan 19 01:19:22 MST 2023 by jamai
\* Created Wed Jan 18 22:53:05 MST 2023 by jamai
