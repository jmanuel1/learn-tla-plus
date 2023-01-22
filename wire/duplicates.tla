----------------------------- MODULE duplicates -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets

CONSTANT S, Size
ASSUME Cardinality(S) >= 4
ASSUME Size > 0

(*--algorithm dup
    variable
    n \in 1..Size;
    seq \in [1..n -> S];
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
\* BEGIN TRANSLATION (chksum(pcal) = "540c1e02" /\ chksum(tla) = "9e7fbf07")
VARIABLES n, seq, index, seen, is_unique, pc

(* define statement *)
TypeInvariant ==
    /\ is_unique \in BOOLEAN
    /\ seen \subseteq S
    /\ index \in 1..Len(seq)+1
IsUnique(s) ==
    \A i, j \in 1..Len(s):
        i # j => s[i] # s[j]
IsCorrect == pc = "Done" => is_unique = IsUnique(seq)


vars == << n, seq, index, seen, is_unique, pc >>

Init == (* Global variables *)
        /\ n \in 1..Size
        /\ seq \in [1..n -> S]
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
           /\ UNCHANGED << n, seq >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Iterate
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sun Jan 22 09:55:45 MST 2023 by jamai
\* Created Wed Jan 18 22:53:05 MST 2023 by jamai
