------------------------------ MODULE pluscal ------------------------------
EXTENDS Integers, TLC, Sequences

(* --algorithm pluscal
variables
    x = 2;
    y = TRUE;
    seq = <<x, 10>>;
    i = 0;
    
macro inc(var) begin
    if var < 10 then
        var := var + 1;
    end if;
    with tmp_x = x, tmp_y = y do
        y := tmp_x;
        x := tmp_y;
    end with;
end macro;
    
begin
    A:
        x := x + 1;
    B:
        x := x + 1;
        y := FALSE;
        if y then
            C:
                skip;
        else
            skip;
        end if;
        D: skip;
    Sum:
        \*** NOTE: While is nonatomic. After each iteration of the while loop, we’re back at the Sum label. 
        \*   Other processes can run before the next iteration.
        while i <= Len(seq) do
            x := x + seq[i];
            Inc:
                i := i + 1;
        end while;
end algorithm; *) 
\* BEGIN TRANSLATION (chksum(pcal) = "2685cc8e" /\ chksum(tla) = "a8484a9")
VARIABLES x, y, seq, i, pc

vars == << x, y, seq, i, pc >>

Init == (* Global variables *)
        /\ x = 2
        /\ y = TRUE
        /\ seq = <<x, 10>>
        /\ i = 0
        /\ pc = "A"

A == /\ pc = "A"
     /\ x' = x + 1
     /\ pc' = "B"
     /\ UNCHANGED << y, seq, i >>

B == /\ pc = "B"
     /\ x' = x + 1
     /\ y' = FALSE
     /\ IF y'
           THEN /\ pc' = "C"
           ELSE /\ TRUE
                /\ pc' = "D"
     /\ UNCHANGED << seq, i >>

C == /\ pc = "C"
     /\ TRUE
     /\ pc' = "D"
     /\ UNCHANGED << x, y, seq, i >>

D == /\ pc = "D"
     /\ TRUE
     /\ pc' = "Sum"
     /\ UNCHANGED << x, y, seq, i >>

Sum == /\ pc = "Sum"
       /\ IF i <= Len(seq)
             THEN /\ x' = x + seq[i]
                  /\ pc' = "Inc"
             ELSE /\ pc' = "Done"
                  /\ x' = x
       /\ UNCHANGED << y, seq, i >>

Inc == /\ pc = "Inc"
       /\ i' = i + 1
       /\ pc' = "Sum"
       /\ UNCHANGED << x, y, seq >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == A \/ B \/ C \/ D \/ Sum \/ Inc
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Wed Jan 18 22:48:45 MST 2023 by jamai
\* Created Wed Jan 18 22:25:45 MST 2023 by jamai
