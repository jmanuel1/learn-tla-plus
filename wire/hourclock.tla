----------------------------- MODULE hourclock -----------------------------
EXTENDS Naturals
\* TODO: two clocks
(*--algorithm hourclock
variable hr = 1;

begin
    A:
        while TRUE do
            if hr = 12 then
                hr := 1;
            else
                with x \in 1..2 do
                    hr := hr + 1;
                end with;
            end if;
        end while;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "a5fcba29" /\ chksum(tla) = "b9380734")
VARIABLE hr

vars == << hr >>

Init == (* Global variables *)
        /\ hr = 1

Next == IF hr = 12
           THEN /\ hr' = 1
           ELSE /\ \E x \in 1..2:
                     hr' = hr + 1

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Wed Jan 25 21:35:50 MST 2023 by jamai
\* Created Wed Jan 25 21:24:25 MST 2023 by jamai
