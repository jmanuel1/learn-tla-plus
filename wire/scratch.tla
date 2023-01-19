------------------------------ MODULE scratch ------------------------------
EXTENDS Integers, TLC, Sequences, FiniteSets

ClockType == (0..23) \X (0..59) \X (0..59)
ToSeconds(time) == time[1]*3600 + time[2]*60 + time[3]
ToClock(seconds) == 
    LET seconds_per_day == 86400 
    IN CHOOSE x \in ClockType: ToSeconds(x) = seconds % seconds_per_day
ToClock2(seconds) ==
    LET
        h == seconds \div 3600
        h_left == seconds % 3600
        m == h_left \div 60
        m_left == h_left % 60
        s == m_left \div 60 \* NOTE: This is wrong. Is that deliberate?
    IN
        <<h, m, s>>
        
Test == LET
    seq == <<1, 2, 3, 4>>
    s == 1..4
IN
    CHOOSE p \in s \X s: seq[p[1]] = seq[p[2]]

Eval == Test

MinutesToSeconds(m) == m * 60
SecondsPerMinute == 60
Abs(x) == IF x < 0 THEN -x ELSE x
Xor(A, B) == A = ~B

\* Exercise: Contrapositives
\* 1. Rewrite A => B using the “regular three” programming operators.
Implies(A, B) == ~A \/ B 
\* 2. For what values of A and B is ~B => ~A true?
\* ~B => ~A is A => B, which is true when A is false or B is true.


Earlier(t1, t2) == ToSeconds(t1) < ToSeconds(t2)

AddTimes(t1, t2) == <<t1[1] + t2[1], t1[2] + t2[2], t1[3] + t2[3]>>
\*** NOTE: Sets cannot contain elements of different types; {1, "a"} is invalid. ***

Squares == {x*x: x \in 1..4}
Evens == {x \in 1..4: x % 2 = 0}

SecondHalfOfHour == {t \in ClockType: t[2] >= 30 /\ t[3] = 30}
Range(seq) == {seq[i]: i \in 1..Len(seq)}

ThreeMax(a, b, c) ==
    LET
        Max(x, y) == IF x > y THEN x ELSE y
        maxab == Max(a, b)
    IN
        Max(maxab, c)
        
IsComposite(num) ==
    \E m, n \in 2..num:
        m * n = num

Contains(seq, elem) ==
    \E i \in 1..Len(seq):
        seq[i] = elem

=============================================================================
\* Modification History
\* Last modified Thu Jan 19 01:20:26 MST 2023 by jamai
\* Created Wed Jan 18 21:13:07 MST 2023 by jamai
