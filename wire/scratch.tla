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

RangeStruct(struct) == {struct[key]: key \in DOMAIN struct}
\*Range(seq) == {seq[i]: i \in 1..Len(seq)}
Range(f) == {f[x] : x \in DOMAIN f}

TruthTable == [p, q \in BOOLEAN |-> p => q]

CountMatching(f, val) ==
    Cardinality({key \in DOMAIN f: f[key] = val})

IsSorted(seq) ==
    \A i, j \in 1..Len(seq):
        i < j => seq[i] <= seq[j]

\* I confused sorted with seq in the last line when I typed Sort in.
\*Sort(seq) ==
\*    CHOOSE sorted \in [DOMAIN seq -> Range(seq)]:
\*        /\ \A i \in DOMAIN seq:
\*            CountMatching(seq, seq[i]) = CountMatching(sorted, seq[i])
\*        /\ IsSorted(seq)
\* Copied from Learn TLA+
Sort(seq) ==
  CHOOSE sorted \in [DOMAIN seq -> Range(seq)]:
    /\ \A i \in DOMAIN seq:
      CountMatching(seq, seq[i]) = CountMatching(sorted, seq[i])
    /\ IsSorted(sorted)
Eval == Sort(<<8, 2, 7, 4, 3, 1, 3>>)

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

Prod ==
    LET S == 1..10 IN
        [p \in S \X S |-> p[1] * p[2]]

=============================================================================
\* Modification History
\* Last modified Sun Jan 22 09:57:03 MST 2023 by jamai
\* Created Wed Jan 18 21:13:07 MST 2023 by jamai
