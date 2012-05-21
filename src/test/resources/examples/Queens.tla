---- MODULE Queens ----

EXTENDS Naturals, FiniteSets

VARIABLE q, n, solved
----

Init == /\ q=[i \in 1..2 |-> 0]
        /\ n=7
        /\ solved = 0

Solve == /\ solved=0
         /\ q' \in [1..n -> 1..n]
         /\ \A i \in 1..n : (\A j \in 2..n : i<j => q'[i] # q'[j] /\ q'[i]+i-j # q'[j] /\ q'[i]-i+j # q'[j])
         /\ solved'=1
         /\ n'=n
Spec == Init /\ [] [Solve]_<<n,q>>
=======
\* Generated at Tue Jun 22 21:06:17 CEST 2010
\* Takes 2 seconds for n-6, 12 seconds to solve for n=7 and 4 minutes 9 seconds for n=8, 1h45min47sec for n=9
\* ProB takes 0.01 seconds for n=8, both on MacBook Pro 3.06 GHz
\*         /\ \A i \in 1..n : (\E j \in 1..n : q'[j]=i)