---- MODULE GraphIso ----

EXTENDS Naturals, FiniteSets
VARIABLE g1, g2, p, n, solved
----
Init == /\ n = 9
        /\ g1 = [[i\in 1..n|->i] EXCEPT ![1]=3,![2]=3,![3]=6,![4]=6,![5]=6,![8]=9,![9]=8]
        /\ g2 = [[i\in 1..n|->i] EXCEPT ![2]=5,![3]=5,![4]=5,![6]=4,![7]=4,![1]=9,![9]=1]
        /\ p = [i \in 1..n |-> 0]
        /\ solved = 0
Solve == /\ solved = 0
         /\ solved' = 1
         /\ p' \in [1..n -> 1..n]
         /\ \A i \in 1..n : (\E j \in 1..n : p'[j]=i)
         /\ \A i \in 1..n : (p'[g1[i]] = g2[p'[i]])
         /\ UNCHANGED <<g1,g2,n>>
====
\* Generated at Wed Jul 21 15:51:20 CEST 2010
\*         /\ \A i \in 1..n : (p'[g1[i]] = g2[p'[i]])
\* trying to encode graph isomporphism in TLA for graphs with exactly one successor
\* ProB takes 0.06 seconds for first solution; 0.1 second for all 8 solutions
\* TLC starts at  21:28:18
\* finds permutation <<6, 7, 4, 2, 3, 5, 8, 1, 9>>   at 23:34:46  (2h 6mins 28secs)
\* same as first permutation found by ProB in 0.06 seconds