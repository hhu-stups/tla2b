----- MODULE RecursiveFunction -----
EXTENDS Naturals
CONSTANTS k, k2, k3
fact[n \in Nat] == IF n = 0 THEN 1 ELSE n * fact[n-1]
ASSUME k = fact[0] /\ k2 = fact[3] /\ k3 = fact[4]
=======================

