-------------- MODULE InstanceOpArg3 ----------------
EXTENDS Naturals
CONSTANTS c2, bar(_,_)
bazz(a,b) == a + b
INSTANCE OpArg WITH c <- c2, foo <- bar
ASSUME def /\ c2 = 3
=================================