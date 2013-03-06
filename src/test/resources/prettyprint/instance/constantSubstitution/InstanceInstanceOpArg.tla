-------------- MODULE InstanceInstanceOpArg ----------------
EXTENDS Naturals
CONSTANTS c3, foo3(_,_)
bazz(a,b) == a + b
INSTANCE InstanceOpArg WITH c2 <- c3, foo2 <- foo3
ASSUME def /\ c3 = 3 
=================================