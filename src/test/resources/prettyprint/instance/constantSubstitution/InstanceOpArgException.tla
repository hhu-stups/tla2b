-------------- MODULE InstanceOpArgException ----------------
EXTENDS Naturals
CONSTANTS c2, bar(_,_)
INSTANCE OpArg WITH c <- c2, foo <- bar
ASSUME def /\ c2 = 3 
=================================