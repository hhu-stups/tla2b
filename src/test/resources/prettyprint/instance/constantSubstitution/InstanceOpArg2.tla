-------------- MODULE InstanceOpArg2 ----------------
EXTENDS Naturals
CONSTANTS c2
bar(a,b) == a + b 
INSTANCE OpArg WITH c <- c2, foo <- bar
ASSUME def /\ c2 = 3 
=================================