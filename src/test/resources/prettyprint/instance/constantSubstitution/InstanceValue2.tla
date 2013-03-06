-------------- MODULE InstanceValue2 ----------------
EXTENDS Naturals
CONSTANTS c, val2
INSTANCE Value WITH val <- val2
ASSUME def /\ val2 = 1
=================================