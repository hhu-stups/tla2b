 -------------- MODULE InstanceValue2Times ----------------
CONSTANTS k, k2
Inst == INSTANCE Value WITH val <- 1, c <- k
Inst2 == INSTANCE Value WITH val <- TRUE, c <- k2
ASSUME Inst!def /\ Inst2!def
=================================