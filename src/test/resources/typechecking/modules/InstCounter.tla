-------------------------- MODULE InstCounter -----------------------------
EXTENDS Naturals
CONSTANTS k
VARIABLE u
bar == 1
inst == INSTANCE Counter WITH x <- u, start <- bar + k
inst2 == INSTANCE Counter WITH x <- u, start <- bar + inst!val
Init == inst!Init

-----------------------------------------------------------------------
=======================================================================