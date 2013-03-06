-------------- MODULE InstanceLet ----------------
VARIABLES c, c2
inst == INSTANCE Let WITH x <- c
inst2 == INSTANCE Let WITH x <- c2
Init == inst!Init /\ inst2!Init
Next == inst!Next /\ inst2!Next
=================================