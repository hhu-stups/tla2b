-------------- MODULE InstanceNoName ----------------
CONSTANTS start
VARIABLES c
INSTANCE Counter WITH x <- c
Spec == Init /\ [][Next]_c
=================================