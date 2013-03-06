-------------- MODULE NamedInstanceCounter ----------------
CONSTANTS start
VARIABLES c
count == INSTANCE Counter WITH x <- c
Init == count!Init
Next == count!Next
=================================