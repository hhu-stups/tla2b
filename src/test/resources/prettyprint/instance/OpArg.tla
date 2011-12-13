-------------- MODULE OpArg ----------------
EXTENDS Naturals
CONSTANTS k(_,_)
VARIABLES c
Init == c = 1 
Next == c' = c + k(1, 2)
=================================