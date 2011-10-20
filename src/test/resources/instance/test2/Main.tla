---------------------------- MODULE Main -------------------------------
EXTENDS Naturals
CONSTANTS k
VARIABLES c 
INSTANCE FirstInstance WITH x <- c, start <- 1

-----------------------------------------------------------------------------
Inv == c \in Nat /\ k \in Nat 
Init == Init1

Next == Next1 
=============================================================================

