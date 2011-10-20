---------------------------- MODULE Main -------------------------------
EXTENDS Naturals
CONSTANTS start
VARIABLES x
First == INSTANCE FirstInstance WITH x <- x, start <- start
-----------------------------------------------------------------------------
Init == First!Init
Next == First!Next
=============================================================================

