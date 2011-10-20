---------------------------- MODULE Main -------------------------------
EXTENDS Naturals
CONSTANTS start
VARIABLES x
count == INSTANCE Counter WITH x <- x, start <- start
-----------------------------------------------------------------------------
Init == count!Init
Next ==  count!Next 
=============================================================================

