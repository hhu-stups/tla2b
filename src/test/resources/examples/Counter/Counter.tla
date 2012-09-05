------------------------------ MODULE Counter ------------------------------- 
EXTENDS Naturals
CONSTANTS k

VARIABLES a

Init == a = 0

Inc ==  a < k /\ a' = a+1
Dec == a > 0 /\ a' = a-1
Next == Inc \/ Dec

=============================================================================