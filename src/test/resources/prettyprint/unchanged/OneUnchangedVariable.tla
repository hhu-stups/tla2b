-----MODULE OneUnchangedVariable -----
VARIABLES a, b
Init == a= 0 /\ b = 0
Next == a = 1 /\ UNCHANGED b
=================================