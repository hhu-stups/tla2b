 ----- MODULE SeveralUnchangedVariables -----
VARIABLES a,b,c,d,e
Init == a= 0 /\ b = 0 /\ c = 0 /\ d = 0 /\ e = 0
Next == a = 1 /\ UNCHANGED <<b,c,d,e>>
=================================