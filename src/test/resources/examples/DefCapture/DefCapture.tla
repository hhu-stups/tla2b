-------------------------------- MODULE DefCapture --------------------------------
EXTENDS Naturals

Double(y) == \E x \in 1..10 :(x+x=y)

NotDouble(y) == \neg Double(y)

ASSUME Double(2)

ASSUME NotDouble(3)

ASSUME {x \in {2,3} : NotDouble(x)} = {3}

=======================

