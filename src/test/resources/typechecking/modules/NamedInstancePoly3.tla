----------- MODULE NamedInstancePoly3 ----------------
VARIABLES c, c2
count == INSTANCE Poly WITH x <- c
count2 == INSTANCE Poly WITH x <- c2
foo == count!foo = TRUE
foo2 == count2!foo = 1
Init == foo /\ foo2
=================================