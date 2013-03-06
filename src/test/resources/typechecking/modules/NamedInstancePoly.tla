-------------- MODULE NamedInstancePoly ----------------
VARIABLES c
count == INSTANCE Poly WITH x <- c
Init == count!foo = 1
=================================