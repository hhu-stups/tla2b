-------------- MODULE NamedInstancePoly2 ----------------
VARIABLES c
count == INSTANCE Poly WITH x <- c
Init == count!bar(1)
=================================