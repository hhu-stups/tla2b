-------------- MODULE NamedInstancePoly4 ----------------
CONSTANTS k
VARIABLES c
poly == INSTANCE Poly WITH x <- c
Init == poly!foo = TRUE
ASSUME poly!baz(1,k)
=================================