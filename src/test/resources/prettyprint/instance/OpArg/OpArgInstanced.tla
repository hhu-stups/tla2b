-------------- MODULE OpArgInstanced --------------
EXTENDS Naturals
VARIABLES c
foo(a,b) == a + b
INSTANCE OpArg WITH k <- foo
=================================