-------------------------- MODULE Counter -----------------------------
EXTENDS Naturals
CONSTANTS start
VARIABLE x
-----------------------------------------------------------------------
Init  ==  x = start
plus(a,b) == a +b
Next  ==  x' = plus(x,1)
=======================================================================
