-------------------------- MODULE Counter -----------------------------
EXTENDS Naturals
CONSTANTS start, _\prec_
VARIABLE x
-----------------------------------------------------------------------
Init  ==  x = start
val == 1
Next  ==  1 \prec 2 /\  x' = x + val
=======================================================================