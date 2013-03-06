-------------- MODULE InstanceCounter ----------------
EXTENDS Naturals
VARIABLES c
a \prec b == a < b
INSTANCE Counter WITH x <- c, start <- 0, \prec <- \prec
=================================