-------------- MODULE TwoInstanced --------------
CONSTANTS start
VARIABLES c, c2
count == INSTANCE Counter WITH x <- c
count2 == INSTANCE Counter WITH x <- c2, start <- 0
Init == count!Init /\ count2!Init
Next == 	\/ (count!Next /\ UNCHANGED c2)
			\/ (count2!Next /\ UNCHANGED c)
=================================