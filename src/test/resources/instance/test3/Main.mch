MACHINE Main
CONSTANTS start
PROPERTIES
 start : INTEGER
VARIABLES x
DEFINITIONS
 First_Next == x_n = First_plus(x, 1);
 First_Init == x = start;
 First_plus(a,b) == a + b;
 Init == First_Init;
INVARIANT
 x :INTEGER
INITIALISATION
 x:(Init)
OPERATIONS
 First_NextOp = ANY x_n
	WHERE First_Next
	THEN x := x_n END
END
