MACHINE Main
CONSTANTS start
PROPERTIES
 start : INTEGER
VARIABLES x
DEFINITIONS
 count_Next == x_n = count_plus(x, 1);
 count_Init == x = start;
 count_plus(a,b) == a + b;
 Init == count_Init;
INVARIANT
 x :INTEGER
INITIALISATION
 x:(Init)
OPERATIONS
 count_NextOp = ANY x_n
	WHERE count_Next
	THEN x := x_n END
END