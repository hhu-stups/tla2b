MACHINE ExtendsCounter
ABSTRACT_CONSTANTS start
PROPERTIES
 start = 2
DEFINITIONS
 val == 1
VARIABLES x
INVARIANT
 x : INTEGER
INITIALISATION
 x:(x = start)
OPERATIONS
 Next_Op = ANY x_n
	WHERE x_n : INTEGER & x_n = x + val
	THEN x := x_n END
END