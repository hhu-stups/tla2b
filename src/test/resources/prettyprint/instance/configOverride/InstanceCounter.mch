MACHINE InstanceCounter
ABSTRACT_CONSTANTS start
PROPERTIES
 start : INTEGER
DEFINITIONS
 val == 4
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
