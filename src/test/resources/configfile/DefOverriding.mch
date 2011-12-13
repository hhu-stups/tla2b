MACHINE DefOverriding
DEFINITIONS
 foo == foo2;

 foo2 == 6;

VARIABLES c
INVARIANT
 c : INTEGER
INITIALISATION
 c:(c = 1)
OPERATIONS
 Next_Op = ANY c_n
	WHERE c_n = foo
	THEN c := c_n END
END