MACHINE DefOverriding
DEFINITIONS
 foo2 == 6;

VARIABLES c
INVARIANT
 c : INTEGER
INITIALISATION
 c:(c = 1)
OPERATIONS
 Next_Op = ANY c_n
	WHERE c_n : INTEGER & c_n = foo2
	THEN c := c_n END
END