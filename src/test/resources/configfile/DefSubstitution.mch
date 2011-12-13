MACHINE DefSubstitution
DEFINITIONS
 foo == 1;

VARIABLES c
INVARIANT
 c : INTEGER
INITIALISATION
 c:(c = 1)
OPERATIONS
 Next_Op = ANY c_n
	WHERE c_n = c + foo
	THEN c := c_n END
END
