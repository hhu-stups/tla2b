MACHINE overrides
CONSTANTS k
PROPERTIES
 k : INTEGER
 & k = foo
DEFINITIONS
 foo == 5;

VARIABLES c
INVARIANT
 c : INTEGER
INITIALISATION
 c:(c = 1)
OPERATIONS
 Next_Op = ANY c_n
	WHERE c_n = c + k
	THEN c := c_n END
END