MACHINE OpArgInstanced
DEFINITIONS
 foo(a,b) == a + b;

VARIABLES c
INVARIANT
 c : INTEGER
INITIALISATION
 c:(c = 1)
OPERATIONS
 Next_Op = ANY c_n
	WHERE c_n : INTEGER & c_n = c + foo(1,2)
	THEN c := c_n END
END