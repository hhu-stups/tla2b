MACHINE ModConstantAssignment
DEFINITIONS
 val == 7
VARIABLES c
INVARIANT
 c : INTEGER
INITIALISATION
 c:(c = 0)
OPERATIONS
 Next_Op = ANY c_n
	WHERE c_n : INTEGER & c_n = c + val
	THEN c := c_n END
END
