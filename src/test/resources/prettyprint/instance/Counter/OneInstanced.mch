MACHINE OneInstanced
ABSTRACT_CONSTANTS start
PROPERTIES
 start : INTEGER
DEFINITIONS
 count_Init == c = start;

 count_val == 1;

VARIABLES c
INVARIANT
 c : INTEGER
INITIALISATION
 c:(count_Init)
OPERATIONS
 count_Next_Op = ANY c_n
	WHERE c_n : INTEGER & c_n = c + count_val
	THEN c := c_n END
END