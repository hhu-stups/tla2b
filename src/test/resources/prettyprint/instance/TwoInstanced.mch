MACHINE TwoInstanced
ABSTRACT_CONSTANTS start
PROPERTIES
 start : INTEGER
DEFINITIONS
 count_Init == c = start;

 count_val == 1;

 count_Next == c_n = c + count_val;

 count2_Init == c2 = 0;

 count2_val == 1;

 count2_Next == c2_n = c2 + count2_val;

VARIABLES c, c2
INVARIANT
 c : INTEGER
 & c2 : INTEGER
INITIALISATION
 c, c2:(count_Init & count2_Init)
OPERATIONS
 Next1_Op = ANY c_n
	WHERE c_n : INTEGER & count_Next & TRUE = TRUE
	THEN c := c_n END;

 Next2_Op = ANY c2_n
	WHERE c2_n : INTEGER & count2_Next & TRUE = TRUE
	THEN c2 := c2_n END
END
