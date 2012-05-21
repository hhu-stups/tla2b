MACHINE Counter
ABSTRACT_CONSTANTS k
PROPERTIES
 k = 10
VARIABLES a
INVARIANT
 a : INTEGER
INITIALISATION
 a:(a = 0)
OPERATIONS
 Inc_Op = ANY a_n
	WHERE a_n : INTEGER & a < k & a_n = a + 1
	THEN a := a_n END;

 Dec_Op = ANY a_n
	WHERE a_n : INTEGER & a > 0 & a_n = a - 1
	THEN a := a_n END
END
