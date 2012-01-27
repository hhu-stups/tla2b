MACHINE SeveralUnchangedVariables
VARIABLES a, b, c, d, e
INVARIANT
 a : INTEGER
 & b : INTEGER
 & c : INTEGER
 & d : INTEGER
 & e : INTEGER
INITIALISATION
 a, b, c, d, e:(a = 0 & b = 0 & c = 0 & d = 0 & e = 0)
OPERATIONS
 Next_Op = ANY a_n
	WHERE a_n : INTEGER & a = 1 & TRUE = TRUE
	THEN a := a_n END
END