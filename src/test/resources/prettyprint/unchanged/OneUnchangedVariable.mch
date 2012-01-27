MACHINE OneUnchangedVariable
VARIABLES a, b
INVARIANT
 a : INTEGER
 & b : INTEGER
INITIALISATION
 a, b:(a = 0 & b = 0)
OPERATIONS
 Next_Op = ANY a_n
	WHERE a_n : INTEGER & a = 1 & TRUE = TRUE
	THEN a := a_n END
END