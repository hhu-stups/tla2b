MACHINE ConfigFile
DEFINITIONS
 Inv == c : NATURAL;

VARIABLES c
INVARIANT
 c : INTEGER
 & Inv
INITIALISATION
 c:(c = 1)
OPERATIONS
 Next_Op = ANY c_n
	WHERE c_n = c + 1
	THEN c := c_n END
END