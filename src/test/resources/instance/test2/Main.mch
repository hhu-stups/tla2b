MACHINE Main
CONSTANTS k
PROPERTIES
 k : INTEGER
VARIABLES c
DEFINITIONS
 Next1 == c_n = c + 1;
 Init1 == c = 1;
 Inv == c : NATURAL & k : NATURAL;
 Init == Init1;
INVARIANT
 c :INTEGER
INITIALISATION
 c:(Init)
OPERATIONS
 Next1Op = ANY c_n
	WHERE Next1
	THEN c := c_n END
END