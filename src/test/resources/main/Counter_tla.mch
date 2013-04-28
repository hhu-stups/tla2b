/*@ generated TLA2B 1.0.7 Sun Apr 28 11:05:36 CEST 2013 */
MACHINE Counter
ABSTRACT_CONSTANTS start
PROPERTIES
 start : INTEGER
VARIABLES x
INVARIANT
 x : INTEGER
INITIALISATION
 x:(x = start)
OPERATIONS
 Inc_Op = ANY x_n
	WHERE x_n : INTEGER & x_n = x + 1
	THEN x := x_n END;

 Dec_Op = ANY x_n
	WHERE x_n : INTEGER & x_n = x - 1
	THEN x := x_n END
END