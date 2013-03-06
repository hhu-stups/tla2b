MACHINE SimpleSATProblem
ABSTRACT_CONSTANTS x1, x2, x3, x4, x5, x6, x7
PROPERTIES
 x1 : BOOL
 & x2 : BOOL
 & x3 : BOOL
 & x4 : BOOL
 & x5 : BOOL
 & x6 : BOOL
 & x7 : BOOL
 & x1 : BOOL & x2 : BOOL & x3 : BOOL
 & (x4 : BOOL & x5 : BOOL & x6 : BOOL & x7 : BOOL)
 & (x1 = TRUE or x2 = TRUE or x5 = TRUE or x4 = TRUE)
 & (x1 = TRUE or x2 = TRUE or not(x5 = TRUE) or x4 = TRUE)
 & (x3 = TRUE or x6 = TRUE)
 & (not(x4 = TRUE) or x7 = TRUE or x1 = TRUE)
 & (not(x4 = TRUE) or not(x7 = TRUE) or x2 = TRUE)
VARIABLES r
INVARIANT
 r : BOOL*BOOL*BOOL*BOOL*BOOL*BOOL*BOOL
INITIALISATION
 r:(r = (TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE))
OPERATIONS
 Set_Op = ANY r_n
	WHERE r_n : BOOL*BOOL*BOOL*BOOL*BOOL*BOOL*BOOL & r_n = (x1, x2, x3, x4, x5, x6, x7)
	THEN r := r_n END
END
