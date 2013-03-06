MACHINE InstanceCounter
DEFINITIONS
 prec(a, b) == a < b;

 val == 1
VARIABLES c
INVARIANT
 c : INTEGER
INITIALISATION
 c:(c = 0)
OPERATIONS
 Next_Op = ANY c_n
	WHERE c_n : INTEGER & prec(1, 2) & c_n = c + val
	THEN c := c_n END
END