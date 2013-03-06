MACHINE InstanceLet
DEFINITIONS
 inst_Init == c = 1;

 inst_val == 4;

 inst_foo(p) == 1 + e + p;
 inst_Next == #e.(e : {1, 2} & c_n = c + inst_foo(3) + inst_val);

 inst2_Init == c2 = 1;

 inst2_val == 4;

 inst2_foo(p) == 1 + e + p;
 inst2_Next == #e.(e : {1, 2} & c2_n = c2 + inst2_foo(3) + inst2_val)
VARIABLES c, c2
INVARIANT
 c : INTEGER
 & c2 : INTEGER
INITIALISATION
 c, c2:(inst_Init & inst2_Init)
OPERATIONS
 Next_Op = ANY c_n, c2_n
	WHERE c_n : INTEGER & c2_n : INTEGER & inst_Next & inst2_Next
	THEN c, c2 := c_n, c2_n END
END
