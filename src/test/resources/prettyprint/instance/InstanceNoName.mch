MACHINE InstanceNoName
ABSTRACT_CONSTANTS start
PROPERTIES
 start : INTEGER
DEFINITIONS
 Init == c = start;

 val == 1
VARIABLES c
INVARIANT
 c : INTEGER
INITIALISATION
 c:(Init)
OPERATIONS
 Next_Op = ANY c_n
	WHERE c_n : INTEGER & c_n = c + val
	THEN c := c_n END
END