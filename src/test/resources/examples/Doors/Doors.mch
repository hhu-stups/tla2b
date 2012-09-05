MACHINE Doors
SETS
 ENUM1 = {D1, D2, D3}; ENUM2 = {open, closed}
ABSTRACT_CONSTANTS DOOR, POSITION
PROPERTIES
 DOOR = ENUM1
 & POSITION : POW(ENUM2)
 & POSITION = {open, closed}
DEFINITIONS
 Inv == position : DOOR --> POSITION;

 opening(dd) == dd : DOOR & position_n = position <+ {dd |-> open};

 closedoor(dd) == dd : DOOR & position_n = position <+ {dd |-> closed}
VARIABLES position
INVARIANT
 position : POW(ENUM1*ENUM2)
 & Inv
INITIALISATION
 position:(position = %x.(x : DOOR| closed))
OPERATIONS
 opening_Op(dd) = ANY position_n
	WHERE dd : DOOR & 
	 position_n : POW(ENUM1*ENUM2) & opening(dd)
	THEN position := position_n END;

 closedoor_Op(dd) = ANY position_n
	WHERE dd : DOOR & 
	 position_n : POW(ENUM1*ENUM2) & closedoor(dd)
	THEN position := position_n END
END
