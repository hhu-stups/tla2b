MACHINE Club
SETS
 ENUM1 = {n1, n2, n3}
ABSTRACT_CONSTANTS capacity, NAME, total
PROPERTIES
 capacity : INTEGER
 & NAME = ENUM1
 & total : INTEGER
 & capacity : NATURAL & capacity = 2
 & card(NAME) > capacity
 & total : NATURAL & total > 2
DEFINITIONS
 join_queue(nn) == nn /: member & nn /: waiting & card(waiting) < total & waiting_n = waiting \/ {nn} & TRUE = TRUE;

 join(nn) == nn : waiting & card(member) < capacity & member_n = member \/ {nn} & waiting_n = waiting - {nn};

 remove(nn) == nn : member & member_n = member - {nn} & TRUE = TRUE
VARIABLES member, waiting
INVARIANT
 member : POW(ENUM1)
 & waiting : POW(ENUM1)
INITIALISATION
 member, waiting:(member = {} & waiting = {})
OPERATIONS
 join_queue_Op(nn) = ANY waiting_n
	WHERE nn : NAME & 
	 waiting_n : POW(ENUM1) & join_queue(nn)
	THEN waiting := waiting_n END;

 join_Op(nn) = ANY member_n, waiting_n
	WHERE nn : NAME & 
	 member_n : POW(ENUM1) & waiting_n : POW(ENUM1) & join(nn)
	THEN member, waiting := member_n, waiting_n END;

 remove_Op(nn) = ANY member_n
	WHERE nn : NAME & 
	 member_n : POW(ENUM1) & remove(nn)
	THEN member := member_n END
END
