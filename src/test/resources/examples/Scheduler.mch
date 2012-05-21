MACHINE Scheduler
SETS
 ENUM1 = {p1, p2, p3, p4, p5, p6, p7}
ABSTRACT_CONSTANTS PID
PROPERTIES
 PID = ENUM1
DEFINITIONS
 Inv == active : POW(PID) & ready : POW(PID) & waiting : POW(PID) & active <: PID & ready <: PID & waiting <: PID & ready /\ waiting = {} & card(active) <= 1 & (active = {} => ready = {});

 new(pp) == pp /: active & pp /: ready \/ waiting & waiting_n = waiting \/ {pp} & TRUE = TRUE;

 del(pp) == pp : waiting & waiting_n = waiting - {pp} & TRUE = TRUE;

 ready_(rr) == rr : waiting & waiting_n = waiting - {rr} & ((active = {} 
	  => active_n = {rr} & ready_n = ready) 
	 & (not(active = {}) 
	  => ready_n = ready \/ {rr} & active_n = active))
VARIABLES active, ready, waiting
INVARIANT
 active : POW(ENUM1)
 & ready : POW(ENUM1)
 & waiting : POW(ENUM1)
 & Inv
INITIALISATION
 active, ready, waiting:(active = {} & ready = {} & waiting = {})
OPERATIONS
 new_Op(pp) = ANY waiting_n
	WHERE pp : PID & 
	 waiting_n : POW(ENUM1) & new(pp)
	THEN waiting := waiting_n END;

 del_Op(pp) = ANY waiting_n
	WHERE pp : PID & 
	 waiting_n : POW(ENUM1) & del(pp)
	THEN waiting := waiting_n END;

 ready__Op(rr) = ANY active_n, ready_n, waiting_n
	WHERE rr : PID & 
	 active_n : POW(ENUM1) & ready_n : POW(ENUM1) & waiting_n : POW(ENUM1) & ready_(rr)
	THEN active, ready, waiting := active_n, ready_n, waiting_n END;

 swap_Op = ANY active_n, ready_n, waiting_n
	WHERE active_n : POW(ENUM1) & ready_n : POW(ENUM1) & waiting_n : POW(ENUM1) & active /= {} & waiting_n = waiting \/ active & ((ready = {} 
	  => active_n = {} & ready_n = ready) 
	 & (not(ready = {}) 
	  => #pp.(pp : ready & (active_n = {pp} & ready_n = ready - {pp}))))
	THEN active, ready, waiting := active_n, ready_n, waiting_n END
END
