MACHINE DieHarder
ABSTRACT_CONSTANTS Goal
PROPERTIES
 Goal = 4
 & MCCapacity : MCJug --> {n|n : NATURAL & n > 0}
 & Goal : NATURAL
DEFINITIONS
 IF_THEN_ELSE(P, a, b) == (%t_.(t_ = TRUE & P = TRUE | a )\/%t_.(t_= TRUE & not(P= TRUE) | b ))(TRUE);
 MCJug == {"j1", "j2"};

 MCCapacity == %j_1.(j_1 : MCJug| (%t_.(t_ = 0 & j_1 = "j1" | 3) \/ %t_.(t_ = 0 & j_1 = "j2" | 5))(0));

 Min(m,n) == IF_THEN_ELSE(bool(m < n), m, n);

 FillJug(j) == contents_n = contents <+ {j |-> MCCapacity(j)};

 EmptyJug(j) == contents_n = contents <+ {j |-> 0};

 amountPoured(j, k) == Min(contents(j), MCCapacity(k) - contents(k));
 JugToJug(j,k) == contents_n = contents <+ {j |-> contents(j) - amountPoured(j, k), k |-> contents(k) + amountPoured(j, k)};

 NotSolved == !j.(j : MCJug => contents(j) /= Goal)
VARIABLES contents
INVARIANT
 contents : POW(STRING*INTEGER)
 & NotSolved
INITIALISATION
 contents:(contents = %j.(j : MCJug| 0))
OPERATIONS
 FillJug_Op(j) = ANY contents_n
	WHERE j : MCJug & 
	 contents_n : POW(STRING*INTEGER) & FillJug(j)
	THEN contents := contents_n END;

 EmptyJug_Op(j) = ANY contents_n
	WHERE j : MCJug & 
	 contents_n : POW(STRING*INTEGER) & EmptyJug(j)
	THEN contents := contents_n END;

 JugToJug_Op(j, k) = ANY contents_n
	WHERE j : MCJug & k : MCJug - {j} & 
	 contents_n : POW(STRING*INTEGER) & JugToJug(j, k)
	THEN contents := contents_n END
END