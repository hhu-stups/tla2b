MACHINE GraphIso
VARIABLES g1, g2, p, n, solved
INVARIANT
 g1 : POW(INTEGER*INTEGER)
 & g2 : POW(INTEGER*INTEGER)
 & p : POW(INTEGER*INTEGER)
 & n : INTEGER
 & solved : INTEGER
INITIALISATION
 g1, g2, p, n, solved:(n = 9
 & g1 = %i.(i : 1 .. n| i) <+ {1 |-> 3, 2 |-> 3, 3 |-> 6, 4 |-> 6, 5 |-> 6, 8 |-> 9, 9 |-> 8}
 & g2 = %i.(i : 1 .. n| i) <+ {2 |-> 5, 3 |-> 5, 4 |-> 5, 6 |-> 4, 7 |-> 4, 1 |-> 9, 9 |-> 1}
 & p = %i.(i : 1 .. n| 0)
 & solved = 0)
OPERATIONS
 Solve_Op = ANY p_n, solved_n
	WHERE p_n : POW(INTEGER*INTEGER) & solved_n : INTEGER & solved = 0
	 & solved_n = 1
	 & p_n : 1 .. n --> 1 .. n
	 & !i.(i : 1 .. n => #j.(j : 1 .. n & p_n(j) = i))
	 & !i.(i : 1 .. n => p_n(g1(i)) = g2(p_n(i)))
	 & TRUE = TRUE
	THEN p, solved := p_n, solved_n END
END
