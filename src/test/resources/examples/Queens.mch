MACHINE Queens
VARIABLES q, n, solved
INVARIANT
 q : POW(INTEGER*INTEGER)
 & n : INTEGER
 & solved : INTEGER
INITIALISATION
 q, n, solved:(q = %i.(i : 1 .. 2| 0)
 & n = 7
 & solved = 0)
OPERATIONS
 Solve_Op = ANY q_n, n_n, solved_n
	WHERE q_n : POW(INTEGER*INTEGER) & n_n : INTEGER & solved_n : INTEGER & solved = 0
	 & q_n : 1 .. n --> 1 .. n
	 & !i.(i : 1 .. n => !j.(j : 2 .. n => (i < j => q_n(i) /= q_n(j) & q_n(i) + (i - j) /= q_n(j) & q_n(i) - i + j /= q_n(j))))
	 & solved_n = 1
	 & n_n = n
	THEN q, n, solved := q_n, n_n, solved_n END
END
