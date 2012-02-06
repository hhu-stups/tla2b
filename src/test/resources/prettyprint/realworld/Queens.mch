MACHINE Queens
ABSTRACT_CONSTANTS N
PROPERTIES
 N : INTEGER
 & N : NATURAL - {0}
DEFINITIONS
 Attacks(queens,i,j) == queens(i) = queens(j)
	 or queens(i) - queens(j) = i - j
	 or queens(j) - queens(i) = i - j;

 Init == todo = {[]}
	 & sols = {};

 nxtQ == size(queens) + 1;
 cols == {c|c : 1 .. N & not(#i.(i : 1 .. size(queens) & Attacks(queens <- c, i, nxtQ)))};
 exts == {t_|#c.(c : cols & t_ = queens <- c)}
VARIABLES todo, sols
INVARIANT
 todo : POW(POW(INTEGER*INTEGER))
 & sols : POW(POW(INTEGER*INTEGER))
INITIALISATION
 todo, sols:(Init)
OPERATIONS
 PlaceQueen_Op(queens) = ANY todo_n, sols_n
	WHERE queens : todo & 
	 todo_n : POW(POW(INTEGER*INTEGER)) & sols_n : POW(POW(INTEGER*INTEGER)) & (nxtQ = N 
	  => todo_n = todo - {queens}
	  & sols_n = sols \/ exts) 
	 & (not(nxtQ = N) 
	  => todo_n = todo - {queens} \/ exts
	  & sols_n = sols)
	THEN todo, sols := todo_n, sols_n END
END