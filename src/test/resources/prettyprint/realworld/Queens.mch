MACHINE Queens
CONSTANTS N
PROPERTIES
 N : INTEGER
 & N : NATURAL - {0}
DEFINITIONS
 Attacks(queens,i,j) == queens(i) = queens(j)
	 or queens(i) - queens(j) = i - j
	 or queens(j) - queens(i) = i - j;

 Init == todo = {[]}
	 & sols = {};

 nxtQ(queens) == size(queens) + 1;
 cols(queens) == {c|c : 1 .. N & not(#i.(i : 1 .. size(queens) & Attacks(queens <- c, i, nxtQ(queens))))};
 exts(queens) == {t_|#c.(c : cols(queens) & t_ = queens <- c)};
VARIABLES todo, sols
INVARIANT
 todo : POW(POW(INTEGER*INTEGER))
 & sols : POW(POW(INTEGER*INTEGER))
INITIALISATION
 todo, sols:(Init)
OPERATIONS
 PlaceQueen_Op(queens) = ANY todo_n, sols_n
	WHERE queens : todo & 
	 (nxtQ(queens) = N 
	  => todo_n = todo - {queens}
	  & sols_n = sols \/ exts(queens)) 
	 & (not(nxtQ(queens) = N) 
	  => todo_n = todo - {queens} \/ exts(queens)
	  & sols_n = sols)
	THEN todo, sols := todo_n, sols_n END
END