MACHINE Jukebox
SETS
 ENUM1 = {t1, t2, t3}
ABSTRACT_CONSTANTS TRACK, limit
PROPERTIES
 TRACK = ENUM1
 & limit : INTEGER
 & limit : NATURAL & limit > 0
DEFINITIONS
 IF_THEN_ELSE(P, a, b) == (%t_.(t_ = TRUE & P = TRUE | a )\/%t_.(t_= TRUE & not(P= TRUE) | b ))(TRUE);
 Inv == credit : NATURAL & credit <= limit & playset <: TRACK;

 minimum(a,b) == IF_THEN_ELSE(bool(a < b), a, b);

 pay(cc) == cc > 0 & credit_n = minimum(credit + cc, limit);

 select(tt) == credit > 0 & (credit_n = credit - 1 or credit_n = credit) & playset_n = playset \/ {tt}
VARIABLES credit, playset
INVARIANT
 credit : INTEGER
 & playset : POW(ENUM1)
 & Inv
INITIALISATION
 credit, playset:(credit = 0 & playset = {})
OPERATIONS
 pay_Op(cc) = ANY credit_n, playset_n
	WHERE cc : NATURAL & 
	 credit_n : INTEGER & playset_n : POW(ENUM1) & pay(cc)
	THEN credit, playset := credit_n, playset_n END;

 select_Op(tt) = ANY credit_n, playset_n
	WHERE tt : TRACK & 
	 credit_n : INTEGER & playset_n : POW(ENUM1) & select(tt)
	THEN credit, playset := credit_n, playset_n END;

 play_Op = ANY playset_n
	WHERE playset_n : POW(ENUM1) & playset /= {} & #tr.(tr : playset & playset_n = playset - {tr}) & TRUE = TRUE
	THEN playset := playset_n END;

 removeCredit_Op = ANY credit_n
	WHERE credit_n : INTEGER & credit > 0 & credit_n = credit - 1 & TRUE = TRUE
	THEN credit := credit_n END;

 dropTrack_Op(tt) = ANY playset_n
	WHERE tt : playset & 
	 playset_n : POW(ENUM1) & playset_n = playset - {tt} & TRUE = TRUE
	THEN playset := playset_n END
END
