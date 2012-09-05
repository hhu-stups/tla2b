MACHINE DieHard
DEFINITIONS
 IF_THEN_ELSE(P, a, b) == (%t_.(t_ = TRUE & P = TRUE | a )\/%t_.(t_= TRUE & not(P= TRUE) | b ))(TRUE);
 TypeOK == small : 0 .. 3
	 & big : 0 .. 5;

 Min(m,n) == IF_THEN_ELSE(bool(m < n), m, n);

 NotSolved == big /= 4
VARIABLES big, small
INVARIANT
 big : INTEGER
 & small : INTEGER
 & TypeOK
 & NotSolved
INITIALISATION
 big, small:(big = 0
 & small = 0)
OPERATIONS
 FillSmallJug_Op = ANY big_n, small_n
	WHERE big_n : INTEGER & small_n : INTEGER & small_n = 3
	 & big_n = big
	THEN big, small := big_n, small_n END;

 FillBigJug_Op = ANY big_n, small_n
	WHERE big_n : INTEGER & small_n : INTEGER & big_n = 5
	 & small_n = small
	THEN big, small := big_n, small_n END;

 EmptySmallJug_Op = ANY big_n, small_n
	WHERE big_n : INTEGER & small_n : INTEGER & small_n = 0
	 & big_n = big
	THEN big, small := big_n, small_n END;

 EmptyBigJug_Op = ANY big_n, small_n
	WHERE big_n : INTEGER & small_n : INTEGER & big_n = 0
	 & small_n = small
	THEN big, small := big_n, small_n END;

 SmallToBig_Op = ANY big_n, small_n
	WHERE big_n : INTEGER & small_n : INTEGER & big_n = Min(big + small, 5)
	 & small_n = small - (big_n - big)
	THEN big, small := big_n, small_n END;

 BigToSmall_Op = ANY big_n, small_n
	WHERE big_n : INTEGER & small_n : INTEGER & small_n = Min(big + small, 3)
	 & big_n = big - (small_n - small)
	THEN big, small := big_n, small_n END
END
