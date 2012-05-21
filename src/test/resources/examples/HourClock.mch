MACHINE HourClock
DEFINITIONS
 IF_THEN_ELSE(P, a, b) == (%t_.(t_ = TRUE & P = TRUE | a )\/%t_.(t_= TRUE & not(P= TRUE) | b ))(TRUE);
 HCini == hr : 1 .. 12
VARIABLES hr
INVARIANT
 hr : INTEGER
 & HCini
INITIALISATION
 hr:(hr : 1 .. 12)
OPERATIONS
 HCnxt_Op = ANY hr_n
	WHERE hr_n : INTEGER & hr_n = IF_THEN_ELSE(bool(hr /= 12), hr + 1, 1)
	THEN hr := hr_n END
END
