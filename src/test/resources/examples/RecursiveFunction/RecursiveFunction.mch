MACHINE RecursiveFunction
ABSTRACT_CONSTANTS k, k2, k3, fact
PROPERTIES
 k : INTEGER
 & k2 : INTEGER
 & k3 : INTEGER
 & k = fact(0) & k2 = fact(3) & k3 = fact(4)
 & fact = %n.(n : NATURAL & n = 0 | 1) \/ %n.(n : NATURAL & not(n = 0) | n * fact(n - 1))
DEFINITIONS
 IF_THEN_ELSE(P, a, b) == (%t_.(t_ = TRUE & P = TRUE | a )\/%t_.(t_= TRUE & not(P= TRUE) | b ))(TRUE)
END
