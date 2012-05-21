MACHINE AsynchInterface
ABSTRACT_CONSTANTS Data
PROPERTIES
 Data : POW(INTEGER)
 & Data = 0 .. 7
DEFINITIONS
 TypeInvariant == val : Data
	 & rdy : {0, 1}
	 & ack : {0, 1}
VARIABLES val, rdy, ack
INVARIANT
 val : INTEGER
 & rdy : INTEGER
 & ack : INTEGER
 & TypeInvariant
INITIALISATION
 val, rdy, ack:(val : Data
 & rdy : {0, 1}
 & ack = rdy)
OPERATIONS
 Snd_Op = ANY val_n, rdy_n
	WHERE val_n : INTEGER & rdy_n : INTEGER & rdy = ack
	 & val_n : Data
	 & rdy_n = 1 - rdy
	 & TRUE = TRUE
	THEN val, rdy := val_n, rdy_n END;

 Rcv_Op = ANY ack_n
	WHERE ack_n : INTEGER & rdy /= ack
	 & ack_n = 1 - ack
	 & TRUE = TRUE
	THEN ack := ack_n END
END
