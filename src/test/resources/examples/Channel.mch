MACHINE Channel
SETS
 ENUM1 = {d1, d2}
ABSTRACT_CONSTANTS Data
PROPERTIES
 Data = ENUM1
DEFINITIONS
 TypeInvariant == chan : struct(ack : {0, 1},val : Data,rdy : {0, 1});

 Send(d) == chan'rdy = chan'ack
	 & chan_n = rec(ack : chan'ack, val : d, rdy : 1 - chan'rdy)
VARIABLES chan
INVARIANT
 chan : struct(ack:INTEGER,val:ENUM1,rdy:INTEGER)
 & TypeInvariant
INITIALISATION
 chan:(TypeInvariant
 & chan'ack = chan'rdy)
OPERATIONS
 Send_Op(d) = ANY chan_n
	WHERE d : Data & 
	 chan_n : struct(ack:INTEGER,val:ENUM1,rdy:INTEGER) & Send(d)
	THEN chan := chan_n END;

 Rcv_Op = ANY chan_n
	WHERE chan_n : struct(ack:INTEGER,val:ENUM1,rdy:INTEGER) & chan'rdy /= chan'ack
	 & chan_n = rec(ack : 1 - chan'ack, val : chan'val, rdy : chan'rdy)
	THEN chan := chan_n END
END
