MACHINE Channel
SETS
 ENUM1 = {d1, d2}
ABSTRACT_CONSTANTS Data
PROPERTIES
 Data = ENUM1
DEFINITIONS
 TypeInvariant == chan : struct(val : Data,rdy : {0, 1},ack : {0, 1});

 Send(d) == chan'rdy = chan'ack
	 & chan_n = rec(val : d, rdy : 1 - chan'rdy, ack : chan'ack)
VARIABLES chan
INVARIANT
 chan : struct(val:ENUM1,rdy:INTEGER,ack:INTEGER)
 & TypeInvariant
INITIALISATION
 chan:(TypeInvariant
 & chan'ack = chan'rdy)
OPERATIONS
 Send_Op(d) = ANY chan_n
	WHERE d : Data & 
	 chan_n : struct(val:ENUM1,rdy:INTEGER,ack:INTEGER) & Send(d)
	THEN chan := chan_n END;

 Rcv_Op = ANY chan_n
	WHERE chan_n : struct(val:ENUM1,rdy:INTEGER,ack:INTEGER) & chan'rdy /= chan'ack
	 & chan_n = rec(val : chan'val, rdy : chan'rdy, ack : 1 - chan'ack)
	THEN chan := chan_n END
END

