MACHINE Channel
SETS
 ENUM1 = {d1, d2}
ABSTRACT_CONSTANTS Data
PROPERTIES
 Data = ENUM1
DEFINITIONS
 TypeInvariant == chan : struct(ack : {0, 1},rdy : {0, 1},val : Data);

 Send(d) == chan'rdy = chan'ack
	 & chan_n = rec(ack : chan'ack, rdy : 1 - chan'rdy, val : d)
VARIABLES chan
INVARIANT
 chan : struct(ack:INTEGER,rdy:INTEGER,val:ENUM1)
 & TypeInvariant
INITIALISATION
 chan:(TypeInvariant
 & chan'ack = chan'rdy)
OPERATIONS
 Send_Op(d) = ANY chan_n
	WHERE d : Data & 
	 chan_n : struct(ack:INTEGER,rdy:INTEGER,val:ENUM1) & Send(d)
	THEN chan := chan_n END;

 Rcv_Op = ANY chan_n
	WHERE chan_n : struct(ack:INTEGER,rdy:INTEGER,val:ENUM1) & chan'rdy /= chan'ack
	 & chan_n = rec(ack : 1 - chan'ack, rdy : chan'rdy, val : chan'val)
	THEN chan := chan_n END
END
