----- MODULE AsynchInterface -----
EXTENDS Naturals
CONSTANTS Data
ASSUME Data = 0..7 (* added to avoid having to give Data a value in .cfg file *)
VARIABLES val, rdy, ack
TypeInvariant == /\ val \in Data
                 /\ rdy \in {0,1}
                 /\ ack \in {0,1}
----------------------
Init == /\ val \in Data
        /\ rdy \in {0,1}
        /\ ack = rdy
Snd  == /\ rdy=ack
        /\ val' \in Data
        /\ rdy' = 1-rdy
        /\ UNCHANGED ack
Rcv  == /\ rdy # ack
        /\ ack' = 1-ack
        /\ UNCHANGED <<val,rdy>>
Next == Snd \/ Rcv
Spec == Init /\ [] [Next]_<<val,rdy,ack>>
----------------------
THEOREM Spec => [] TypeInvariant  (* this defines the invariant; not yet automatically detected by TLA2B *)
=======================

