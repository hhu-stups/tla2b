-------------------------- MODULE Jukebox -----------------------------
EXTENDS Naturals
CONSTANT TRACK, limit
ASSUME limit \in Nat /\ limit > 0

VARIABLE credit, playset
Init == credit = 0 /\ playset = {}
Inv  ==  credit \in Nat /\ credit \leq limit /\ playset \subseteq TRACK
-----------------------------------------------------------------------

(* A user can purchase some credits to make some selections from the
jukebox. The limit cannot be exceeded.  *)

minimum(a,b) == IF a < b THEN a ELSE b
pay(cc) ==  cc > 0 /\ credit' = minimum(credit + cc, limit)


(* The select action occasionally provides free selections.  The
intention is that this should occur occasionally, and randomly.  Note that even a free selection can only be made if the credit total is positive. *)

select(tt) == credit > 0 /\ (credit' = credit - 1 \/ credit' = credit)
	 /\ playset' = playset \cup {tt}


(* Any track that is currently in the set to be played can be output
by this action. *)

play == playset # {} /\ (\E tr \in playset: playset' = playset\{tr}) /\ UNCHANGED credit


(* the penalty action, invoked when the jukebox is mistreated,
either removes a credit if there are any left, or drops a tack from
the playset, if there are any left.  If both are possible, then it can
do either of these.*)

removeCredit == credit > 0 /\ credit' = credit -1 /\ UNCHANGED playset
dropTrack == \E tt \in playset: playset' = playset\{tt} /\ UNCHANGED credit
penalty == removeCredit \/ dropTrack


(* Disjunction of all actions *)

Next == \/ (\E cc \in Nat: pay(cc))
	\/ (\E tt \in TRACK: select(tt))
	\/ play
	\/ penalty

=======================================================================
