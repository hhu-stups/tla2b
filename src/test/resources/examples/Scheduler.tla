------------------------------ MODULE Scheduler ------------------------------- 
EXTENDS Naturals, FiniteSets
CONSTANTS PID
VARIABLES active, ready, waiting
Inv == active \in SUBSET(PID) /\ ready \in SUBSET(PID) /\ waiting \in SUBSET(PID)
	 /\ active \subseteq PID /\ ready \subseteq PID /\ waiting \subseteq PID
	/\ (ready \cap waiting) = {} /\ Cardinality(active) \leq 1
	/\ (active = {} => ready = {})
Init == active = {} /\ ready = {} /\ waiting = {}
------------------------------------------------------------------------------
new(pp) == pp \notin active /\ pp \notin (ready \cup waiting) /\ waiting' = waiting \cup {pp} /\ UNCHANGED <<ready,active>>

del(pp) == pp \in waiting /\ waiting' = waiting\{pp} /\ UNCHANGED <<ready,active>>

ready_(rr) == rr \in waiting /\ waiting' =  waiting\{rr} /\
	IF active = {} THEN active' = {rr} /\ UNCHANGED ready
	ELSE ready' = ready \cup {rr} /\ UNCHANGED active

swap == active # {} /\ waiting' = waiting \cup active 
	/\ IF ready = {} THEN active' = {} /\ UNCHANGED ready
	ELSE \E pp \in ready: active' ={pp} /\ ready' = ready\{pp}



Next ==  \/ (\E pp \in PID : new(pp))
	\/ (\E pp \in PID : del(pp))
	\/ (\E rr \in PID : ready_(rr))
	\/ swap
=============================================================================
