------------------------------ MODULE Doors ------------------------------- 
EXTENDS Naturals
CONSTANTS DOOR, POSITION, open, closed
ASSUME POSITION = {open,closed}
VARIABLES position

Inv == position \in [DOOR -> POSITION]
Init == position = [x \in DOOR |-> closed] 

opening(dd)== dd \in DOOR /\ position' = [position EXCEPT ![dd] = open ]

closedoor(dd)== dd \in DOOR /\  position' =  [position EXCEPT ![dd] = closed ]

Next == \E dd \in DOOR : opening(dd) \/ closedoor(dd)
=============================================================================