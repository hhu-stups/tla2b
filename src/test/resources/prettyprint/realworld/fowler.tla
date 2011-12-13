---------------------------- MODULE fowler ------------------------------------
(*****************************************************************************)
(* Controller of the secret compartment of Mrs. H, who loves secrets!        *)
(* Following the example of M. Fowler,                                       *)
(* which can be found at: `^http://martinfowler.com/^'                       *)
(*****************************************************************************)

(*****************************************************************************)
(* Variables                                                                 *)
(*****************************************************************************)
VARIABLE 
  state, \* the state for display, only to be compliant with Fowler 
  light, \* state of the light     
  draw,  \* state of the draw
  panel, \* state of the secret panel
  door   \* state of the entry door

(*****************************************************************************)
(* Type invariance                                                           *)
(*****************************************************************************)
TypeInv == 
  /\ state \in { "idle", "active", "waitingForDraw", 
                 "waitingForLight", "unlockedPanel" }
  /\ light \in { "on", "off" }
  /\ draw \in { "opened", "closed" }
  /\ door \in { "locked", "unlocked"}
  /\ panel \in { "locked", "unlocked" }
(*****************************************************************************)
(* Initial state                                                             *)
(*****************************************************************************)
Init == 
  /\ state = "idle"
  /\ light = "off"
  /\ draw  = "closed"
  /\ door  = "unlocked"
  /\ panel = "locked"
------------------------------------------------------------------------------- 
(*****************************************************************************)
(* Action definition.                                                        *)
(* Note that the state variable is not                                       *)
(* used for the determination of the                                         *)
(* actual state, but only for display.                                       *)
(* This shows that this variable                                             *)
(* is not required in TLA+                                                   *)
(*****************************************************************************)
  
(*****************************************************************************)
(* Closes the door, to activate                                              *)
(*****************************************************************************)
CloseDoor == 
  /\ door = "unlocked"
  /\ door' = "locked"
  /\ state' = "active"
  /\ UNCHANGED << panel, light, draw >>
(*****************************************************************************)
(* Switch on the light, if the draw is                                       *)
(* opened, this opens the secret panel                                       *)
(*****************************************************************************)
LightOn == 
  /\ light = "off"
  /\ light' = "on"
  /\ IF draw = "opened" THEN 
       /\ state' = "unlockedPanel"
	   /\ panel' = "unlocked"
	   /\ door' = "locked"
	 ELSE 
	   /\ state' = "waitingForDraw"
	   /\ UNCHANGED << panel, door >>
  /\ UNCHANGED << draw >>
(*****************************************************************************)
(* Open the draw, if the light is on,                                        *)
(* this opens the secret panel                                               *)
(*****************************************************************************)
OpenDraw ==
  /\ draw = "closed"
  /\ draw' = "opened"
  /\ IF light = "on" THEN 
       /\ state' = "unlockedPanel"
	   /\ panel' = "unlocked"
	   /\ door' = "locked"
	 ELSE 
	   /\ state' = "waitingForLight"
	   /\ UNCHANGED << panel, door >>
  /\ UNCHANGED << light >>
(*****************************************************************************)
(* Closes the secret panel and move the                                      *)
(* system to initial state                                                   *)
(*****************************************************************************)
ClosePanel ==
  /\ panel = "unlocked"
  /\ panel' = "locked"
  /\ light' = "off"
  /\ draw' = "closed"
  /\ door' = "unlocked"
  /\ state' = "idle"
-------------------------------------------------------------------------------
(*****************************************************************************)
(* All possible actions                                                      *)
(*****************************************************************************)
Next == 
  \/ CloseDoor 
  \/ LightOn 
  \/ OpenDraw 
  \/ ClosePanel
(*****************************************************************************)
(* Specification of the entire system                                        *)
(*****************************************************************************)
Spec == Init /\ [][Next]_<< panel, light, draw, door, state >>

(*****************************************************************************)
(* Specification never violates the type invariance                          *)
(*****************************************************************************)
THEOREM Spec => []TypeInv
(*****************************************************************************)
(* The panel and door are never both unlocked in the same time               *)
(*****************************************************************************)
Inv == 
  \/ panel = "unlocked" => door = "locked"  
  \/ door = "unlocked" => panel = "locked" 
===============================================================================