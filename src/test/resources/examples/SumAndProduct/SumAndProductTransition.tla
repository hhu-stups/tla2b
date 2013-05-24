------------------------- MODULE SumAndProductTransition ---------------------
(****************************************************************************)
(* This module formalizes the "sum and product" puzzle, due to Freudenthal  *)
(* (1969), and which goes as follows:                                       *)
(* J says to S and P: I have chosen two integers x and y such that          *)
(* 1 < x <= y < 100. In a moment, I will inform S only of the sum x+y       *)
(* and P only of the product x*y. These announcements remain private.       *)
(* You are required to determine the pair (x,y). He acts as said.           *)
(* The following conversation now takes place:                              *)
(* 1. P says: "I don't know it."                                            *)
(* 2. S says: "I knew you didn't."                                          *)
(* 3. P says: "Now I know it."                                              *)
(* 4. S says: "I now also know it."                                         *)
(* Determine the pair (x,y).                                                *)
(*                                                                          *)
(* The following TLA+ module represents the puzzle as a transition system   *)
(* where the two values are picked arbitrarily, then the feasibility of the *)
(* above dialogue is verified, with S and P adapting their beliefs at each  *)
(* step.                                                                    *)
(* In fact, the first announcement is implied by the second one, so we do   *)
(* not have to represent it explicitly.                                     *)
(****************************************************************************)

EXTENDS Naturals, FiniteSets

VARIABLES x, y,     \* the numbers chosen by J
  beliefP, beliefS, \* the pairs considered possible by P and S
  step              \* next announcement in the conversation

Pairs == { <<i,j>> \in (2 .. 99) \X (2 .. 99) : i <= j }

(* Set of pairs that are equivalent from the point of view of P or S with a pair (i,j).
   In particular, possibleP(x,y) denotes the set of pairs that P considers possible
   given her initial knowledge. *)
possibleP(i,j) == { <<u,v>> \in Pairs : u*v = i*j }
possibleS(i,j) == { <<u,v>> \in Pairs : u+v = i+j }

(* Given a set B of beliefs (pairs of numbers), an agent knows the pair if B 
   is a singleton. For example, P knows the pair if knows(beliefP) holds. *)
knows(B) == Cardinality(B) = 1

(* Given a set B of beliefs, one knows that P knows the pair, if for every
   belief b in B, P knows the result based on what it considers compatible
   with b. For example, S knows that P knows if knows_knowsP(beliefS) holds. *)
knows_knowsP(B) == \A <<i,j>> \in B : knows(possibleP(i,j))

(* Similarly, given B, one knows that P doesn't know if there is no pair in B
   for which P knows. *)
knows_not_knowsP(B) == \A <<i,j>> \in B : ~ knows(possibleP(i,j))

Init ==
  /\ x \in 2 .. 99 /\ y \in 2 .. 99 /\ x <= y
(* uncomment the following conjunct to check uniqueness of solution *)
\*  /\ ~ (x=4 /\ y=13)
  /\ beliefP = possibleP(x,y)
  /\ beliefS = possibleS(x,y)
  /\ step = 2

(* The following actions correspond to the different steps in the conversation. *)
Step2 ==
  /\ step = 2
  /\ ~ knows(beliefP)   \* logically redundant, but speeds up verification
  /\ knows_not_knowsP(beliefS)
  /\ beliefP' = beliefP \ { <<i,j>> \in beliefP : ~ knows_not_knowsP(possibleS(i,j)) }
  /\ step' = 3
  /\ UNCHANGED <<x,y,beliefS>>

Step3 ==
  /\ step = 3
  /\ knows(beliefP)
  /\ beliefS' = beliefS \ { <<i,j>> \in beliefS : 
                            LET P == possibleP(i,j)
                            IN  ~ knows(P \ {<<u,v>> \in P : ~ knows_not_knowsP(possibleS(u,v))}) }
  /\ step' = 4
  /\ UNCHANGED <<x,y,beliefP>>

Step4 ==
  /\ step = 4
  /\ knows(beliefS)
  /\ step' = 5
  /\ UNCHANGED <<x,y,beliefP,beliefS>>

Next == Step2 \/ Step3 \/ Step4

vars == <<x,y,beliefP,beliefS>>

SumProduct == Init /\ [][Next]_vars

(* The following assertion says that the protocol cannot finish. Try to verify it
   in order to find the solution of the puzzle (disable deadlock checking). *)
Impossible == step # 5

=============================================================================
\* Modification History
\* Last modified Mon Apr 22 12:17:12 CEST 2013 by merz
\* Created Fri Apr 19 18:30:06 CEST 2013 by merz
