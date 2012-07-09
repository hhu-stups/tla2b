----------------------------- MODULE MCFastPaxos ----------------------------
EXTENDS FiniteSets, Naturals 

CONSTANTS PVal, Acceptor, FastNum, ClassicNum, Quorum(_) \* , _\prec_
VARIABLES rnd, vrnd, pval, sentMsg, learned

NextNum(a) == IF a+1 \in FastNum \cup ClassicNum THEN a+1 ELSE 0

INSTANCE FastPaxos WITH \prec <- <
CONSTANTS a1, a2, a3, v1, v2

MCQuorum(i) == IF i \in ClassicNum THEN {{a1,a2}, {a1,a3}, {a2, a3}}
                                   ELSE {{a1,a2,a3}}
Correctness == 
 /\ Cardinality(learned) \leq 1
 /\ \A v \in learned : \E m \in sentMsg : /\ m.type = "propose"
                                          /\ m.pval = v
TSpec == Init /\  [][Next]_vars

(*
TInit ==

TSpec == TInit /\ [][Next]_vars
*)
=============================================================================
