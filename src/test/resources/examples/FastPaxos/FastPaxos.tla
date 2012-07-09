------------------------------ MODULE FastPaxos -----------------------------
CONSTANTS PVal, Acceptor, FastNum, ClassicNum, Quorum(_), _\prec_, NextNum(_)

i \preceq j == (i \prec j) \/ (i = j)

Max(S) == CHOOSE i \in S : \A j \in S : j \preceq i

RNum == FastNum \cup ClassicNum

ASSUME 
  /\ FastNum \cap ClassicNum = {}
  /\ \A i, j, k \in RNum : (i \prec j) /\ (j \prec k) => (i \prec k)
  /\ \A i \in RNum : ~(i \prec i)
  /\ \A i, j \in RNum : (i \preceq j) \/ (j \preceq i)
  /\ (0 \notin RNum) /\ \A i \in RNum : 0 \prec i
  /\ \A i \in FastNum : NextNum(i) \in RNum => 
                          ~\E j \in RNum : (i \prec j) /\ (j \prec NextNum(i))

R3 ==   \A i, j \in RNum : 
          \A Q \in Quorum(i), R \in Quorum(j) : Q \cap R # {}
R5b ==   \A i, j \in RNum :     
             (j \in FastNum) => \A Q \in Quorum(i), R1, R2 \in Quorum(j) : 
                                   Q \cap R1 \cap R2 # {}

ASSUME
  /\ \A i \in RNum : Quorum(i) \subseteq SUBSET Acceptor
  /\ R3 /\ R5b

any == CHOOSE v : v \notin PVal

Message ==
       [type : {"propose"}, pval : PVal]
  \cup [type : {"phase1a"}, rnd : RNum]
  \cup [type : {"phase1b"}, rnd : RNum, vrnd : RNum \cup {0}, 
         pval : PVal \cup {any}, acc : Acceptor]
  \cup [type : {"phase2a"}, rnd : RNum, pval : PVal \cup {any}]
  \cup [type : {"phase2b"}, rnd : RNum, pval : PVal, acc : Acceptor]


VARIABLES rnd, vrnd, pval, sentMsg, learned
vars == <<rnd, vrnd, pval, sentMsg, learned>>

TypeOK == 
  /\ rnd  \in [Acceptor -> RNum \cup {0}]
  /\ vrnd \in [Acceptor -> RNum \cup {0}]
  /\ pval \in [Acceptor -> PVal \cup {any}]
  /\ sentMsg  \in SUBSET Message
  /\ learned  \in SUBSET PVal

Init ==
  /\ rnd  = [a \in Acceptor |-> 0]
  /\ vrnd = [a \in Acceptor |-> 0]
  /\ pval = [a \in Acceptor |-> any]
  /\ sentMsg  = {}
  /\ learned  = {}
-----------------------------------------------------------------------------
Send(m) == sentMsg' = sentMsg \cup {m}

Propose(v) ==  
  /\ Send([type |-> "propose", pval |-> v])
  /\ UNCHANGED <<rnd, vrnd, pval, learned>>
  
Phase1a(i) == 
  /\ Send([type |-> "phase1a", rnd |-> i])
  /\ UNCHANGED <<rnd, vrnd, pval, learned>>

Phase1b(a, i) ==
  /\ rnd[a] \prec i
  /\ \E m \in sentMsg : (m.type = "phase1a") /\ (m.rnd = i)
  /\ rnd' = [rnd EXCEPT ![a] = i]
  /\ Send([type |-> "phase1b", rnd |-> i, vrnd |-> vrnd[a], pval |-> pval[a], 
           acc |-> a])
  /\ UNCHANGED <<vrnd, pval, learned>>

P1bMsg(Q, i) == 
   {m \in sentMsg : (m.type = "phase1b") /\ (m.acc \in Q) /\ (m.rnd = i)}

SafeSet(M, Q, i) ==
    LET k  == Max({m.vrnd : m \in M})
        Vk == {m.pval : m \in {mm \in M : mm.vrnd = k}}
        Only(v) == \/ Vk = {v}
                   \/ /\ k \in FastNum
                      /\ \E R \in Quorum(k) : 
                           \A a \in Q \cap R :
                             \E m \in M : /\ m.vrnd = k
                                          /\ m.pval = v
                                          /\ m.acc = a
    IN  IF k = 0 
          THEN PVal
          ELSE IF \E v \in Vk : Only(v)
                 THEN {CHOOSE v \in Vk : Only(v)}
                 ELSE PVal                     

Phase2a(i, va) ==
  /\ ~\E m \in sentMsg : (m.type = "phase2a") /\ (m.rnd = i)
  /\ \E Q \in Quorum(i) : 
       /\ \A a \in Q : \E m \in sentMsg : /\ m.type = "phase1b"
                                          /\ m.rnd  = i
                                          /\ m.acc  = a
       /\ \/ /\ va \in SafeSet(P1bMsg(Q,i), Q, i)
             /\ \E m \in sentMsg : /\ m.type \in {"propose", "phase1b"} 
                                   /\ m.pval = va
          \/ /\ SafeSet(P1bMsg(Q,i), Q, i) = PVal
             /\ i \in FastNum
             /\ va = any
  /\ Send([type |-> "phase2a", rnd |-> i, pval |-> va])
  /\ UNCHANGED <<rnd, vrnd, pval, learned>>

Phase2b(i, a, v) ==
  /\ rnd[a] \preceq i
  /\ vrnd[a] \prec i
  /\ \E m \in sentMsg : 
       /\ m.type = "phase2a"
       /\ m.rnd = i
       /\ \/ m.pval = v
          \/ /\ m.pval = any
             /\ \E mm \in sentMsg  : (mm.type = "propose") /\ (mm.pval = v)
  /\ rnd' = [rnd EXCEPT ![a] = i]
  /\ vrnd'  = [vrnd  EXCEPT ![a] = i]
  /\ pval' = [pval EXCEPT ![a] = v]
  /\ Send([type |-> "phase2b", rnd |-> i, pval |-> v, acc |-> a])
  /\ UNCHANGED learned

Learn(v) ==
  /\ \E i \in RNum :
       \E Q \in Quorum(i) : 
         \A a \in Q : 
           \E m \in sentMsg : /\ m.type = "phase2b"
                              /\ m.rnd = i
                              /\ m.pval = v
                              /\ m.acc  = a
  /\ learned' = learned \cup {v}
  /\ UNCHANGED <<rnd, vrnd, pval, sentMsg>>
-----------------------------------------------------------------------------
P2bToP1b(Q, i) ==
  LET iMsg == 
        {m \in sentMsg : (m.type = "phase2b") /\ (m.rnd = i) /\ (m.acc \in Q)}
  IN  {[type |-> "phase1b", rnd |-> NextNum(i), vrnd |-> i, 
           pval |-> m.pval, acc |-> m.acc] : m \in iMsg}

LeaderRecovery(i, v) ==
  /\ ~\E m \in sentMsg : (m.type = "phase2a") /\ (m.rnd = NextNum(i))
  /\ \E Q \in Quorum(i) : 
        /\ \A a \in Q : \E m \in P2bToP1b(Q, i) : m.acc  = a
        /\ v \in SafeSet(P2bToP1b(Q, i), Q, NextNum(i))
        /\ \E m \in P2bToP1b(Q, i) : m.pval = v
  /\ Send([type |-> "phase2a", rnd |-> NextNum(i), pval |-> v])
  /\ UNCHANGED <<rnd, vrnd, pval, learned>>

LeaderlessRecovery(i, a, v) ==  
  /\ NextNum(i) \in FastNum
  /\ rnd[a] = i
  /\ vrnd[a] = i
  /\ \E Q \in Quorum(i) : 
        /\ \A b \in Q : \E m \in P2bToP1b(Q, i) : m.acc  = b
        /\ v \in SafeSet(P2bToP1b(Q, i), Q, NextNum(i))
        /\ \E m \in P2bToP1b(Q, i): m.pval = v
  /\ rnd' = [rnd EXCEPT ![a] = NextNum(i)]
  /\ vrnd'  = [vrnd  EXCEPT ![a] = NextNum(i)]
  /\ pval' = [pval EXCEPT ![a] = v]
  /\ Send([type |-> "phase2b", rnd |-> NextNum(i), pval |-> v, acc |-> a])
  /\ UNCHANGED learned


-----------------------------------------------------------------------------
Next ==
  \/ \E v \in PVal : Propose(v) \/  Learn(v)
  \/ \E i \in RNum : \/ Phase1a(i)
                     \/ \E a \in Acceptor : \/ Phase1b(a, i)
                                            \/ \E v \in PVal : Phase2b(i, a, v)
                     \/ \E va \in PVal \cup {any} : Phase2a(i, va)
  (*\/ \E i \in FastNum, v \in PVal : 
         \/ LeaderRecovery(i, v)
         \/ \E a \in Acceptor :LeaderlessRecovery(i, a, v)*)

Spec == Init /\ [][Next]_vars

VotedForIn(a, v, i) ==
  \E m \in sentMsg : /\ m.type = "phase2b"
                     /\ m.acc  = a
                     /\ m.pval = v
                     /\ m.rnd = i

VotedorAbstainedIn(a, i) ==
  \/ \E v \in PVal : VotedForIn(a, v, i)
  \/ i \prec rnd[a] 

R1 == \A m \in sentMsg : 
        (m.type = "phase2b") => \E mm \in sentMsg : /\ mm.type = "propose"
                                                    /\ mm.pval = m.pval

R2 == \A a \in Acceptor, v1, v2 \in PVal, i \in RNum :
         VotedForIn(a, v1, i) /\ VotedForIn(a, v2, i) => (v1 = v2)

ChooseableIn(v, i) == 
  \E Q \in Quorum(i) : 
    \A a \in Q : (~ VotedorAbstainedIn(a, i)) \/ VotedForIn(a, v, i)
  
NOC(v, i) == \A w \in PVal : ChooseableIn(w, i) => (w = v)

SafeIn(v, i) == \A j \in RNum : (j \prec i) => NOC(v, j)

R4 == \A a \in Acceptor, v \in PVal, i \in RNum :
        VotedForIn(a, v, i) => SafeIn(v, i)

R5a == \A j \in ClassicNum :
         \A a1, a2 \in Acceptor :
           \A v1, v2 \in PVal :
              VotedForIn(a1, v1, j) /\ VotedForIn(a2, v2, j) => (v1 = v2)
=============================================================================
