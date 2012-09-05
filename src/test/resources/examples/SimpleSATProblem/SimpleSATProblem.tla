----- MODULE SimpleSATProblem -----
EXTENDS Naturals
CONSTANTS x1,x2,x3,x4,x5,x6,x7
ASSUME 
  /\ x1 \in BOOLEAN /\ x2 \in BOOLEAN /\ x3 \in BOOLEAN
  /\ x4 \in BOOLEAN /\ x5 \in BOOLEAN /\ x6 \in BOOLEAN /\ x7 \in BOOLEAN
  /\ (x1 \/ x2 \/ x5 \/ x4)
  /\ (x1 \/ x2 \/ ~x5 \/ x4)
  /\ (x3 \/ x6)
  /\ (~x4 \/ x7 \/ x1)
  /\ (~x4 \/ ~x7 \/ x2)
 \* 60 different solutions exist
VARIABLES r
Init == r = <<TRUE,TRUE,TRUE,TRUE,TRUE,TRUE,TRUE>>
Set ==  r'= <<x1,x2,x3,x4,x5,x6,x7>>
Next == Set
=======================

