----- MODULE MySequence-----
EXTENDS Sequences
VARIABLE q
Init == q = <<1, 2, 3>>
Next ==
  /\ q # <<>>
  /\ q' = Tail(q)
Spec == Init /\ [][Next]_q
=======================
