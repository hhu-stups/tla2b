--------- MODULE TLA2B ---------
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
MinOfSet(S) == CHOOSE p \in S: \A n \in S: p \leq n
MaxOfSet(S) == CHOOSE p \in S: \A n \in S: p \geq n
SetProduct(S)  == S
SetSummation(S) == S
PermutedSequences(S) == S
==============================