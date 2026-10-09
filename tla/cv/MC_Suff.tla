---- MODULE MC_Suff ----
EXTENDS CoordinatedVariant_Proof, Defs
\* tau = 1 silence ({2}) suffices: the silence variant is proper at the commitment and realizable
ASSUME /\ IsTau(1) /\ Hits({2}, FOpen) /\ Cardinality({2}) = 1
       /\ B3conv /\ RunsFromH0 /\ O0 \in Obs[H0] /\ <<O0, O0>> \in Leq
       /\ ProperAt(SilenceVariant({2}))
       /\ \A A \in SUBSET Open : SilenceVariant({2})[HistOf[A][A \ {2}]] # {}
====
