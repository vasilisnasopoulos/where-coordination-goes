---- MODULE MC_Suff_mut ----
(* Mutant of MC_Suff: silences nobody; the invariant must be violated.     *)
(* variant at the commitment and realizable on every run. Mutant:           *)
(* MC_Suff_mut silences nobody and must violate the invariant.              *)
EXTENDS CoordinatedVariant_Proof, Defs
VARIABLE x
Init == x = 0
Next == x' = x
Spec == Init /\ [][Next]_x
Silenced == {}
UpperBoundModel ==
  /\ IsTau(1) /\ Hits(Silenced, FOpen) /\ Cardinality(Silenced) = 1
  /\ B3conv /\ RunsFromH0 /\ O0 \in Obs[H0] /\ <<O0, O0>> \in Leq
  /\ ProperAt(SilenceVariant(Silenced))
  /\ \A A \in SUBSET Open : SilenceVariant(Silenced)[HistOf[A][A \ Silenced]] # {}
====
