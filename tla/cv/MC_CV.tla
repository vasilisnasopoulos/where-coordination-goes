---- MODULE MC_CV ----
(* Non-vacuity of CoordinatedVariant_Proof, lower bound. One state; the     *)
(* invariant is the conjunction the theorems need, evaluated on a concrete   *)
(* model (alarm, tau = 1, first-come-wins). The module's own ASSUMEs (AssmA, *)
(* AssmC, AssmB) are checked by TLC at startup. Mutant: MC_CV_mut.          *)
EXTENDS CoordinatedVariant_Proof, Defs
VARIABLE x
Init == x = 0
Next == x' = x
Spec == Init /\ [][Next]_x
LowerBoundModel == ProperVariant /\ B3 /\ IsTau(1) /\ Cardinality(SilencedAll) = 1
====
