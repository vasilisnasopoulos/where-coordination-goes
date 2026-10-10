---- MODULE MC_CV_mut ----
(* Mutant: the mechanism lets everyone take effect (silences nobody). TLC    *)
(* must reject it: realizability B2 in AssmB is false.                        *)
EXTENDS CoordinatedVariant_Proof, Defs
cEffNone == [A \in SUBSET cN |-> A]
VARIABLE x
Init == x = 0
Next == x' = x
Spec == Init /\ [][Next]_x
LowerBoundModel == ProperVariant /\ B3 /\ IsTau(1) /\ Cardinality(SilencedAll) = 1
====
