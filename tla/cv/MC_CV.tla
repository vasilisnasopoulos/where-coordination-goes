---- MODULE MC_CV ----
(* Non-vacuity of CoordinatedVariant_Proof: all assumptions hold together with  *)
(* tau = 1 (alarm, first-come-wins). Run with ../CoordinatedVariant_Proof.tla *)
(* copied next to this file and the TLAPS stdlib on -DTLA-Library.            *)
EXTENDS CoordinatedVariant_Proof, Defs
ASSUME ProperVariant /\ IsTau(1) /\ Cardinality(SilencedAll) = 1
====
