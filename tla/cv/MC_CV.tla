---- MODULE MC_CV ----
(* Non-vacuity of CoordinatedVariant_Proof: all assumptions hold together with  *)
(* tau = 1 (alarm, first-come-wins). Run from tla/cv with                    *)
(* -DTLA-Library=<repo>/tla:<tlapm>/lib/tlapm/stdlib (see README).           *)
EXTENDS CoordinatedVariant_Proof, Defs
ASSUME ProperVariant /\ IsTau(1) /\ Cardinality(SilencedAll) = 1
====
