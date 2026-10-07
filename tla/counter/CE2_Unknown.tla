----------------------------- MODULE CE2_Unknown -----------------------------
(* Counterexample 2 -- membership not fixed. Known member a closes the     *)
(* scope; by the theorem F_open = {} so "nothing in this scope" is committed*)
(* with zero coordination. A newcomer j then joins and acts.                *)
(* EpochRule = FALSE: j's invocation counts in the open scope -> violation. *)
(* EpochRule = TRUE : j counts only in scopes opened after its admission    *)
(*   (MINIMAL_SILENCE 8.7) -> must hold.                                    *)
EXTENDS Naturals
CONSTANT EpochRule
VARIABLES closedA, committed, joined, counted
vars == <<closedA, committed, joined, counted>>

Init == closedA = FALSE /\ committed = FALSE /\ joined = FALSE /\ counted = 0

ACloses == ~closedA /\ closedA' = TRUE /\ UNCHANGED <<committed, joined, counted>>
Commit  == closedA /\ ~committed /\ committed' = TRUE /\ UNCHANGED <<closedA, joined, counted>>
Join    == ~joined /\ joined' = TRUE /\ UNCHANGED <<closedA, committed, counted>>
JActs   == /\ joined /\ counted = 0
           /\ counted' = IF EpochRule /\ committed THEN 0 ELSE 1
           /\ UNCHANGED <<closedA, committed, joined>>
\* with the epoch rule the newcomer is admitted only into later scopes:
\* if it joined before the commit it is still "closed by construction".
JActsEpoch == JActs /\ (EpochRule => committed)

Next == ACloses \/ Commit \/ Join \/ JActsEpoch
Spec == Init /\ [][Next]_vars

Safe == committed => counted = 0
=============================================================================
