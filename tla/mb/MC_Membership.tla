---- MODULE MC_Membership ----
EXTENDS Membership_Proof
cInv == {S \in SUBSET {1, 2, 3} : 1 \in S \/ 2 \in S}
\* Open = {1,2}, both can break o alone (tau = 2); newcomer 3; leaver 1.
\* Join keeps tau = 2; leave drops it to 1 (the bound tau_L + 1 is tight).
ASSUME /\ TauX(Open, Inv, 2) /\ TauX(Open1, Inv1, 2) /\ TauX(OpenL, Inv, 1)
       /\ ~TauX(Open1, Inv1, 1)
====
