---- MODULE MC_Membership_mut ----
(* Mutant: the newcomer also counts in the earlier scope; tau becomes 3.   *)
(* (tau = 2); newcomer 3; leaver 1. A join keeps tau = 2, a leave gives 1   *)
(* (the +1 bound is tight). Mutant: MC_Membership_mut lets the newcomer     *)
(* count in the old scope, and tau must change.                             *)
EXTENDS Membership_Proof
cInv == {S \in SUBSET {1, 2, 3} : 1 \in S \/ 2 \in S}
VARIABLE x
Init == x = 0
Next == x' = x
Spec == Init /\ [][Next]_x
JoinInvOld == {S \in SUBSET {1, 2, 3} : 1 \in S \/ 2 \in S \/ 3 \in S}  \* newcomer counts in the old scope
MembershipModel ==
  /\ TauX(Open, Inv, 2) /\ TauX(Open1, JoinInvOld, 2) /\ ~TauX(Open1, JoinInvOld, 1)
  /\ TauX(OpenL, Inv, 1)
====
