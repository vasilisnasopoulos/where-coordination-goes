--------------------------- MODULE Membership_Proof ---------------------------
(* MINIMAL_SILENCE.md §8.7, machine-checked. Changing membership, one        *)
(* commitment o of an EARLIER scope at a time.                                 *)
(*                                                                             *)
(*   Join j: j's invocations count only in scopes opened after its admission, *)
(*   so for o a coalition invalidates iff it does so without j:               *)
(*   Inv1 = {S : S \ {j} \in Inv}.                                             *)
(*     JoinSafe     -- D is safe after the join iff D \ {j} was safe before;   *)
(*                     silencing the newcomer never helps an old commitment.   *)
(*     JoinKeepsTau -- tau of every earlier commitment is unchanged.          *)
(*                                                                             *)
(*   Leave i: i is silenced in every later scope (one agreement, Complete      *)
(*   CALM Remark 3), i.e. for a later commitment i is no longer open.          *)
(*     LeaveSafe    -- D is safe without i iff D \cup {i} was safe with i.     *)
(*     LeaveTau     -- tau_without_i <= tau_with_i <= tau_without_i + 1:       *)
(*                     a removal saves at most one silence, and costs the one  *)
(*                     agreement that removes i.                               *)
(*                                                                             *)
(* Safety and counting only; how a system admits or removes a member is not   *)
(* modelled.                                                                   *)
EXTENDS FiniteSets, FiniteSetTheorems, TLAPS

CONSTANTS N, Open, Inv, j, i

ASSUME Assm ==
  /\ IsFiniteSet(N)
  /\ Open \subseteq N
  /\ Inv \subseteq SUBSET N
  /\ \A S, T \in SUBSET N : S \in Inv /\ S \subseteq T => T \in Inv   \* Fact 1
  /\ j \in N /\ j \notin Open                                          \* the newcomer
  /\ i \in Open                                                        \* the one who leaves

\* safety and tau for a given open set and invalidating family
SafeX(O, I, D) == (O \ D) \notin I
TauX(O, I, t) ==
  /\ \E D \in SUBSET O : SafeX(O, I, D) /\ Cardinality(D) = t
  /\ \A D \in SUBSET O : SafeX(O, I, D) => t <= Cardinality(D)

LEMMA FinSub == \A S \in SUBSET N : IsFiniteSet(S) /\ Cardinality(S) \in Nat
  BY Assm, FS_Subset, FS_CardinalityType

\* ---------------- Join ----------------
Open1 == Open \cup {j}
Inv1  == {S \in SUBSET N : S \ {j} \in Inv}

THEOREM JoinSafe == \A D \in SUBSET Open1 : SafeX(Open1, Inv1, D) <=> SafeX(Open, Inv, D \ {j})
<1> SUFFICES ASSUME NEW D \in SUBSET Open1 PROVE SafeX(Open1, Inv1, D) <=> SafeX(Open, Inv, D \ {j})
  OBVIOUS
<1>1. (Open1 \ D) \ {j} = Open \ (D \ {j})  BY Assm DEF Open1
<1>2. Open1 \ D \in SUBSET N  BY Assm DEF Open1
<1> QED BY <1>1, <1>2 DEF SafeX, Inv1

THEOREM JoinKeepsTau == \A t \in Nat : TauX(Open, Inv, t) <=> TauX(Open1, Inv1, t)
<1> SUFFICES ASSUME NEW t \in Nat PROVE TauX(Open, Inv, t) <=> TauX(Open1, Inv1, t)
  OBVIOUS
<1>0. Open \subseteq Open1 /\ Open1 \subseteq N  BY Assm DEF Open1
<1>1. TauX(Open, Inv, t) => TauX(Open1, Inv1, t)
  <2> SUFFICES ASSUME TauX(Open, Inv, t) PROVE TauX(Open1, Inv1, t)
    OBVIOUS
  <2>1. PICK D \in SUBSET Open : SafeX(Open, Inv, D) /\ Cardinality(D) = t  BY DEF TauX
  <2>2. D \ {j} = D  BY Assm
  <2>3. SafeX(Open1, Inv1, D)  BY <2>1, <2>2, <1>0, JoinSafe
  <2>4. \A E \in SUBSET Open1 : SafeX(Open1, Inv1, E) => t <= Cardinality(E)
    <3> SUFFICES ASSUME NEW E \in SUBSET Open1, SafeX(Open1, Inv1, E) PROVE t <= Cardinality(E)
      OBVIOUS
    <3>1. SafeX(Open, Inv, E \ {j})  BY JoinSafe
    <3>2. E \ {j} \in SUBSET Open  BY DEF Open1
    <3>3. t <= Cardinality(E \ {j})  BY <3>1, <3>2 DEF TauX
    <3>4. IsFiniteSet(E) /\ E \ {j} \in SUBSET E  BY <1>0, FinSub
    <3>5. Cardinality(E \ {j}) <= Cardinality(E)  BY <3>4, FS_Subset
    <3>6. Cardinality(E \ {j}) \in Nat /\ Cardinality(E) \in Nat  BY <3>2, <1>0, FinSub
    <3> QED BY <3>3, <3>5, <3>6
  <2> QED BY <2>1, <2>3, <2>4, <1>0 DEF TauX
<1>2. TauX(Open1, Inv1, t) => TauX(Open, Inv, t)
  <2> SUFFICES ASSUME TauX(Open1, Inv1, t) PROVE TauX(Open, Inv, t)
    OBVIOUS
  <2>1. PICK D \in SUBSET Open1 : SafeX(Open1, Inv1, D) /\ Cardinality(D) = t  BY DEF TauX
  <2> DEFINE D0 == D \ {j}
  <2>2. D0 \in SUBSET Open /\ SafeX(Open, Inv, D0)  BY <2>1, JoinSafe DEF Open1
  <2>3. SafeX(Open1, Inv1, D0)  BY <2>2, <1>0, JoinSafe
  <2>4. t <= Cardinality(D0)  BY <2>2, <2>3, <1>0 DEF TauX
  <2>5. Cardinality(D0) <= Cardinality(D)  BY <1>0, FinSub, FS_Subset
  <2>6. Cardinality(D0) \in Nat  BY <2>2, <1>0, FinSub
  <2>7. Cardinality(D0) = t  BY <2>1, <2>4, <2>5, <2>6
  <2>8. \A E \in SUBSET Open : SafeX(Open, Inv, E) => t <= Cardinality(E)
    <3> SUFFICES ASSUME NEW E \in SUBSET Open, SafeX(Open, Inv, E) PROVE t <= Cardinality(E)
      OBVIOUS
    <3>1. E \ {j} = E  BY Assm
    <3>2. SafeX(Open1, Inv1, E)  BY <3>1, <1>0, JoinSafe
    <3> QED BY <3>2, <1>0 DEF TauX
  <2> QED BY <2>2, <2>7, <2>8 DEF TauX
<1> QED BY <1>1, <1>2

\* ---------------- Leave ----------------
OpenL == Open \ {i}

THEOREM LeaveSafe == \A D \in SUBSET OpenL : SafeX(OpenL, Inv, D) <=> SafeX(Open, Inv, D \cup {i})
<1> SUFFICES ASSUME NEW D \in SUBSET OpenL PROVE SafeX(OpenL, Inv, D) <=> SafeX(Open, Inv, D \cup {i})
  OBVIOUS
<1>1. OpenL \ D = Open \ (D \cup {i})  BY DEF OpenL
<1> QED BY <1>1 DEF SafeX

\* silencing more never hurts (Fact 1)
LEMMA SafeUp == \A D, E \in SUBSET N : D \subseteq E /\ SafeX(Open, Inv, D) => SafeX(Open, Inv, E)
<1> SUFFICES ASSUME NEW D \in SUBSET N, NEW E \in SUBSET N, D \subseteq E,
                    SafeX(Open, Inv, D), (Open \ E) \in Inv
             PROVE FALSE
  BY DEF SafeX
<1>1. Open \ E \subseteq Open \ D  OBVIOUS
<1>2. (Open \ D) \in Inv  BY <1>1, Assm
<1> QED BY <1>2 DEF SafeX

THEOREM LeaveTau == \A t0, t1 \in Nat :
  TauX(Open, Inv, t0) /\ TauX(OpenL, Inv, t1) => t1 <= t0 /\ t0 <= t1 + 1
<1> SUFFICES ASSUME NEW t0 \in Nat, NEW t1 \in Nat, TauX(Open, Inv, t0), TauX(OpenL, Inv, t1)
             PROVE t1 <= t0 /\ t0 <= t1 + 1
  OBVIOUS
<1>0. OpenL \subseteq Open /\ Open \subseteq N /\ i \in N  BY Assm DEF OpenL
<1>1. t1 <= t0
  <2>1. PICK D \in SUBSET Open : SafeX(Open, Inv, D) /\ Cardinality(D) = t0  BY DEF TauX
  <2> DEFINE D1 == D \ {i}
  <2>2. D1 \in SUBSET OpenL  BY DEF OpenL
  <2>3. D \subseteq D1 \cup {i} /\ D1 \cup {i} \in SUBSET N  BY <1>0
  <2>4. SafeX(Open, Inv, D1 \cup {i})  BY <2>1, <2>3, <1>0, SafeUp
  <2>5. SafeX(OpenL, Inv, D1)  BY <2>2, <2>4, LeaveSafe
  <2>6. t1 <= Cardinality(D1)  BY <2>2, <2>5 DEF TauX
  <2>7. Cardinality(D1) <= Cardinality(D) /\ Cardinality(D1) \in Nat  BY <1>0, FinSub, FS_Subset
  <2> QED BY <2>1, <2>6, <2>7
<1>2. t0 <= t1 + 1
  <2>1. PICK D \in SUBSET OpenL : SafeX(OpenL, Inv, D) /\ Cardinality(D) = t1  BY DEF TauX
  <2>2. SafeX(Open, Inv, D \cup {i})  BY <2>1, LeaveSafe
  <2>3. D \cup {i} \in SUBSET Open  BY <1>0, Assm DEF OpenL
  <2>4. t0 <= Cardinality(D \cup {i})  BY <2>2, <2>3 DEF TauX
  <2>5. IsFiniteSet(D)  BY <1>0, FinSub
  <2>6. Cardinality(D \cup {i}) <= Cardinality(D) + 1  BY <2>5, FS_AddElement, <1>0, FinSub
  <2>7. Cardinality(D) \in Nat /\ Cardinality(D \cup {i}) \in Nat  BY <2>3, <1>0, FinSub
  <2> QED BY <2>1, <2>4, <2>6, <2>7
<1> QED BY <1>1, <1>2
=============================================================================
