-------------------------- MODULE B3Patterns_Proof --------------------------
(* MINIMAL_SILENCE §8.16, open item: do the Appendix F patterns of Complete  *)
(* CALM have B3? One commitment o. Each open participant i may contribute     *)
(* events from Ev[i] (nonempty); i "took effect" when its events count.       *)
(* o breaks when the counted events X are in BadSets. If BadSets is UPWARD    *)
(* CLOSED (adding events never repairs o), then breaking is upward closed in  *)
(* the set E of participants that took effect, and with Inv = the coalitions  *)
(* able to break o (existentially, as in MINIMAL_SILENCE §1),                 *)
(*     Broken(E) <=> E \in Inv     (= B3 and B3conv together).                *)
(* Instances, each shown upward closed, for any number of participants:       *)
(*   Seal            any new event changes a closed period's content          *)
(*   Before(w)       an event ordered before w: unique choice (w = winner)    *)
(*                   and total order (w = last event of the committed prefix) *)
(*   MoreThan(k)     more than k unit purchases: bounded cardinality          *)
EXTENDS FiniteSets, FiniteSetTheorems, TLAPS

CONSTANTS Open, U, Ev, BadSets
ASSUME Assm ==
  /\ Ev \in [Open -> SUBSET U]
  /\ \A i \in Open : Ev[i] # {}

UpClosed(B) == \A X \in B : \A Y \in SUBSET U : X \subseteq Y => Y \in B

Choices(E) == { f \in [E -> SUBSET U] : \A i \in E : f[i] \subseteq Ev[i] /\ f[i] # {} }
Counted(f, E) == UNION { f[i] : i \in E }
Broken(E) == \E f \in Choices(E) : Counted(f, E) \in BadSets
Inv == { S \in SUBSET Open : \E E \in SUBSET S : Broken(E) }

THEOREM MonoBroken ==
  UpClosed(BadSets) =>
    \A E1, E2 \in SUBSET Open : E1 \subseteq E2 /\ Broken(E1) => Broken(E2)
<1> SUFFICES ASSUME UpClosed(BadSets), NEW E1 \in SUBSET Open, NEW E2 \in SUBSET Open,
                    E1 \subseteq E2, Broken(E1)
             PROVE Broken(E2)
  OBVIOUS
<1>1. PICK f \in Choices(E1) : Counted(f, E1) \in BadSets  BY DEF Broken
<1> DEFINE g == [i \in E2 |-> IF i \in E1 THEN f[i] ELSE Ev[i]]
<1>2. g \in Choices(E2)
  <2>1. \A i \in E2 : g[i] \subseteq Ev[i] /\ g[i] # {} /\ g[i] \in SUBSET U
    BY <1>1, Assm DEF Choices
  <2> QED BY <2>1 DEF Choices
<1>3. Counted(f, E1) \subseteq Counted(g, E2)  BY <1>1 DEF Counted, Choices
<1>4. Counted(g, E2) \in SUBSET U  BY <1>2 DEF Counted, Choices
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF UpClosed, Broken

THEOREM B3Holds ==
  UpClosed(BadSets) => \A E \in SUBSET Open : Broken(E) <=> E \in Inv
<1> SUFFICES ASSUME UpClosed(BadSets), NEW E \in SUBSET Open PROVE Broken(E) <=> E \in Inv
  OBVIOUS
<1>1. Broken(E) => E \in Inv  BY DEF Inv
<1>2. E \in Inv => Broken(E)
  <2> SUFFICES ASSUME E \in Inv PROVE Broken(E)  OBVIOUS
  <2>1. PICK E1 \in SUBSET E : Broken(E1)  BY DEF Inv
  <2> QED BY <2>1, MonoBroken
<1> QED BY <1>1, <1>2

\* Inv is upward closed (Fact 1) — so F_open and tau are defined as in MINIMAL_SILENCE.
THEOREM InvUpClosed ==
  \A S, T \in SUBSET Open : S \in Inv /\ S \subseteq T => T \in Inv
  BY DEF Inv

\* ---------------- The three patterns ----------------
SealBad == { X \in SUBSET U : X # {} }
THEOREM SealUp == UpClosed(SealBad)
  BY DEF UpClosed, SealBad

BeforeBad(Lt, w) == { X \in SUBSET U : \E x \in X : <<x, w>> \in Lt }
THEOREM BeforeUp == \A Lt, w : UpClosed(BeforeBad(Lt, w))
  BY DEF UpClosed, BeforeBad

MoreThanBad(k) == { X \in SUBSET U : Cardinality(X) > k }
THEOREM MoreThanUp == IsFiniteSet(U) => \A k \in Nat : UpClosed(MoreThanBad(k))
<1> SUFFICES ASSUME IsFiniteSet(U), NEW k \in Nat, NEW X \in MoreThanBad(k),
                    NEW Y \in SUBSET U, X \subseteq Y
             PROVE Y \in MoreThanBad(k)
  BY DEF UpClosed
<1>1. IsFiniteSet(Y) /\ IsFiniteSet(X)  BY FS_Subset DEF MoreThanBad
<1>2. Cardinality(X) <= Cardinality(Y)  BY <1>1, FS_Subset
<1>3. Cardinality(X) > k /\ Cardinality(X) \in Nat /\ Cardinality(Y) \in Nat
  BY <1>1, FS_CardinalityType DEF MoreThanBad
<1> QED BY <1>2, <1>3 DEF MoreThanBad

\* ---------------- And one that does NOT have B3 ----------------
\* The referee's counterexample "alarm iff exactly one presses" is not upward closed
\* in the counted events: {press_i} is bad, {press_i, press_j} is not. B3Holds
\* does not apply, as it should not (checks/b3.py: tau = 2, least worst case 1).
=============================================================================
