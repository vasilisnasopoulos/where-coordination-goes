---------------------------- MODULE Temporal_Proof ----------------------------
(* MINIMAL_SILENCE §8.17: the per-run lemma restated in a state machine.    *)
(* Breaking depends only on the current accepted set, so order cannot matter *)
(* by construction; LowerBound is the per-state lemma Core in every reachable *)
(* state. The policy has no fairness (accepting nobody also satisfies it).   *)
(* An asynchronous run: the environment makes open participants act, one at  *)
(* a time, in any order; the mechanism answers each pending invocation with  *)
(* accept or refuse, whenever it likes (or never: deferral), with any policy *)
(* (the next-state relation is fully nondeterministic). Breaking depends on  *)
(* the accepted set (B3: Broken(E) <=> E \in Inv, proved for the patterns in *)
(* B3Patterns_Proof). Results, as invariants of every behaviour:             *)
(*  LowerBound  if the mechanism never lets o break, then in every state     *)
(*              where all open participants have acted, at least tau were    *)
(*              refused or are still pending (deferral counts as silence).  *)
(*  UpperBound  the policy "refuse D, accept everyone else, at once" keeps o *)
(*              unbroken in every behaviour whenever D hits F_open, and it   *)
(*              needs no knowledge of who else will act.                     *)
EXTENDS FiniteSets, FiniteSetTheorems, TLAPS

CONSTANTS Open, Inv
ASSUME Assm ==
  /\ IsFiniteSet(Open)
  /\ Inv \subseteq SUBSET Open
  /\ \A S, T \in SUBSET Open : S \in Inv /\ S \subseteq T => T \in Inv    \* Fact 1

FOpen == {S \in Inv : S \subseteq Open}
Hits(D, F) == \A S \in F : S \cap D # {}
IsTau(t) ==
  /\ \E D \in SUBSET Open : Hits(D, FOpen) /\ Cardinality(D) = t
  /\ \A D \in SUBSET Open : Hits(D, FOpen) => t <= Cardinality(D)

VARIABLES acted, acc, ref          \* who invoked; accepted; refused
vars == <<acted, acc, ref>>

Init == acted = {} /\ acc = {} /\ ref = {}
Act(i)    == i \in Open \ acted /\ acted' = acted \cup {i} /\ UNCHANGED <<acc, ref>>
Accept(i) == i \in acted \ (acc \cup ref) /\ acc' = acc \cup {i} /\ UNCHANGED <<acted, ref>>
Refuse(i) == i \in acted \ (acc \cup ref) /\ ref' = ref \cup {i} /\ UNCHANGED <<acted, acc>>
Next == \E i \in Open : Act(i) \/ Accept(i) \/ Refuse(i)
Spec == Init /\ [][Next]_vars

TypeOK == acted \subseteq Open /\ acc \subseteq acted /\ ref \subseteq acted /\ acc \cap ref = {}
Broken == acc \in Inv                                   \* B3 (B3Patterns_Proof.B3Holds)
Pending == acted \ (acc \cup ref)

THEOREM TypeInv == Spec => []TypeOK
<1>1. Init => TypeOK  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'  BY DEF TypeOK, Next, Act, Accept, Refuse, vars
<1> QED BY <1>1, <1>2, PTL DEF Spec

\* The per-state core: whatever was accepted, if it does not break o, those not
\* accepted (refused, pending, or never acted) hit every coalition able to break o.
LEMMA Core ==
  \A E \in SUBSET Open : \A t \in Nat : (E \notin Inv /\ IsTau(t)) => t <= Cardinality(Open \ E)
<1> SUFFICES ASSUME NEW E \in SUBSET Open, NEW t \in Nat, E \notin Inv, IsTau(t)
             PROVE t <= Cardinality(Open \ E)
  OBVIOUS
<1>1. Hits(Open \ E, FOpen)
  <2> SUFFICES ASSUME NEW S \in FOpen, S \cap (Open \ E) = {} PROVE FALSE  BY DEF Hits
  <2>1. S \in Inv /\ S \subseteq E  BY DEF FOpen
  <2> QED BY <2>1, Assm
<1> QED BY <1>1 DEF IsTau

\* Lower bound over executions: any mechanism (any interleaving, any deferral, any
\* policy). If o is never broken, then once everyone open has acted, the silenced
\* (refused or still pending) number at least tau.
THEOREM LowerBound ==
  \A t \in Nat : IsTau(t) =>
    ((Spec /\ []~Broken) => [](acted = Open => t <= Cardinality(ref \cup Pending)))
<1> SUFFICES ASSUME NEW t \in Nat, IsTau(t)
             PROVE (Spec /\ []~Broken) => [](acted = Open => t <= Cardinality(ref \cup Pending))
  OBVIOUS
<1>1. TypeOK /\ ~Broken /\ acted = Open => t <= Cardinality(ref \cup Pending)
  <2> SUFFICES ASSUME TypeOK, ~Broken, acted = Open PROVE t <= Cardinality(ref \cup Pending)
    OBVIOUS
  <2>1. ref \cup Pending = Open \ acc  BY DEF TypeOK, Pending
  <2>2. acc \in SUBSET Open /\ acc \notin Inv  BY DEF TypeOK, Broken
  <2> QED BY <2>1, <2>2, Core
<1> QED BY <1>1, TypeInv, PTL

\* Upper bound over executions: the policy that refuses exactly D and accepts the rest.
PolicyNext(D) == \E i \in Open : Act(i) \/ (i \notin D /\ Accept(i)) \/ (i \in D /\ Refuse(i))
PolicySpec(D) == Init /\ [][PolicyNext(D)]_vars

PInv(D) == acc \cap D = {} /\ acc \subseteq Open

THEOREM UpperBound ==
  \A D \in SUBSET Open : Hits(D, FOpen) => (PolicySpec(D) => []~Broken)
<1> SUFFICES ASSUME NEW D \in SUBSET Open, Hits(D, FOpen) PROVE PolicySpec(D) => []~Broken
  OBVIOUS
<1>1. Init => PInv(D)  BY DEF Init, PInv
<1>2. PInv(D) /\ [PolicyNext(D)]_vars => PInv(D)'
  BY DEF PInv, PolicyNext, Act, Accept, Refuse, vars
<1>3. PInv(D) => ~Broken
  <2> SUFFICES ASSUME PInv(D), acc \in Inv PROVE FALSE  BY DEF Broken
  <2>1. acc \in FOpen  BY DEF FOpen, PInv
  <2> QED BY <2>1 DEF Hits, PInv
<1> QED BY <1>1, <1>2, <1>3, PTL DEF PolicySpec

\* The policy silences exactly D: nobody outside D is ever refused.
THEOREM PolicySilencesOnlyD ==
  \A D \in SUBSET Open : PolicySpec(D) => [](ref \subseteq D)
<1> SUFFICES ASSUME NEW D \in SUBSET Open PROVE PolicySpec(D) => [](ref \subseteq D)  OBVIOUS
<1>1. Init => ref \subseteq D  BY DEF Init
<1>2. ref \subseteq D /\ [PolicyNext(D)]_vars => (ref \subseteq D)'
  BY DEF PolicyNext, Act, Accept, Refuse, vars
<1> QED BY <1>1, <1>2, PTL DEF PolicySpec
=============================================================================
