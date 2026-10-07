-------------------------- MODULE MinimalSilence_Proof --------------------------
(* Combinatorial core of MINIMAL_SILENCE.md, Theorems 1(b) and 3, for ANY    *)
(* specification, one commitment at a time.                                    *)
(*                                                                             *)
(*   N    : participants (fixed membership)                                    *)
(*   Open : participants that have not closed the scope (Open \subseteq N)     *)
(*   Inv  : the coalitions S that invalidate the outcome o (some admissible    *)
(*          S-extension leaves o not refinable). Upward closed (Fact 1).       *)
(*   D    : participants about whom silence commitments are made.              *)
(*                                                                             *)
(* After the commitments only Open \ D can act effectively, so o is safe iff   *)
(* Open \ D does not invalidate it.                                            *)
(*                                                                             *)
(* Proved here: Safe(D) <=> D meets every invalidating coalition of open       *)
(* participants (and equivalently every MINIMAL one). Hence the least |D| is   *)
(* exactly the hitting number of F_open. What is NOT proved here: that every   *)
(* coordination saving o is a silence commitment (the modelling step,          *)
(* Theorem 2(b)) -- that rests on the definition, not on set theory.           *)
EXTENDS FiniteSets, FiniteSetTheorems, TLAPS

CONSTANTS N, Open, Inv

ASSUME Assm ==
  /\ IsFiniteSet(N)
  /\ Open \subseteq N
  /\ Inv \subseteq SUBSET N
  /\ \A S, T \in SUBSET N : S \in Inv /\ S \subseteq T => T \in Inv   \* Fact 1

FOpen    == {S \in Inv : S \subseteq Open}
MinFOpen == {S \in FOpen : \A T \in FOpen : T \subseteq S => T = S}

Hits(D, F) == \A S \in F : S \cap D # {}
Safe(D)    == (Open \ D) \notin Inv

\* Theorem 3, both halves: safe exactly when D hits every open invalidating coalition.
THEOREM Exact == \A D \in SUBSET N : Safe(D) <=> Hits(D, FOpen)
<1> SUFFICES ASSUME NEW D \in SUBSET N PROVE Safe(D) <=> Hits(D, FOpen)
  OBVIOUS
<1>1. Safe(D) => Hits(D, FOpen)            \* lower bound (Theorem 1(b))
  <2> SUFFICES ASSUME Safe(D), NEW S \in FOpen, S \cap D = {} PROVE FALSE
    BY DEF Hits
  <2>1. S \subseteq Open \ D  BY DEF FOpen
  <2>2. (Open \ D) \in Inv    BY <2>1, Assm DEF FOpen
  <2> QED BY <2>2 DEF Safe
<1>2. Hits(D, FOpen) => Safe(D)            \* upper bound (sufficiency)
  <2> SUFFICES ASSUME Hits(D, FOpen), (Open \ D) \in Inv PROVE FALSE
    BY DEF Safe
  <2>1. (Open \ D) \in FOpen  BY DEF FOpen
  <2>2. (Open \ D) \cap D = {} OBVIOUS
  <2> QED BY <2>1, <2>2 DEF Hits
<1> QED BY <1>1, <1>2

\* Every open invalidating coalition contains a minimal one (finiteness).
LEMMA HasMinimal == \A S \in FOpen : \E M \in MinFOpen : M \subseteq S
<1> DEFINE P(k) == \A S \in FOpen : Cardinality(S) = k => \E M \in MinFOpen : M \subseteq S
<1>0. \A S \in SUBSET N : IsFiniteSet(S)  BY Assm, FS_Subset
<1>1. \A k \in Nat : P(k)
  <2> DEFINE Q(k) == \A j \in 0..k : P(j)
  <2>1. \A k \in Nat : Q(k)
    <3>1. Q(0)
      <4> SUFFICES ASSUME NEW S \in FOpen, Cardinality(S) = 0
                   PROVE \E M \in MinFOpen : M \subseteq S
        OBVIOUS
      <4>1. S = {}  BY <1>0, FS_EmptySet, Assm DEF FOpen
      <4>2. S \in MinFOpen  BY <4>1 DEF MinFOpen
      <4> QED BY <4>2
    <3>2. \A k \in Nat : Q(k) => Q(k+1)
      <4> SUFFICES ASSUME NEW k \in Nat, Q(k), NEW S \in FOpen, Cardinality(S) = k+1
                   PROVE \E M \in MinFOpen : M \subseteq S
        OBVIOUS
      <4>1. CASE S \in MinFOpen  BY <4>1
      <4>2. CASE S \notin MinFOpen
        <5>1. PICK T \in FOpen : T \subseteq S /\ T # S  BY <4>2 DEF MinFOpen
        <5>2. IsFiniteSet(S) /\ T \subseteq N  BY <1>0, Assm DEF FOpen
        <5>3. IsFiniteSet(T) /\ Cardinality(T) < Cardinality(S)  BY <5>1, <5>2, FS_Subset
        <5>3a. Cardinality(T) \in Nat  BY <5>3, FS_CardinalityType
        <5>4. Cardinality(T) \in 0..k  BY <5>3, <5>3a
        <5>5. PICK M \in MinFOpen : M \subseteq T  BY <5>4
        <5> QED BY <5>1, <5>5
      <4> QED BY <4>1, <4>2
    <3> QED BY <3>1, <3>2, NatInduction
  <2> QED BY <2>1
<1> SUFFICES ASSUME NEW S \in FOpen PROVE \E M \in MinFOpen : M \subseteq S
  OBVIOUS
<1>2. Cardinality(S) \in Nat  BY <1>0, Assm, FS_CardinalityType DEF FOpen
<1>3. P(Cardinality(S))  BY <1>1, <1>2
<1> QED BY <1>3

\* Hitting the minimal coalitions is the same as hitting all of them,
\* so the least |D| is the hitting number of the minimal family F_open(o, H).
THEOREM ExactMinimal == \A D \in SUBSET N : Safe(D) <=> Hits(D, MinFOpen)
<1> SUFFICES ASSUME NEW D \in SUBSET N PROVE Hits(D, FOpen) <=> Hits(D, MinFOpen)
  BY Exact
<1>1. Hits(D, FOpen) => Hits(D, MinFOpen)  BY DEF Hits, MinFOpen
<1>2. Hits(D, MinFOpen) => Hits(D, FOpen)
  <2> SUFFICES ASSUME Hits(D, MinFOpen), NEW S \in FOpen PROVE S \cap D # {}
    BY DEF Hits
  <2>1. PICK M \in MinFOpen : M \subseteq S  BY HasMinimal
  <2> QED BY <2>1 DEF Hits
<1> QED BY <1>1, <1>2

\* Theorem 2(a): no open invalidating coalition => no commitment needed.
THEOREM NoCoalitionNoCoordination == FOpen = {} => Safe({})
BY Exact DEF Hits

(***************************************************************************)
(* Theorem 2(b), mechanism-agnostic. A mechanism is ANY rule Eff that,     *)
(* in the extension where coalition S acts, lets only Eff[S] \subseteq S   *)
(* take effect (ordering, locking, voting, leasing, ...). If it keeps o    *)
(* correct in every extension, then in every S of FOpen it makes some      *)
(* member's invocation ineffective -- i.e. it silences someone in S.       *)
(* If Eff must be fixed at H (the commitment is taken before anyone acts), *)
(* Eff[S] = S \ D for one D, and Exact gives the count.                    *)
(***************************************************************************)
THEOREM SilenceNecessary ==
  \A Eff \in [SUBSET Open -> SUBSET N] :
     (\A S \in SUBSET Open : Eff[S] \subseteq S /\ Eff[S] \notin Inv)
       => \A S \in FOpen : S \ Eff[S] # {}
<1> SUFFICES ASSUME NEW Eff \in [SUBSET Open -> SUBSET N],
                    \A S \in SUBSET Open : Eff[S] \subseteq S /\ Eff[S] \notin Inv,
                    NEW S \in FOpen, S \ Eff[S] = {}
             PROVE FALSE
  OBVIOUS
<1>1. S \in SUBSET Open  BY DEF FOpen
<1>2. Eff[S] = S  BY <1>1
<1> QED BY <1>1, <1>2 DEF FOpen

\* Commitments fixed at H are the special case Eff[S] = S \ D.
THEOREM FixedMechanism ==
  \A D \in SUBSET N :
     (\A S \in SUBSET Open : (S \ D) \notin Inv) <=> Safe(D)
<1> SUFFICES ASSUME NEW D \in SUBSET N
             PROVE (\A S \in SUBSET Open : (S \ D) \notin Inv) <=> Safe(D)
  OBVIOUS
<1>1. (\A S \in SUBSET Open : (S \ D) \notin Inv) => Safe(D)  BY DEF Safe
<1>2. Safe(D) => \A S \in SUBSET Open : (S \ D) \notin Inv
  <2> SUFFICES ASSUME Safe(D), NEW S \in SUBSET Open, (S \ D) \in Inv PROVE FALSE
    OBVIOUS
  <2>1. (S \ D) \subseteq (Open \ D) /\ (S \ D) \in SUBSET N /\ (Open \ D) \in SUBSET N
    BY Assm
  <2> QED BY <2>1, Assm DEF Safe
<1> QED BY <1>1, <1>2

(***************************************************************************)
(* Over a run: one commitment about i in a scope serves every outcome of   *)
(* that scope. Hitting all of them = hitting the union, so the least total *)
(* per scope is the hitting number of the UNION of their families.         *)
(***************************************************************************)
THEOREM RunUnion ==
  \A D \in SUBSET N, F1, F2 \in SUBSET SUBSET N :
     Hits(D, F1 \cup F2) <=> Hits(D, F1) /\ Hits(D, F2)
BY DEF Hits

(***************************************************************************)
(* Hardness. For any graph (edge set Edges over N) the "alarm" specification*)
(* -- alarm iff both ends of some edge press; commit "no alarm" -- has      *)
(* Inv = UpClose(Edges). Hitting it = vertex cover. So the least amount of *)
(* coordination is NP-hard to compute in general (paper: MINIMAL_SILENCE  *)
(* §8). Here: the reduction is exact.                                       *)
(***************************************************************************)
UpClose(E) == {T \in SUBSET N : \E e \in E : e \subseteq T}

THEOREM VertexCover ==
  \A E \in SUBSET SUBSET N, D \in SUBSET N :
     Hits(D, UpClose(E)) <=> \A e \in E : e \cap D # {}
<1> SUFFICES ASSUME NEW E \in SUBSET SUBSET N, NEW D \in SUBSET N
             PROVE Hits(D, UpClose(E)) <=> \A e \in E : e \cap D # {}
  OBVIOUS
<1>1. Hits(D, UpClose(E)) => \A e \in E : e \cap D # {}
  BY DEF Hits, UpClose
<1>2. (\A e \in E : e \cap D # {}) => Hits(D, UpClose(E))
  <2> SUFFICES ASSUME \A e \in E : e \cap D # {}, NEW T \in UpClose(E)
               PROVE T \cap D # {}
    BY DEF Hits
  <2>1. PICK e \in E : e \subseteq T  BY DEF UpClose
  <2> QED BY <2>1
<1> QED BY <1>1, <1>2
================================================================================
