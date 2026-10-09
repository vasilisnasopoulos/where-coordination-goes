----------------------- MODULE CoordinatedVariant_Proof -----------------------
(* MINIMAL_SILENCE.md §8.12, Lemmas A and C.                                   *)
(*                                                                             *)
(* Lemma A, in Complete CALM's own terms (Hellerstein, arXiv 2602.09435,       *)
(* Defs. 6 and 11): a properly coordinated variant Spec' that admits o at H    *)
(* must forbid (ObsP[H2] = {}) every future H2 of H at which the original Spec *)
(* has no refinement of o.                                                     *)
(*                                                                             *)
(* Lemma C: a mechanism that decides whom to silence adaptively (Eff[A] = the  *)
(* acting participants whose invocations take effect, chosen after A acts)     *)
(* still silences a hitting set of F_open in the run where every open          *)
(* participant acts, so it pays at least tau in the worst case.                *)
(*                                                                             *)
(* Lemma B: Lemma A's "forbid" is Lemma C's "silence".                         *)
(* OnlySilence needs only B1 and B2: coordination = choosing who counts.       *)
(* B3 is needed only for the exact count (Lemma B, Chain); without it, if       *)
(* attempts alone break o, no variant exists (NoVariantIfAttemptsBreak).        *)
(*   B1 (Def. 5) the environment may make any set A of open participants act, *)
(*      and the implementation chooses only which of them get an effective     *)
(*      response, Eff[A] \subseteq A; the run reaches history HistOf[A][Eff[A]]. *)
(*   B2 (realizable) the variant admits some outcome on every run the          *)
(*      environment can produce: ObsP[HistOf[A][Eff[A]]] # {}.                 *)
(*   B3 (effect through responses) if the EFFECTIVE set R invalidates o, the   *)
(*      history HistOf[A][R] is an invalidating future of H0 (Def. 6).          *)
EXTENDS FiniteSets, FiniteSetTheorems, TLAPS

\* ---------------- Lemma A ----------------
CONSTANTS Hist, Out, Fut, Leq, Obs, ObsP

ASSUME AssmA ==
  /\ Fut \subseteq Hist \X Hist                      \* <<H1, H2>> : H2 is a future of H1
  /\ Leq \subseteq Out \X Out                        \* <<o1, o2>> : o2 refines o1
  /\ Obs  \in [Hist -> SUBSET Out]
  /\ ObsP \in [Hist -> SUBSET Out]

\* Def. 11 (properly coordinated variant)
ProperVariant ==
  /\ \A h \in Hist : ObsP[h] \subseteq Obs[h]
  /\ \A h1, h2 \in Hist :
        (<<h1, h2>> \in Fut /\ ObsP[h1] # {} /\ ObsP[h2] # {})
          => \A o \in ObsP[h1] : \E o2 \in ObsP[h2] : <<o, o2>> \in Leq

\* o is invalidated at the future h2 of h: Spec has no refinement of o there (Def. 6)
Invalidates(h, o, h2) ==
  <<h, h2>> \in Fut /\ \A o2 \in Obs[h2] : <<o, o2>> \notin Leq

THEOREM LemmaA ==
  ProperVariant =>
    \A h, h2 \in Hist : \A o \in ObsP[h] :
       Invalidates(h, o, h2) => ObsP[h2] = {}
<1> SUFFICES ASSUME ProperVariant, NEW h \in Hist, NEW h2 \in Hist, NEW o \in ObsP[h],
                    Invalidates(h, o, h2), ObsP[h2] # {}
             PROVE FALSE
  OBVIOUS
<1>1. ObsP[h] # {}  OBVIOUS
<1>2. PICK o2 \in ObsP[h2] : <<o, o2>> \in Leq  BY <1>1 DEF ProperVariant, Invalidates
<1>3. o2 \in Obs[h2]  BY <1>2 DEF ProperVariant
<1> QED BY <1>2, <1>3 DEF Invalidates

\* ---------------- Lemma C ----------------
CONSTANTS N, Open, Inv, Eff

ASSUME AssmC ==
  /\ IsFiniteSet(N)
  /\ Open \subseteq N
  /\ Inv \subseteq SUBSET N
  /\ \A S, T \in SUBSET N : S \in Inv /\ S \subseteq T => T \in Inv   \* Fact 1
  /\ Eff \in [SUBSET Open -> SUBSET Open]
  /\ \A A \in SUBSET Open : Eff[A] \subseteq A          \* only actors can take effect

FOpen == {S \in Inv : S \subseteq Open}
Hits(D, F) == \A S \in F : S \cap D # {}

\* tau is the hitting number: some hitting set has size t, none is smaller
IsTau(t) ==
  /\ \E D \in SUBSET Open : Hits(D, FOpen) /\ Cardinality(D) = t
  /\ \A D \in SUBSET Open : Hits(D, FOpen) => t <= Cardinality(D)

\* the mechanism keeps o correct in every run: what takes effect never invalidates
Correct == \A A \in SUBSET Open : Eff[A] \notin Inv

\* silenced in the worst run (everyone open acts)
SilencedAll == Open \ Eff[Open]

THEOREM LemmaC_Hits == Correct => Hits(SilencedAll, FOpen)
<1> SUFFICES ASSUME Correct, NEW S \in FOpen, S \cap SilencedAll = {} PROVE FALSE
  BY DEF Hits
<1>1. S \subseteq Open  BY DEF FOpen
<1>2. S \subseteq Eff[Open]  BY <1>1 DEF SilencedAll
<1>3. Eff[Open] \in SUBSET N  BY AssmC
<1>4. S \in Inv /\ S \in SUBSET N  BY AssmC DEF FOpen
<1>5. Eff[Open] \in Inv  BY <1>2, <1>3, <1>4, AssmC
<1> QED BY <1>5, AssmC DEF Correct

THEOREM LemmaC == \A t \in Nat : Correct /\ IsTau(t) => t <= Cardinality(SilencedAll)
<1> SUFFICES ASSUME NEW t \in Nat, Correct, IsTau(t) PROVE t <= Cardinality(SilencedAll)
  OBVIOUS
<1>1. SilencedAll \in SUBSET Open  BY DEF SilencedAll
<1>2. Hits(SilencedAll, FOpen)  BY LemmaC_Hits
<1> QED BY <1>1, <1>2 DEF IsTau

\* ---------------- Lemma B and the chain A -> B -> C ----------------
CONSTANTS H0, O0, HistOf

ASSUME AssmB ==
  /\ H0 \in Hist /\ O0 \in ObsP[H0]
  /\ HistOf \in [SUBSET Open -> [SUBSET Open -> Hist]]
  /\ \A A \in SUBSET Open : ObsP[HistOf[A][Eff[A]]] # {}                          \* B2

\* B3 is no longer assumed: it is a property a specification may or may not have.
B3 == \A A, R \in SUBSET Open : R \in Inv => Invalidates(H0, O0, HistOf[A][R])

\* Without B3. The implementation's only lever is which invocations take effect
\* (B1 = Def. 5). Any realizable properly coordinated variant uses it so that the
\* run it produces never invalidates o. So coordination IS choosing whose
\* invocations do not count -- silence -- for every specification.
THEOREM OnlySilence ==
  ProperVariant => \A A \in SUBSET Open : ~Invalidates(H0, O0, HistOf[A][Eff[A]])
<1> SUFFICES ASSUME ProperVariant, NEW A \in SUBSET Open,
                    Invalidates(H0, O0, HistOf[A][Eff[A]])
             PROVE FALSE
  OBVIOUS
<1>1. Eff[A] \in SUBSET Open  BY AssmC
<1>2. HistOf[A][Eff[A]] \in Hist  BY <1>1, AssmB
<1>3. ObsP[HistOf[A][Eff[A]]] = {}  BY <1>2, LemmaA, AssmB
<1> QED BY <1>3, AssmB

\* Without B3, the other side. If the mere attempt of A breaks o, whatever is
\* silenced, then no realizable properly coordinated variant exists at all:
\* such a commitment cannot be saved by any coordination.
THEOREM NoVariantIfAttemptsBreak ==
  \A A \in SUBSET Open :
    (\A R \in SUBSET A : Invalidates(H0, O0, HistOf[A][R])) => ~ProperVariant
<1> SUFFICES ASSUME NEW A \in SUBSET Open,
                    \A R \in SUBSET A : Invalidates(H0, O0, HistOf[A][R]),
                    ProperVariant
             PROVE FALSE
  OBVIOUS
<1>1. Eff[A] \in SUBSET A  BY AssmC
<1> QED BY <1>1, OnlySilence

\* With B3: what is silenced meets every invalidating coalition (Lemma B) ...
THEOREM LemmaB == ProperVariant /\ B3 => Correct
<1> SUFFICES ASSUME ProperVariant, B3, NEW A \in SUBSET Open, Eff[A] \in Inv PROVE FALSE
  BY DEF Correct
<1>1. Eff[A] \in SUBSET Open  BY AssmC
<1>2. Invalidates(H0, O0, HistOf[A][Eff[A]])  BY <1>1 DEF B3
<1> QED BY <1>2, OnlySilence

\* ... so in the run where every open participant acts it silences at least tau.
THEOREM Chain == \A t \in Nat : ProperVariant /\ B3 /\ IsTau(t) => t <= Cardinality(SilencedAll)
  BY LemmaB, LemmaC
=============================================================================
