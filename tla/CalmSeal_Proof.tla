---------------------------- MODULE CalmSeal_Proof ----------------------------
(***************************************************************************)
(* TLAPS proof, for ANY set of participants, events and quorums (pairwise  *)
(* intersecting), that Inv is inductive; hence every participant that      *)
(* finalises the period holds the SAME content (Agreement), therefore the  *)
(* same deterministic order and the same unique winner (UniqueChoice), and *)
(* a vote-free finalisation never coexists with an ABSENT decision.        *)
(***************************************************************************)
EXTENDS CalmSeal, TLAPS

ASSUME NoneNotContent == NONE \notin Content
ASSUME AbsentNotSet   == ABSENT \notin SUBSET Ev


\* Decisions as functions of an arbitrary vote table, so primed and unprimed use the same lemma.
DA(vt, n) == \E Q \in Quorum : \A v \in Q : vt[v][n] = "absent"
DP(vt, n) == \E Q \in Quorum : \A v \in Q : vt[v][n] = "present"
VoteType == [Node -> [Node -> {"none", "present", "absent"}]]

LEMMA DecidedIsDA == \A n \in Node : /\ DecidedAbsent(n) = DA(vote, n) /\ DecidedPresent(n) = DP(vote, n)
                                     /\ DecidedAbsent(n)' = DA(vote', n) /\ DecidedPresent(n)' = DP(vote', n)
  BY DEF DecidedAbsent, DecidedPresent, DA, DP

LEMMA NotBothAny == ASSUME NEW vt \in VoteType, NEW n \in Node PROVE ~(DA(vt, n) /\ DP(vt, n))
  <1> SUFFICES ASSUME DA(vt, n), DP(vt, n) PROVE FALSE
    OBVIOUS
  <1>1. PICK Q1 \in Quorum : \A v \in Q1 : vt[v][n] = "absent"
    BY DEF DA
  <1>2. PICK Q2 \in Quorum : \A v \in Q2 : vt[v][n] = "present"
    BY DEF DP
  <1>3. PICK v \in Q1 \cap Q2 : TRUE
    BY QuorumAssumption
  <1> QED BY <1>1, <1>2, <1>3

\* If the absent/present pattern of n's column is the same in two tables, so are the decisions.
LEMMA SameColumn == ASSUME NEW vt1 \in VoteType, NEW vt2 \in VoteType, NEW n \in Node,
                          \A w \in Node : (vt1[w][n] = "absent") = (vt2[w][n] = "absent"),
                          \A w \in Node : (vt1[w][n] = "present") = (vt2[w][n] = "present")
                   PROVE  DA(vt1, n) = DA(vt2, n) /\ DP(vt1, n) = DP(vt2, n)
  BY QuorumAssumption DEF DA, DP

\* Setting one "none" cell to a value can only ADD that value's votes.
LEMMA OneVote == ASSUME NEW vt \in VoteType, NEW v \in Node, NEW n \in Node, NEW val \in {"present", "absent"},
                        vt[v][n] = "none"
                 PROVE  LET vt2 == [vt EXCEPT ![v][n] = val] IN
                          /\ vt2 \in VoteType
                          /\ \A x \in Node \ {n} : DA(vt2, x) = DA(vt, x) /\ DP(vt2, x) = DP(vt, x)
                          /\ DA(vt, n) => DA(vt2, n)
                          /\ DP(vt, n) => DP(vt2, n)
                          /\ val = "present" => DA(vt2, n) = DA(vt, n)
                          /\ val = "absent"  => DP(vt2, n) = DP(vt, n)
  <1> DEFINE vt2 == [vt EXCEPT ![v][n] = val]
  <1>1. vt2 \in VoteType
    BY DEF VoteType
  <1>2. \A w, y \in Node : vt2[w][y] = IF w = v /\ y = n THEN val ELSE vt[w][y]
    BY DEF VoteType
  <1>3. \A x \in Node \ {n} : DA(vt2, x) = DA(vt, x) /\ DP(vt2, x) = DP(vt, x)
    <2> SUFFICES ASSUME NEW x \in Node \ {n} PROVE DA(vt2, x) = DA(vt, x) /\ DP(vt2, x) = DP(vt, x)
      OBVIOUS
    <2> QED BY <1>1, <1>2, SameColumn
  <1>4. DA(vt, n) => DA(vt2, n)
    BY <1>2, QuorumAssumption DEF DA
  <1>5. DP(vt, n) => DP(vt2, n)
    BY <1>2, QuorumAssumption DEF DP
  <1>6. val = "present" => DA(vt2, n) = DA(vt, n)
    <2> SUFFICES ASSUME val = "present" PROVE DA(vt2, n) = DA(vt, n)
      OBVIOUS
    <2>1. \A w \in Node : (vt2[w][n] = "absent") = (vt[w][n] = "absent")
      BY <1>2
    <2>2. \A w \in Node : (vt2[w][n] = "present") = (vt[w][n] = "present") \/ w = v
      BY <1>2
    <2> QED BY <2>1, QuorumAssumption DEF DA
  <1>7. val = "absent" => DP(vt2, n) = DP(vt, n)
    <2> SUFFICES ASSUME val = "absent" PROVE DP(vt2, n) = DP(vt, n)
      OBVIOUS
    <2>1. \A w \in Node : (vt2[w][n] = "present") = (vt[w][n] = "present")
      BY <1>2
    <2> QED BY <2>1, QuorumAssumption DEF DP
  <1> QED BY <1>1, <1>3, <1>4, <1>5, <1>6, <1>7

LEMMA QuorumNonEmpty == \A Q \in Quorum : Q # {}
  BY QuorumAssumption

LEMMA NotBothLemma == TypeOK => NotBoth
  <1> SUFFICES ASSUME TypeOK, NEW n \in Node, DecidedAbsent(n), DecidedPresent(n) PROVE FALSE
    BY DEF NotBoth
  <1>1. PICK Q1 \in Quorum : \A v \in Q1 : vote[v][n] = "absent"
    BY DEF DecidedAbsent
  <1>2. PICK Q2 \in Quorum : \A v \in Q2 : vote[v][n] = "present"
    BY DEF DecidedPresent
  <1>3. PICK v \in Q1 \cap Q2 : TRUE
    BY QuorumAssumption
  <1> QED BY <1>1, <1>2, <1>3

\* With every participant having said HaveAll, nobody can hold an ABSENT vote.
LEMMA AllHA_NoAbsent == ASSUME Inv, \A x \in Node : haveAll[x] PROVE \A n \in Node : ~DecidedAbsent(n)
  <1> SUFFICES ASSUME NEW n \in Node, DecidedAbsent(n) PROVE FALSE
    OBVIOUS
  <1>1. PICK Q \in Quorum : \A v \in Q : vote[v][n] = "absent"
    BY DEF DecidedAbsent
  <1>2. PICK v \in Q : TRUE
    BY QuorumNonEmpty
  <1>3. v \in Node
    BY QuorumAssumption
  <1> QED BY <1>1, <1>2, <1>3 DEF Inv

\* Votes, once cast, never change; so a decision, once reached, stays.
LEMMA DecisionsStable ==
  ASSUME TypeOK, TypeOK', \A v, n \in Node : vote[v][n] # "none" => vote'[v][n] = vote[v][n]
  PROVE  \A n \in Node : (DecidedAbsent(n) => DecidedAbsent(n)') /\ (DecidedPresent(n) => DecidedPresent(n)')
  BY QuorumAssumption DEF DecidedAbsent, DecidedPresent

THEOREM InitInv == Init => Inv
  BY QuorumNonEmpty, QuorumAssumption, NoneNotContent
  DEF Init, Inv, TypeOK, Finalised, DecidedAbsent, DecidedPresent

\* ---------------------------------------------------------------- actions
LEMMA CloseInv == ASSUME Inv, NEW n \in Node, NEW S \in SUBSET Ev, Close(n, S) PROVE Inv'
  <1> USE DEF Inv, TypeOK, Finalised
  <1>1. vote' = vote /\ final' = final /\ viaVote' = viaVote /\ heard' = heard
        /\ heardHA' = heardHA /\ haveAll' = haveAll /\ ~closed[n]
    BY DEF Close
  <1>2. \A n2 \in Node : (DecidedAbsent(n2))' = DecidedAbsent(n2) /\ (DecidedPresent(n2))' = DecidedPresent(n2)
    BY <1>1 DEF DecidedAbsent, DecidedPresent
  <1>3. \A m \in Node : Finalised(m) => DecidedAbsent(n)
    BY <1>1
  <1>4. \A n2 \in Node : n2 # n => emitted'[n2] = emitted[n2]
    BY DEF Close
  <1>5. \A m \in Node : Finalised(m) =>
          final'[m] = [x \in Node |-> IF DecidedAbsent(x)' THEN ABSENT ELSE emitted'[x]]
    BY <1>1, <1>2, <1>3, <1>4
  <1> QED BY <1>1, <1>2, <1>3, <1>5 DEF Close

LEMMA HearInv == ASSUME Inv, NEW m \in Node, NEW n \in Node, Hear(m, n) PROVE Inv'
  <1> USE DEF Inv, TypeOK, Finalised
  <1>1. vote' = vote /\ final' = final /\ viaVote' = viaVote /\ emitted' = emitted
        /\ closed' = closed /\ heardHA' = heardHA /\ haveAll' = haveAll
    BY DEF Hear
  <1>2. \A x \in Node : (DecidedAbsent(x))' = DecidedAbsent(x) /\ (DecidedPresent(x))' = DecidedPresent(x)
    BY <1>1 DEF DecidedAbsent, DecidedPresent
  <1> QED BY <1>1, <1>2 DEF Hear

LEMMA HaveAllInv == ASSUME Inv, NEW m \in Node, HaveAll(m) PROVE Inv'
  <1> USE DEF Inv, TypeOK, Finalised
  <1>1. vote' = vote /\ final' = final /\ viaVote' = viaVote /\ emitted' = emitted
        /\ closed' = closed /\ heardHA' = heardHA /\ heard' = heard
    BY DEF HaveAll
  <1>2. \A x \in Node : (DecidedAbsent(x))' = DecidedAbsent(x) /\ (DecidedPresent(x))' = DecidedPresent(x)
    BY <1>1 DEF DecidedAbsent, DecidedPresent
  <1> QED BY <1>1, <1>2 DEF HaveAll

LEMMA HearHAInv == ASSUME Inv, NEW m \in Node, NEW x \in Node, HearHA(m, x) PROVE Inv'
  <1> USE DEF Inv, TypeOK, Finalised
  <1>1. vote' = vote /\ final' = final /\ viaVote' = viaVote /\ emitted' = emitted
        /\ closed' = closed /\ haveAll' = haveAll /\ heard' = heard
    BY DEF HearHA
  <1>2. \A y \in Node : (DecidedAbsent(y))' = DecidedAbsent(y) /\ (DecidedPresent(y))' = DecidedPresent(y)
    BY <1>1 DEF DecidedAbsent, DecidedPresent
  <1> QED BY <1>1, <1>2 DEF HearHA

LEMMA FallSilentInv == ASSUME Inv, NEW n \in Node, FallSilent(n) PROVE Inv'
  <1> USE DEF Inv, TypeOK, Finalised
  <1>1. vote' = vote /\ final' = final /\ viaVote' = viaVote /\ emitted' = emitted
        /\ closed' = closed /\ haveAll' = haveAll /\ heard' = heard /\ heardHA' = heardHA
    BY DEF FallSilent
  <1>2. \A y \in Node : (DecidedAbsent(y))' = DecidedAbsent(y) /\ (DecidedPresent(y))' = DecidedPresent(y)
    BY <1>1 DEF DecidedAbsent, DecidedPresent
  <1> QED BY <1>1, <1>2 DEF FallSilent

LEMMA FinalFastInv == ASSUME Inv, NEW m \in Node, FinalFast(m) PROVE Inv'
  <1> USE DEF Finalised
  <1> DEFINE G == [n \in Node |-> emitted[n]]
  <1>0. TypeOK
    BY DEF Inv
  <1>1. vote' = vote /\ viaVote' = viaVote /\ emitted' = emitted /\ closed' = closed
        /\ haveAll' = haveAll /\ heard' = heard /\ heardHA' = heardHA /\ silent' = silent
        /\ final' = [final EXCEPT ![m] = G] /\ final[m] = NONE /\ heardHA[m] = Node
    BY DEF FinalFast
  <1>2. \A x \in Node : DecidedAbsent(x)' = DecidedAbsent(x) /\ DecidedPresent(x)' = DecidedPresent(x)
    BY <1>1, DecidedIsDA
  <1>3. \A x \in Node : haveAll[x]
    BY <1>1 DEF Inv
  <1>4. \A x \in Node : ~DecidedAbsent(x)
    BY <1>3, AllHA_NoAbsent
  <1>5. \A x \in Node : closed[x]
    BY <1>3 DEF Inv, TypeOK
  <1>6. G \in Content /\ G # NONE
    BY <1>0, AbsentNotSet, NoneNotContent DEF Content, TypeOK
  <1>7. G = [n \in Node |-> IF DecidedAbsent(n) THEN ABSENT ELSE emitted[n]]
    BY <1>4
  <1>8. \A k \in Node : final'[k] = IF k = m THEN G ELSE final[k]
    BY <1>0, <1>1 DEF TypeOK
  <1>9. ~viaVote[m]
    BY <1>1, <1>0 DEF Inv
  <1>10. TypeOK'
    BY <1>0, <1>1, <1>6, <1>8 DEF TypeOK
  <1> QED BY <1>0, <1>1, <1>2, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10 DEF Inv, TypeOK

LEMMA FinalSlowInv == ASSUME Inv, NEW m \in Node, FinalSlow(m) PROVE Inv'
  <1> USE DEF Finalised
  <1> DEFINE F == [n \in Node |-> IF DecidedAbsent(n) THEN ABSENT ELSE emitted[n]]
  <1>0. TypeOK
    BY DEF Inv
  <1>1. vote' = vote /\ emitted' = emitted /\ closed' = closed /\ haveAll' = haveAll
        /\ heard' = heard /\ heardHA' = heardHA /\ silent' = silent
        /\ final' = [final EXCEPT ![m] = F] /\ viaVote' = [viaVote EXCEPT ![m] = TRUE]
        /\ final[m] = NONE
        /\ \A n \in Node : DecidedAbsent(n) \/ (DecidedPresent(n) /\ n \in heard[m])
    BY DEF FinalSlow
  <1>2. \A x \in Node : DecidedAbsent(x)' = DecidedAbsent(x) /\ DecidedPresent(x)' = DecidedPresent(x)
    BY <1>1, DecidedIsDA
  <1>3. \A n \in Node : F[n] \in (SUBSET Ev) \cup {ABSENT}
    BY <1>0 DEF TypeOK
  <1>4. F \in Content /\ F # NONE
    BY <1>3, NoneNotContent DEF Content
  <1>5. \A n \in Node : DecidedAbsent(n) \/ closed[n]
    BY <1>0, <1>1 DEF Inv
  <1>6. \A k \in Node : final'[k] = IF k = m THEN F ELSE final[k]
    BY <1>0, <1>1 DEF TypeOK
  <1>7. \A k \in Node : viaVote'[k] = IF k = m THEN TRUE ELSE viaVote[k]
    BY <1>0, <1>1 DEF TypeOK
  <1>8. TypeOK'
    BY <1>0, <1>1, <1>4, <1>6, <1>7 DEF TypeOK
  <1> QED BY <1>0, <1>1, <1>2, <1>4, <1>5, <1>6, <1>7, <1>8 DEF Inv, TypeOK

LEMMA VotePresentInv == ASSUME Inv, NEW v \in Node, NEW n \in Node, VotePresent(v, n) PROVE Inv'
  <1> USE DEF Finalised
  <1>0. TypeOK
    BY DEF Inv
  <1>1. final' = final /\ viaVote' = viaVote /\ emitted' = emitted /\ closed' = closed
        /\ haveAll' = haveAll /\ heard' = heard /\ heardHA' = heardHA /\ silent' = silent
        /\ vote' = [vote EXCEPT ![v][n] = "present"] /\ vote[v][n] = "none" /\ n \in heard[v]
    BY DEF VotePresent
  <1>2. vote \in VoteType
    BY <1>0 DEF TypeOK, VoteType
  <1>3. /\ vote' \in VoteType
        /\ \A x \in Node : DA(vote', x) = DA(vote, x)
        /\ \A x \in Node : DP(vote, x) => DP(vote', x)
    BY <1>1, <1>2, OneVote
  <1>4. \A x \in Node : DecidedAbsent(x)' = DecidedAbsent(x) /\ (DecidedPresent(x) => DecidedPresent(x)')
    BY <1>3, DecidedIsDA
  <1>5. \A w, y \in Node : vote'[w][y] = IF w = v /\ y = n THEN "present" ELSE vote[w][y]
    BY <1>1, <1>2 DEF VoteType
  <1>6. TypeOK'
    BY <1>0, <1>1, <1>3 DEF TypeOK, VoteType
  <1> QED BY <1>0, <1>1, <1>4, <1>5, <1>6 DEF Inv, TypeOK

LEMMA VoteAbsentInv == ASSUME Inv, NEW v \in Node, NEW n \in Node, VoteAbsent(v, n) PROVE Inv'
  <1> USE DEF Finalised
  <1>0. TypeOK
    BY DEF Inv
  <1>1. final' = final /\ viaVote' = viaVote /\ emitted' = emitted /\ closed' = closed
        /\ haveAll' = haveAll /\ heard' = heard /\ heardHA' = heardHA /\ silent' = silent
        /\ vote' = [vote EXCEPT ![v][n] = "absent"] /\ vote[v][n] = "none"
        /\ n \notin heard[v] /\ ~haveAll[v]
    BY DEF VoteAbsent
  <1>2. vote \in VoteType
    BY <1>0 DEF TypeOK, VoteType
  <1>3. /\ vote' \in VoteType
        /\ \A x \in Node \ {n} : DA(vote', x) = DA(vote, x) /\ DP(vote', x) = DP(vote, x)
        /\ DA(vote, n) => DA(vote', n)
        /\ DP(vote', n) = DP(vote, n)
    BY <1>1, <1>2, OneVote
  <1>4. \A w, y \in Node : vote'[w][y] = IF w = v /\ y = n THEN "absent" ELSE vote[w][y]
    BY <1>1, <1>2 DEF VoteType
  <1>5. TypeOK'
    BY <1>0, <1>1, <1>3 DEF TypeOK, VoteType
  \* the only decision that could change is DecidedAbsent(n); no finalised participant can see it change
  <1>6. \A k \in Node : Finalised(k) => (DA(vote', n) <=> DA(vote, n))
    <2> SUFFICES ASSUME NEW k \in Node, Finalised(k) PROVE (DA(vote', n) <=> DA(vote, n))
      OBVIOUS
    <2>1. CASE ~viaVote[k]
      <3>1. heardHA[k] = Node
        BY <2>1 DEF Inv
      <3>2. haveAll[v]
        BY <3>1, <1>0 DEF Inv, TypeOK
      <3> QED BY <3>2, <1>1
    <2>2. CASE viaVote[k]
      <3>1. DA(vote, n) \/ DP(vote, n)
        BY <2>2, DecidedIsDA DEF Inv
      <3>2. CASE DA(vote, n)
        BY <3>2, <1>3
      <3>3. CASE DP(vote, n)
        <4>1. DP(vote', n)
          BY <3>3, <1>3
        <4>2. ~DA(vote', n)
          BY <4>1, <1>3, NotBothAny
        <4>3. ~DA(vote, n)
          BY <3>3, <1>2, NotBothAny
        <4> QED BY <4>2, <4>3
      <3> QED BY <3>1, <3>2, <3>3
    <2> QED BY <2>1, <2>2
  <1>7. \A k \in Node : Finalised(k) => \A x \in Node : (DecidedAbsent(x)' <=> DecidedAbsent(x))
    <2> SUFFICES ASSUME NEW k \in Node, Finalised(k), NEW x \in Node PROVE (DecidedAbsent(x)' <=> DecidedAbsent(x))
      OBVIOUS
    <2>1. CASE x = n
      <3>0. k \in Node /\ final[k] # NONE
        OBVIOUS
      <3>1. (DA(vote', n) <=> DA(vote, n))
        <4>1. \A kk \in Node : final[kk] # NONE => (DA(vote', n) <=> DA(vote, n))
          BY <1>6
        <4> QED BY <4>1, <3>0
      <3> QED BY <2>1, <3>1 DEF DecidedAbsent, DA
    <2>2. CASE x # n
      <3>1. x \in Node \ {n}
        BY <2>2
      <3>2. DA(vote', x) <=> DA(vote, x)
        BY <3>1, <1>3
      <3> QED BY <3>2 DEF DecidedAbsent, DA
    <2> QED BY <2>1, <2>2
  <1>8. \A x \in Node : (DecidedAbsent(x) => DecidedAbsent(x)') /\ (DecidedPresent(x) => DecidedPresent(x)')
    BY <1>3, DecidedIsDA
  <1> QED BY <1>0, <1>1, <1>4, <1>5, <1>7, <1>8 DEF Inv, TypeOK

LEMMA StutterInv == ASSUME Inv, UNCHANGED vars PROVE Inv'
  <1> USE DEF Inv, TypeOK, Finalised, vars
  <1>1. \A x \in Node : (DecidedAbsent(x))' = DecidedAbsent(x) /\ (DecidedPresent(x))' = DecidedPresent(x)
    BY DEF DecidedAbsent, DecidedPresent
  <1> QED BY <1>1

THEOREM Inductive == Inv /\ [Next]_vars => Inv'
  BY CloseInv, HearInv, HaveAllInv, HearHAInv, FallSilentInv, FinalFastInv, FinalSlowInv,
     VotePresentInv, VoteAbsentInv, StutterInv DEF Next

THEOREM SafetyInv == Spec => []Inv
  BY InitInv, Inductive, PTL DEF Spec

\* ---------------------------------------------------------------- corollaries
THEOREM AgreementThm == Inv => Agreement
  BY DEF Inv, Agreement

THEOREM UniqueChoiceThm == Inv => UniqueChoice
  <1> SUFFICES ASSUME Inv, NEW m1 \in Node, NEW m2 \in Node, Finalised(m1), Finalised(m2)
               PROVE Winner(m1) = Winner(m2)
    BY DEF UniqueChoice
  <1>1. final[m1] = final[m2]
    BY AgreementThm DEF Agreement
  <1>2. Events(m1) = Events(m2)
    BY <1>1 DEF Events
  <1> QED BY <1>2 DEF Winner

THEOREM FastExcludesAbsentThm == Inv => FastExcludesAbsent
  <1> SUFFICES ASSUME Inv, NEW m \in Node, Finalised(m), ~viaVote[m] PROVE \A n \in Node : ~DecidedAbsent(n)
    BY DEF FastExcludesAbsent
  <1>1. \A x \in Node : haveAll[x]
    BY DEF Inv
  <1> QED BY <1>1, AllHA_NoAbsent

THEOREM Main == Spec => [](Agreement /\ UniqueChoice /\ FastExcludesAbsent /\ NotBoth)
  BY SafetyInv, AgreementThm, UniqueChoiceThm, FastExcludesAbsentThm, NotBothLemma, PTL DEF Inv
=============================================================================
