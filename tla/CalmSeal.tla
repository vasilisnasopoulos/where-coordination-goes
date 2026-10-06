------------------------------- MODULE CalmSeal -------------------------------
(***************************************************************************)
(* Where coordination sits for TOTAL-ORDER and UNIQUE-CHOICE commitment     *)
(* (the two non-monotone patterns of Hellerstein, "Complete CALM",          *)
(* arXiv 2602.09435, Appendix F, Lemmas 2 and 3 with k = 1).                *)
(*                                                                         *)
(* One period. Every participant puts events in the period and then         *)
(* CLOSES it (its content is frozen from then on). Two ways to make the      *)
(* period final, and only one of them is a vote:                            *)
(*                                                                         *)
(*  FAST, no vote: a participant that has every participant's closed        *)
(*  content says so (HaveAll); one that has heard HaveAll from everyone      *)
(*  finalises. Both steps are threshold checks over a KNOWN membership —     *)
(*  monotone in the sense of Complete CALM, Remark 3 / Theorem 8.            *)
(*                                                                         *)
(*  SLOW, a vote: for each participant n, a quorum votes PRESENT (it holds   *)
(*  n's closed content) or ABSENT (it does not). A voter that said HaveAll   *)
(*  never votes ABSENT, and one that voted ABSENT never says HaveAll.        *)
(*                                                                         *)
(* The claim checked here: every participant that finalises holds the same  *)
(* content, hence the same deterministic order and the same unique winner;  *)
(* and a vote is needed only for a participant somebody has not heard from  *)
(* — i.e. only on (suspected) silence.                                      *)
(*                                                                         *)
(* Abstract model. It does not describe how any implementation numbers,     *)
(* orders or transports records.                                            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Node,      \* participants (membership fixed once: Complete CALM, Remark 3)
          Ev,        \* possible events
          Owner,     \* [Ev -> Node]: who may put event e in the period
          Rank,      \* [Ev -> Nat], injective: the deterministic order inside a period
          Quorum,    \* set of quorums
          MaxSilent, \* how many participants may fall silent
          ABSENT, NONE

ASSUME QuorumAssumption ==
          /\ Quorum \subseteq SUBSET Node
          /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}
ASSUME OwnerType == Owner \in [Ev -> Node]
ASSUME RankInjective == Rank \in [Ev -> Nat] /\ \A e1, e2 \in Ev : Rank[e1] = Rank[e2] => e1 = e2
\* ABSENT and NONE are distinct from every set of events (TLC: model values; the proof module assumes it)

VARIABLES emitted,   \* [Node -> SUBSET Ev]   what n put in the period
          closed,    \* [Node -> BOOLEAN]     n closed the period (content frozen)
          silent,    \* SUBSET Node           stopped acting, for good
          heard,     \* [Node -> SUBSET Node] whose closed content m holds
          haveAll,   \* [Node -> BOOLEAN]     m announced it holds everyone's
          heardHA,   \* [Node -> SUBSET Node] whose HaveAll m has received
          vote,      \* [Node -> [Node -> {"none","present","absent"}]]
          final,     \* [Node -> NONE or [Node -> (SUBSET Ev) \cup {ABSENT}]]
          viaVote    \* [Node -> BOOLEAN]     m finalised by the slow path

vars == <<emitted, closed, silent, heard, haveAll, heardHA, vote, final, viaVote>>

Content == [Node -> (SUBSET Ev) \cup {ABSENT}]

TypeOK ==
  /\ emitted \in [Node -> SUBSET Ev]
  /\ closed  \in [Node -> BOOLEAN]
  /\ silent  \subseteq Node
  /\ heard   \in [Node -> SUBSET Node]
  /\ haveAll \in [Node -> BOOLEAN]
  /\ heardHA \in [Node -> SUBSET Node]
  /\ vote    \in [Node -> [Node -> {"none", "present", "absent"}]]
  /\ final   \in [Node -> Content \cup {NONE}]
  /\ viaVote \in [Node -> BOOLEAN]

DecidedAbsent(n)  == \E Q \in Quorum : \A v \in Q : vote[v][n] = "absent"
DecidedPresent(n) == \E Q \in Quorum : \A v \in Q : vote[v][n] = "present"

Init ==
  /\ emitted = [n \in Node |-> {}]
  /\ closed  = [n \in Node |-> FALSE]
  /\ silent  = {}
  /\ heard   = [n \in Node |-> {}]
  /\ haveAll = [n \in Node |-> FALSE]
  /\ heardHA = [n \in Node |-> {}]
  /\ vote    = [v \in Node |-> [n \in Node |-> "none"]]
  /\ final   = [n \in Node |-> NONE]
  /\ viaVote = [n \in Node |-> FALSE]

\* n puts some of its own events in the period and closes it in one step (the order of
\* its own emissions does not change what others can observe once it closes).
Close(n, S) ==
  /\ n \notin silent /\ ~closed[n]
  /\ S \subseteq {e \in Ev : Owner[e] = n}
  /\ emitted' = [emitted EXCEPT ![n] = S]
  /\ closed' = [closed EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<silent, heard, haveAll, heardHA, vote, final, viaVote>>

\* m receives n's closed content (asynchronous; any order)
Hear(m, n) ==
  /\ m \notin silent /\ closed[n] /\ n \notin heard[m]
  /\ heard' = [heard EXCEPT ![m] = @ \cup {n}]
  /\ UNCHANGED <<emitted, closed, silent, haveAll, heardHA, vote, final, viaVote>>

HaveAll(m) ==
  /\ m \notin silent /\ ~haveAll[m] /\ heard[m] = Node
  /\ \A n \in Node : vote[m][n] # "absent"
  /\ haveAll' = [haveAll EXCEPT ![m] = TRUE]
  /\ UNCHANGED <<emitted, closed, silent, heard, heardHA, vote, final, viaVote>>

HearHA(m, x) ==
  /\ m \notin silent /\ haveAll[x] /\ x \notin heardHA[m]
  /\ heardHA' = [heardHA EXCEPT ![m] = @ \cup {x}]
  /\ UNCHANGED <<emitted, closed, silent, heard, haveAll, vote, final, viaVote>>

FinalFast(m) ==
  /\ m \notin silent /\ final[m] = NONE /\ heardHA[m] = Node
  /\ final' = [final EXCEPT ![m] = [n \in Node |-> emitted[n]]]
  /\ UNCHANGED <<emitted, closed, silent, heard, haveAll, heardHA, vote, viaVote>>

\* The only non-monotone step. PRESENT needs n's closed content; ABSENT is only
\* possible about someone v has NOT heard, and only if v never said HaveAll.
VotePresent(v, n) ==
  /\ v \notin silent /\ vote[v][n] = "none" /\ n \in heard[v]
  /\ vote' = [vote EXCEPT ![v][n] = "present"]
  /\ UNCHANGED <<emitted, closed, silent, heard, haveAll, heardHA, final, viaVote>>

VoteAbsent(v, n) ==
  /\ v \notin silent /\ vote[v][n] = "none" /\ n \notin heard[v] /\ ~haveAll[v]
  /\ vote' = [vote EXCEPT ![v][n] = "absent"]
  /\ UNCHANGED <<emitted, closed, silent, heard, haveAll, heardHA, final, viaVote>>

FinalSlow(m) ==
  /\ m \notin silent /\ final[m] = NONE
  /\ \A n \in Node : DecidedAbsent(n) \/ (DecidedPresent(n) /\ n \in heard[m])
  /\ final' = [final EXCEPT ![m] =
                 [n \in Node |-> IF DecidedAbsent(n) THEN ABSENT ELSE emitted[n]]]
  /\ viaVote' = [viaVote EXCEPT ![m] = TRUE]
  /\ UNCHANGED <<emitted, closed, silent, heard, haveAll, heardHA, vote>>

FallSilent(n) ==
  /\ n \notin silent /\ Cardinality(silent) < MaxSilent
  /\ silent' = silent \cup {n}
  /\ UNCHANGED <<emitted, closed, heard, haveAll, heardHA, vote, final, viaVote>>

Next ==
  \/ \E n \in Node, S \in SUBSET Ev : Close(n, S)
  \/ \E n \in Node : HaveAll(n) \/ FinalFast(n) \/ FinalSlow(n) \/ FallSilent(n)
  \/ \E m, n \in Node : Hear(m, n) \/ HearHA(m, n) \/ VotePresent(m, n) \/ VoteAbsent(m, n)

Spec == Init /\ [][Next]_vars

(*************************** what is checked ******************************)
Finalised(m) == final[m] # NONE

\* 1. Same content everywhere (TOTAL-ORDER: the order is Rank over the same set)
Agreement == \A m1, m2 \in Node : Finalised(m1) /\ Finalised(m2) => final[m1] = final[m2]

\* 2. Nothing invented: a participant's slot holds exactly what it closed, or ABSENT
Validity == \A m, n \in Node : Finalised(m) =>
              (final[m][n] = ABSENT \/ (closed[n] /\ final[m][n] = emitted[n]))

\* 3. UNIQUE-CHOICE: the winner (first event under the deterministic order Rank) is the same everywhere
Events(m)  == UNION {final[m][n] : n \in {x \in Node : final[m][x] # ABSENT}}
Winner(m)  == IF Events(m) = {} THEN NONE
              ELSE CHOOSE e \in Events(m) : \A e2 \in Events(m) : Rank[e] <= Rank[e2]
UniqueChoice == \A m1, m2 \in Node : Finalised(m1) /\ Finalised(m2) => Winner(m1) = Winner(m2)

\* 4. Votes only on silence: an ABSENT vote is about someone the voter had not heard,
\*    and the fast (vote-free) path never coexists with an ABSENT decision.
FastExcludesAbsent == \A m \in Node : (Finalised(m) /\ ~viaVote[m]) => \A n \in Node : ~DecidedAbsent(n)
NotBoth == \A n \in Node : ~(DecidedAbsent(n) /\ DecidedPresent(n))

\* Inductive invariant (proved in CalmSeal_Proof.tla)
Inv ==
  /\ TypeOK
  /\ \A m, n \in Node : n \in heard[m] => closed[n]
  /\ \A m, x \in Node : x \in heardHA[m] => haveAll[x]
  /\ \A m \in Node : haveAll[m] => heard[m] = Node
  /\ \A v, n \in Node : vote[v][n] = "present" => n \in heard[v]
  /\ \A v, n \in Node : vote[v][n] = "absent" => ~haveAll[v]
  /\ \A m \in Node : (Finalised(m) /\ ~viaVote[m]) => heardHA[m] = Node
  /\ \A m \in Node : Finalised(m) =>
        final[m] = [n \in Node |-> IF DecidedAbsent(n) THEN ABSENT ELSE emitted[n]]
  /\ \A m, n \in Node : Finalised(m) => (DecidedAbsent(n) \/ closed[n])
  /\ \A m \in Node : (Finalised(m) /\ viaVote[m]) => \A n \in Node : DecidedAbsent(n) \/ DecidedPresent(n)
  /\ \A m \in Node : viaVote[m] => Finalised(m)

(*************************** liveness, for TLC ****************************)
\* With nobody silent and nobody suspected (no vote ever cast), the period becomes
\* final through the vote-free path. A spurious suspicion is allowed in Spec and
\* only sends the period down the slow path — it never breaks Agreement.
NextNoVote ==
  \/ \E n \in Node, S \in SUBSET Ev : Close(n, S)
  \/ \E n \in Node : HaveAll(n) \/ FinalFast(n)
  \/ \E m, n \in Node : Hear(m, n) \/ HearHA(m, n)
NoSilenceSpec ==
  /\ Init /\ [][NextNoVote]_vars
  /\ \A n \in Node : WF_vars(\E S \in SUBSET Ev : Close(n, S)) /\ WF_vars(HaveAll(n)) /\ WF_vars(FinalFast(n))
  /\ \A m, x \in Node : WF_vars(Hear(m, x)) /\ WF_vars(HearHA(m, x))
AllFinalEventually == <>(\A m \in Node : Finalised(m))
=============================================================================
