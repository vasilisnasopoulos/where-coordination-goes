------------------------------ MODULE CalmEscrow ------------------------------
(***************************************************************************)
(* Where coordination sits for a BOUNDED commitment: a budget of units,     *)
(* each unit to at most one purchase ("never below zero"). In Complete CALM *)
(* (arXiv 2602.09435) this is a non-I-confluent invariant (Sec. 7.2) and    *)
(* has the shape of the bounded-cardinality / renaming row of Appendix F.   *)
(*                                                                         *)
(* Coordination BEFORE the decision: units are split into per-participant   *)
(* shares ahead of time (escrow — O'Neil 1986; demarcation, Barbara &       *)
(* Garcia-Molina 1992). A purchase then reads and writes ONLY state owned   *)
(* by the participant that takes it: no message, no vote, whatever the      *)
(* network does. The price is a REFUSAL when the local share is exhausted   *)
(* while another share still has units. Moving units between shares is     *)
(* the only step that involves two participants, and it happens off the     *)
(* decision path.                                                           *)
(*                                                                         *)
(* Abstract model; says nothing about how any implementation stores shares. *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Node, Unit, Purchase, Share0, FREE

ASSUME ShareAssumption ==
  /\ Share0 \in [Node -> SUBSET Unit]
  /\ \A n1, n2 \in Node : n1 # n2 => Share0[n1] \cap Share0[n2] = {}
  /\ UNION {Share0[n] : n \in Node} = Unit
ASSUME FreeNotPurchase == FREE \notin Purchase

VARIABLES share,    \* [Node -> SUBSET Unit]   current owner of each unit
          taken,    \* [Unit -> Purchase \cup {FREE}]
          asked,    \* [Purchase -> Node \cup {FREE}]   where purchase p was made
          refused,  \* SUBSET Purchase   refused although some unit was free somewhere
          moves     \* Nat               coordinated share transfers (two participants)

vars == <<share, taken, asked, refused, moves>>

TypeOK ==
  /\ share \in [Node -> SUBSET Unit]
  /\ taken \in [Unit -> Purchase \cup {FREE}]
  /\ asked \in [Purchase -> Node \cup {FREE}]
  /\ refused \subseteq Purchase
  /\ moves \in Nat

Init ==
  /\ share = Share0
  /\ taken = [u \in Unit |-> FREE]
  /\ asked = [p \in Purchase |-> FREE]
  /\ refused = {}
  /\ moves = 0

FreeIn(n) == {u \in share[n] : taken[u] = FREE}

\* The decision. Guard and effect touch only share[n] and the units in it.
Buy(n, p) ==
  /\ asked[p] = FREE
  /\ asked' = [asked EXCEPT ![p] = n]
  /\ IF FreeIn(n) # {}
       THEN /\ taken' = [taken EXCEPT ![CHOOSE u \in FreeIn(n) : TRUE] = p]
            /\ UNCHANGED refused
       ELSE /\ refused' = IF \E u \in Unit : taken[u] = FREE THEN refused \cup {p} ELSE refused
            /\ UNCHANGED taken
  /\ UNCHANGED <<share, moves>>

\* Coordination, off the decision path: a free unit changes owner (both sides involved).
Move(from, to, u) ==
  /\ from # to /\ u \in share[from] /\ taken[u] = FREE
  /\ share' = [share EXCEPT ![from] = @ \ {u}, ![to] = @ \cup {u}]
  /\ moves' = moves + 1
  /\ UNCHANGED <<taken, asked, refused>>

Next == \/ \E n \in Node, p \in Purchase : Buy(n, p)
        \/ \E f, t \in Node, u \in Unit : Move(f, t, u)

Spec == Init /\ [][Next]_vars

(*************************** what is checked ******************************)
Approved(p) == \E u \in Unit : taken[u] = p

\* Never below zero, in its renaming form: no unit serves two purchases, and every
\* approved purchase holds exactly one unit -> approved purchases <= |Unit|.
NoUnitTwice    == \A u1, u2 \in Unit : (u1 # u2 /\ taken[u1] # FREE) => taken[u1] # taken[u2]
NeverBelowZero == Cardinality({p \in Purchase : Approved(p)}) <= Cardinality(Unit)

\* Shares stay a partition: no unit owned twice, none lost.
Partition == /\ \A n1, n2 \in Node : n1 # n2 => share[n1] \cap share[n2] = {}
             /\ UNION {share[n] : n \in Node} = Unit

\* The decision is local: a unit is taken only by a purchase made where the unit is.
LocalDecision == \A u \in Unit : taken[u] # FREE => \E n \in Node : u \in share[n] /\ asked[taken[u]] = n

Inv == TypeOK /\ Partition /\ NoUnitTwice /\ LocalDecision
=============================================================================
