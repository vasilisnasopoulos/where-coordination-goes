--------------------------- MODULE CalmEscrow_Proof ---------------------------
(***************************************************************************)
(* TLAPS proof that the escrow invariant is inductive, for ANY finite or    *)
(* infinite sets of participants, units and purchases: shares stay a        *)
(* partition, no unit ever serves two purchases, and every unit is taken    *)
(* only by a purchase made at the participant that owns it (the decision   *)
(* is local).  NeverBelowZero (a cardinality bound) follows from            *)
(* NoUnitTwice for finite Unit; it is checked by TLC, not proved here.     *)
(***************************************************************************)
EXTENDS CalmEscrow, TLAPS

ASSUME FreeNotNode == FREE \notin Node

THEOREM InitInv == Init => Inv
  BY ShareAssumption, FreeNotPurchase DEF Init, Inv, TypeOK, Partition, NoUnitTwice, LocalDecision

LEMMA BuyInv == ASSUME Inv, NEW n \in Node, NEW p \in Purchase, Buy(n, p) PROVE Inv'
  <1> USE DEF Inv, TypeOK, Partition, NoUnitTwice, LocalDecision, FreeIn
  <1>1. CASE FreeIn(n) # {}
    <2> DEFINE w == CHOOSE u \in FreeIn(n) : TRUE
    <2>1. w \in share[n] /\ taken[w] = FREE
      BY <1>1
    <2>2. taken' = [taken EXCEPT ![w] = p] /\ asked' = [asked EXCEPT ![p] = n]
      BY <1>1 DEF Buy
    <2>3. asked[p] = FREE
      BY DEF Buy
    <2>4. \A u \in Unit : taken[u] # p
      <3> SUFFICES ASSUME NEW u \in Unit, taken[u] = p PROVE FALSE
        OBVIOUS
      <3>1. taken[u] # FREE
        BY FreeNotPurchase
      <3>2. \E m \in Node : asked[taken[u]] = m
        BY <3>1
      <3> QED BY <3>2, <2>3, FreeNotNode
    <2>5. TypeOK'
      BY <2>1, <2>2, <1>1 DEF Buy
    <2>6. Partition'
      BY DEF Buy
    <2>7. NoUnitTwice'
      BY <2>1, <2>2, <2>4
    <2>8. LocalDecision'
      BY <2>1, <2>2, <2>3, <2>4, FreeNotNode DEF Buy
    <2> QED BY <2>5, <2>6, <2>7, <2>8
  <1>2. CASE FreeIn(n) = {}
    BY <1>2, FreeNotNode DEF Buy
  <1> QED BY <1>1, <1>2

LEMMA MoveInv == ASSUME Inv, NEW f \in Node, NEW t \in Node, NEW u \in Unit, Move(f, t, u) PROVE Inv'
  <1> USE DEF Inv, TypeOK
  <1>1. f # t /\ u \in share[f] /\ taken[u] = FREE
    BY DEF Move
  <1>2. share' = [share EXCEPT ![f] = @ \ {u}, ![t] = @ \cup {u}]
        /\ taken' = taken /\ asked' = asked /\ refused' = refused /\ moves' = moves + 1
    BY DEF Move
  <1>3. share'[f] = share[f] \ {u} /\ share'[t] = share[t] \cup {u}
        /\ \A n \in Node \ {f, t} : share'[n] = share[n]
    BY <1>1, <1>2
  <1>4. TypeOK'
    BY <1>1, <1>2, <1>3
  <1>5. (\A n1, n2 \in Node : n1 # n2 => share[n1] \cap share[n2] = {})'
    <2> SUFFICES ASSUME NEW n1 \in Node, NEW n2 \in Node, n1 # n2
                 PROVE share'[n1] \cap share'[n2] = {}
      OBVIOUS
    <2>0. \A n \in Node : n # f => u \notin share[n]
      BY <1>1 DEF Partition
    <2>a. CASE n1 = f /\ n2 = t
      BY <2>a, <1>1, <1>3 DEF Partition
    <2>b. CASE n1 = t /\ n2 = f
      BY <2>b, <1>1, <1>3 DEF Partition
    <2>c. CASE n1 = f /\ n2 \notin {f, t}
      BY <2>c, <1>3 DEF Partition
    <2>d. CASE n2 = f /\ n1 \notin {f, t}
      BY <2>d, <1>3 DEF Partition
    <2>e. CASE n1 = t /\ n2 \notin {f, t}
      BY <2>e, <2>0, <1>3 DEF Partition
    <2>g. CASE n2 = t /\ n1 \notin {f, t}
      BY <2>g, <2>0, <1>3 DEF Partition
    <2>h. CASE n1 \notin {f, t} /\ n2 \notin {f, t}
      BY <2>h, <1>3 DEF Partition
    <2> QED BY <2>a, <2>b, <2>c, <2>d, <2>e, <2>g, <2>h
  <1>6. (UNION {share[n] : n \in Node} = Unit)'
    <2>1. \A w \in Unit : \E n \in Node : w \in share'[n]
      <3> SUFFICES ASSUME NEW w \in Unit PROVE \E n \in Node : w \in share'[n]
        OBVIOUS
      <3>1. \E n \in Node : w \in share[n]
        BY DEF Partition
      <3> QED BY <3>1, <1>1, <1>3
    <2>2. \A n \in Node : share'[n] \subseteq Unit
      BY <1>4
    <2> QED BY <2>1, <2>2
  <1>7. Partition'
    BY <1>5, <1>6 DEF Partition
  <1>8. NoUnitTwice'
    BY <1>2 DEF NoUnitTwice
  <1>9. LocalDecision'
    <2> SUFFICES ASSUME NEW w \in Unit, taken'[w] # FREE
                 PROVE \E n \in Node : w \in share'[n] /\ asked'[taken'[w]] = n
      BY DEF LocalDecision
    <2>1. w # u
      BY <1>1, <1>2
    <2>2. \E n \in Node : w \in share[n] /\ asked[taken[w]] = n
      BY <1>2 DEF LocalDecision
    <2> QED BY <2>1, <2>2, <1>2, <1>3
  <1> QED BY <1>4, <1>7, <1>8, <1>9

LEMMA StutterInv == ASSUME Inv, UNCHANGED vars PROVE Inv'
  BY DEF vars, Inv, TypeOK, Partition, NoUnitTwice, LocalDecision

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'
    BY BuyInv, MoveInv, StutterInv DEF Next
  <1> QED BY <1>1, <1>2, PTL DEF Spec
=============================================================================
