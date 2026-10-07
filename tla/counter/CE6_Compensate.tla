---------------------------- MODULE CE6_Compensate ----------------------------
(* Candidate counterexample 6 -- a mechanism that ADDS an action instead   *)
(* of silencing. Outcome o: "net effect of the scope is 0", committed while*)
(* a is still open (a may take one unit). Mechanism: if a takes, b must     *)
(* give one back. Nobody is silenced.                                       *)
(* Auto = FALSE: b is a participant (may crash before compensating).       *)
(*   If TLC finds a final state with net # 0, "force someone to act" is not *)
(*   a safe mechanism in the asynchronous crash model -> 2(b) stands.       *)
(* Auto = TRUE : compensation is a deterministic rule applied by every      *)
(*   replica together with a's take. Then {a} does not invalidate o at all  *)
(*   (F_open = {}), the theorem says tau = 0 -- must hold, no silence.       *)
EXTENDS Integers
CONSTANT Auto
VARIABLES net, aTook, bUp, committed
vars == <<net, aTook, bUp, committed>>

Init == net = 0 /\ aTook = FALSE /\ bUp = TRUE /\ committed = FALSE

Commit == ~committed /\ committed' = TRUE /\ UNCHANGED <<net, aTook, bUp>>
ATake  == /\ ~aTook /\ aTook' = TRUE
          /\ net' = IF Auto THEN net ELSE net - 1
          /\ UNCHANGED <<bUp, committed>>
BGive  == ~Auto /\ bUp /\ aTook /\ net < 0 /\ net' = net + 1 /\ UNCHANGED <<aTook, bUp, committed>>
BCrash == ~Auto /\ bUp /\ bUp' = FALSE /\ UNCHANGED <<net, aTook, committed>>

Next == Commit \/ ATake \/ BGive \/ BCrash
Spec == Init /\ [][Next]_vars

\* o must hold in every quiescent state after the commit
SafeAtRest == (committed /\ ~ENABLED Next) => net = 0
=============================================================================
