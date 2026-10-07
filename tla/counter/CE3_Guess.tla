------------------------------ MODULE CE3_Guess ------------------------------
(* Counterexample 3 -- probabilistic correctness ("commit and hope").       *)
(* o = "a takes nothing in this scope", committed while a is still open,    *)
(* with no silence commitment. TLC cannot weigh probabilities; it shows the *)
(* bad run exists. A spec that accepts "correct with probability p" admits  *)
(* that run, so the necessity half does not apply to it -- as stated.       *)
VARIABLES aTook, committed
vars == <<aTook, committed>>
Init == aTook = FALSE /\ committed = FALSE
Next == \/ (~committed /\ committed' = TRUE /\ UNCHANGED aTook)
        \/ (~aTook /\ aTook' = TRUE /\ UNCHANGED committed)
Spec == Init /\ [][Next]_vars
Safe == committed => ~aTook
=============================================================================
