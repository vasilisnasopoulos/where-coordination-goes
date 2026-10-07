------------------------------ MODULE CE1_Liar ------------------------------
(* Counterexample 1 -- a lying closure. Participant a may issue one         *)
(* invocation and a closure; two replicas decide "a contributes nothing"    *)
(* once they see a's closure without an invocation before it.               *)
(* Liar = FALSE: a broadcasts the same sequence to both, never acts after  *)
(*   closing -> Agreement must hold (the theorem's setting).                *)
(* Liar = TRUE : a may send different sequences / act after closing ->      *)
(*   TLC must find a violation (outside the setting, as stated).            *)
EXTENDS Sequences, Naturals
CONSTANT Liar
R == {"r1", "r2"}
VARIABLES ch, closedA, dec, cnt
vars == <<ch, closedA, dec, cnt>>

Init == /\ ch = [r \in R |-> <<>>]
        /\ closedA = FALSE
        /\ dec = [r \in R |-> "none"]
        /\ cnt = [r \in R |-> 0]

\* honest: one broadcast to all replicas, no invocation after closing
Bcast(m) == /\ ~Liar
            /\ m = "inv" => ~closedA
            /\ \A r \in R : Len(ch[r]) < 2
            /\ ch' = [r \in R |-> Append(ch[r], m)]
            /\ closedA' = (closedA \/ m = "close")
            /\ UNCHANGED <<dec, cnt>>
\* liar: any message to any single replica, at any time
Send(m, r) == /\ Liar
              /\ Len(ch[r]) < 2
              /\ ch' = [ch EXCEPT ![r] = Append(@, m)]
              /\ closedA' = (closedA \/ m = "close")
              /\ UNCHANGED <<dec, cnt>>

Recv(r) == /\ ch[r] # <<>>
           /\ LET m == Head(ch[r]) IN
                /\ ch' = [ch EXCEPT ![r] = Tail(@)]
                /\ IF m = "inv" /\ dec[r] = "none"
                     THEN cnt' = [cnt EXCEPT ![r] = 1] ELSE UNCHANGED cnt
                /\ IF m = "close" /\ dec[r] = "none"
                     THEN dec' = [dec EXCEPT ![r] = IF cnt[r] = 0 THEN "zero" ELSE "one"]
                     ELSE UNCHANGED dec
           /\ UNCHANGED closedA

Next == \/ \E m \in {"inv", "close"} : Bcast(m)
        \/ \E m \in {"inv", "close"}, r \in R : Send(m, r)
        \/ \E r \in R : Recv(r)
Spec == Init /\ [][Next]_vars

Agreement == ~(\E r1, r2 \in R : dec[r1] = "zero" /\ dec[r2] = "one")
=============================================================================
