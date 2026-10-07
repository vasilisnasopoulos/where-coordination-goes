---------------------------- MODULE ThreeMoves_Proof ----------------------------
(* Every mechanism has three moves, and only one of them is coordination.  *)
(*                                                                          *)
(* In the extension where coalition S acts, a mechanism may                 *)
(*   (2) REMOVE: make the invocations of Rem[S] ineffective (silence);      *)
(*   (3) ADD:    ask participants Add[S] to issue compensating invocations; *)
(*   (1) CHOOSE: report any outcome admissible for the resulting history.   *)
(* Participants are free (MINIMAL_SILENCE §0): a mechanism cannot force an  *)
(* invocation; any asked participant may crash or decline. K = those who   *)
(* do not follow through. Protocol actions are not invocations and do not  *)
(* change outcomes, except through the specification itself -- in which    *)
(* case they are already inside Inv.                                        *)
(*                                                                          *)
(* Proved: if the mechanism keeps o correct in every extension and for     *)
(* every K, then it REMOVES someone in every open invalidating coalition;   *)
(* moves (1) and (3) contribute nothing. With removal fixed at H, the least *)
(* number removed is the hitting number (MinimalSilence_Proof).             *)
EXTENDS FiniteSets, TLAPS

CONSTANTS N, Open, Inv,
          Vals,          \* possible outcomes
          Good,          \* outcomes that refine o
          Obs(_, _)      \* Obs(X, C): outcomes admissible when the effective
                         \* actors are X and C issued compensations

ASSUME Assm ==
  /\ Open \subseteq N
  /\ Inv \subseteq SUBSET N
  /\ Good \subseteq Vals
  /\ \A X, C \in SUBSET N : Obs(X, C) \subseteq Vals
  \* Inv means: with no compensation, NO admissible outcome refines o
  /\ \A X \in SUBSET N : (X \in Inv) <=> ~\E v \in Obs(X, {}) : v \in Good

FOpen == {S \in Inv : S \subseteq Open}

\* A mechanism: removal, request for compensation, and outcome choice.
Correct(Rem, Add, Out) ==
  \A S \in SUBSET Open, K \in SUBSET N :
     LET X == S \ Rem[S]
         C == Add[S] \ K
     IN  /\ Out[<<S, K>>] \in Obs(X, C)
         /\ Out[<<S, K>>] \in Good

Mechs == [SUBSET Open -> SUBSET N] \X [SUBSET Open -> SUBSET N]
           \X [(SUBSET Open) \X (SUBSET N) -> Vals]

THEOREM OnlyRemovalSaves ==
  \A m \in Mechs :
     Correct(m[1], m[2], m[3]) => \A S \in FOpen : S \cap m[1][S] # {}
<1> SUFFICES ASSUME NEW m \in Mechs, Correct(m[1], m[2], m[3]),
                    NEW S \in FOpen, S \cap m[1][S] = {}
             PROVE FALSE
  OBVIOUS
<1> DEFINE Rem == m[1]  Add == m[2]  Out == m[3]
<1>1. S \in SUBSET Open /\ S \in Inv  BY DEF FOpen
<1>2. Rem \in [SUBSET Open -> SUBSET N] /\ Add \in [SUBSET Open -> SUBSET N]
  BY DEF Mechs
<1>3. Add[S] \in SUBSET N  BY <1>1, <1>2
\* the adversary: everyone asked to compensate declines (K = Add[S])
<1>4. S \ Rem[S] = S  OBVIOUS
<1>5. Add[S] \ Add[S] = {}  OBVIOUS
<1>6. Out[<<S, Add[S]>>] \in Obs(S, {}) /\ Out[<<S, Add[S]>>] \in Good
  BY <1>1, <1>3, <1>4, <1>5 DEF Correct
<1>7. S \in SUBSET N  BY <1>1, Assm
<1>8. ~\E v \in Obs(S, {}) : v \in Good  BY <1>1, <1>7, Assm
<1> QED BY <1>6, <1>8

\* Move (1) alone never saves: without removal and without compensation,
\* no choice of outcome refines o for an invalidating coalition.
THEOREM ChoiceAlone ==
  \A S \in FOpen : ~\E v \in Obs(S, {}) : v \in Good
BY Assm DEF FOpen

\* Move (3) alone never saves: compensation that may be declined.
THEOREM CompensationAlone ==
  \A Add \in [SUBSET Open -> SUBSET N], Out \in [(SUBSET Open) \X (SUBSET N) -> Vals] :
     \A S \in FOpen :
        ~(\A K \in SUBSET N : Out[<<S, K>>] \in Obs(S, Add[S] \ K) /\ Out[<<S, K>>] \in Good)
<1> SUFFICES ASSUME NEW Add \in [SUBSET Open -> SUBSET N],
                    NEW Out \in [(SUBSET Open) \X (SUBSET N) -> Vals],
                    NEW S \in FOpen,
                    \A K \in SUBSET N : Out[<<S, K>>] \in Obs(S, Add[S] \ K) /\ Out[<<S, K>>] \in Good
             PROVE FALSE
  OBVIOUS
<1>1. S \in SUBSET Open /\ S \in Inv /\ S \in SUBSET N  BY Assm DEF FOpen
<1>2. Add[S] \in SUBSET N /\ Add[S] \ Add[S] = {}  BY <1>1
<1>3. Out[<<S, Add[S]>>] \in Obs(S, {}) /\ Out[<<S, Add[S]>>] \in Good  BY <1>2
<1> QED BY <1>1, <1>3, Assm
================================================================================
