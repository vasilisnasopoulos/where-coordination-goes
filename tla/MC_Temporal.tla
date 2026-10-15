---- MODULE MC_Temporal ----
EXTENDS Temporal_Proof
\* alarm "both 0 and 1 press" over 3 participants: Inv = supersets of {0,1}, tau = 1
MCInv == {S \in SUBSET {0,1,2} : {0,1} \subseteq S}
SafeAny == Broken = FALSE
\* lower bound as a state predicate for runs of the policy D = {0}
LB == (acted = Open /\ ~Broken) => 1 <= Cardinality(ref \cup Pending)
NextD == PolicyNext({0})
NextNone == PolicyNext({})
====
