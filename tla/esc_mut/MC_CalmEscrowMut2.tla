---- MODULE MC_CalmEscrowMut2 ----
EXTENDS CalmEscrowMut2, TLC
CONSTANTS a, b, c, u1, u2, u3, p1, p2, p3, p4
MC_Share0 == (a :> {u1, u2}) @@ (b :> {u3}) @@ (c :> {})
MC_Bound == moves <= 3
====
