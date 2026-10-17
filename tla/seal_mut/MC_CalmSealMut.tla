---- MODULE MC_CalmSealMut ----
EXTENDS CalmSealMut, TLC
CONSTANTS a, b, c, e1, e2
MC_Owner == (e1 :> a) @@ (e2 :> b)
MC_Rank  == (e1 :> 1) @@ (e2 :> 0)
MC_Quorum == {{a, b}, {a, c}, {b, c}, {a, b, c}}
====
