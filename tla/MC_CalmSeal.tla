---- MODULE MC_CalmSeal ----
EXTENDS CalmSeal, TLC
CONSTANTS a, b, c, e1, e2, e3
MC_Owner == (e1 :> a) @@ (e2 :> b) @@ (e3 :> c)
MC_Rank  == (e1 :> 2) @@ (e2 :> 0) @@ (e3 :> 1)
MC_Quorum == {{a, b}, {a, c}, {b, c}, {a, b, c}}
====
