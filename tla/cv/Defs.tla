---- MODULE Defs ----
EXTENDS FiniteSets
cN == {1, 2}
cInv == {{1, 2}}                                              \* alarm: both press
cEff == [A \in SUBSET cN |-> IF A = {1, 2} THEN {1} ELSE A]   \* first-come: 2 silenced
cH0 == [b |-> TRUE, a |-> {}, r |-> {}]
cHist == {cH0} \cup {[b |-> FALSE, a |-> A, r |-> R] : A \in SUBSET cN, R \in SUBSET cN}
cHistOf == [A \in SUBSET cN |-> [R \in SUBSET cN |-> [b |-> FALSE, a |-> A, r |-> R]]]
cOut == {"o", "x"}
cLeq == {<<"o", "o">>, <<"x", "x">>}
cFut == {<<cH0, h>> : h \in cHist}
cObs  == [h \in cHist |-> IF h.b THEN {"o"} ELSE IF h.r \in cInv THEN {"x"} ELSE {"o"}]
cObsP == [h \in cHist |-> IF h.b THEN {"o"} ELSE IF h.r \in cInv THEN {}    ELSE {"o"}]
====
