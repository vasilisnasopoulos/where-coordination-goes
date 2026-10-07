---- MODULE TM_Check ----
\* Non-vacuity: a concrete instance satisfies ThreeMoves' assumptions, and a
\* silence-only mechanism (remove a) is Correct in it.
EXTENDS FiniteSets
N == {"a", "b"}  Open == {"a", "b"}
Inv == {{"a"}, {"a", "b"}}          \* a alone can invalidate o
Vals == {0, 1}  Good == {1}
Obs(X, C) == IF "a" \in X /\ C = {} THEN {0} ELSE {0, 1}
INSTANCE ThreeMoves_Proof
Rem == [S \in SUBSET Open |-> {"a"}]
Add == [S \in SUBSET Open |-> {}]
Out == [p \in (SUBSET Open) \X (SUBSET N) |-> 1]
ASSUME Assm
ASSUME Correct(Rem, Add, Out)
ASSUME FOpen = {{"a"}, {"a", "b"}}
\* and without removal (compensation by b only) it is NOT correct:
ASSUME ~Correct([S \in SUBSET Open |-> {}], [S \in SUBSET Open |-> {"b"}], Out)
VARIABLE x
Init == x = 0
Next == UNCHANGED x
====
