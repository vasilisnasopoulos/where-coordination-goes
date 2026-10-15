"""Which specifications have property B3 as it is PROVED (CoordinatedVariant_Proof.tla: B3 + B3conv)?
A commitment o is modelled by broken(E): does o break when exactly the open participants in E had their invocations take effect?
Inv (§1, existential S-extensions: members of S may or may not act) = {S : some E ⊆ S has broken(E)}.
Proved B3 (both halves)  <=>  broken(E) == (E ∈ Inv) for every E  <=>  broken is upward closed in E.
Then the worst case (everyone open acts) silences >= tau. Checks the paper's examples and the referee's counterexample.
"""
import itertools
def subsets(xs):
    xs = sorted(xs)
    return [frozenset(c) for r in range(len(xs)+1) for c in itertools.combinations(xs, r)]
def analyse(name, N, broken):
    Inv = {S for S in subsets(N) if any(broken(E) for E in subsets(S))}
    b3 = all(broken(E) == (E in Inv) for E in subsets(N))
    F = [S for S in Inv if not any(T < S for T in Inv)]
    tau = min(len(D) for D in subsets(N) if all(D & S for S in F)) if F else 0
    # least, over mechanisms that keep o, of the worst-case number silenced; a mechanism = any choice of effective
    # set E(A) ⊆ A per set A of actors (one-shot: the most powerful; temporal mechanisms are a subset)
    worst = max(min(len(A - E) for E in subsets(A) if not broken(E)) for A in subsets(N))
    print(f"{name:42s} B3={'yes' if b3 else 'NO '}  F_open={sorted(map(sorted, F))}  tau={tau}  least worst-case silenced={worst}")
    return b3, tau, worst
N = frozenset({0, 1, 2})
rows = [
  ("Seal: period content fixed, all 3 open", lambda E: len(E) > 0),
  ("escrow: reclaim silent 0's share", lambda E: 0 in E),
  ("alarm iff 0 and 1 press; commit no alarm", lambda E: {0, 1} <= E),
  ("majority (2 of 3) breaks", lambda E: len(E) >= 2),
  ("referee: alarm iff EXACTLY one of 0,1", lambda E: len(E & {0, 1}) == 1),
]
bad = 0
for name, f in rows:
    if f is None: continue
    b3, tau, worst = analyse(name, N, f)
    if b3 and worst != tau: bad += 1          # the theorem: with B3, least worst case == tau
print("theorem violations among B3 specifications:", bad)

# Exhaustive: every broken() on 3 participants (2^8 = 256 functions), and on 4 (2^16 = 65,536).
for n in (3, 4):
    Nn = frozenset(range(n)); S = subsets(Nn); total = b3s = ok = gap = 0
    for bits in range(1 << len(S)):
        val = {E: bool(bits >> k & 1) for k, E in enumerate(S)}
        if val[frozenset()]: continue                      # o must hold when nobody acts (o is committed at H)
        total += 1
        broken = val.__getitem__
        Inv = {X for X in S if any(broken(E) for E in subsets(X))}
        b3 = all(broken(E) == (E in Inv) for E in S)
        F = [X for X in Inv if not any(T < X for T in Inv)]
        tau = min(len(D) for D in S if all(D & X for X in F)) if F else 0
        worst = max(min(len(A - E) for E in subsets(A) if not broken(E)) for A in S)
        if b3:
            b3s += 1; ok += (worst == tau)
        elif worst < tau: gap += 1
    print(f"n={n}: specifications={total}, with B3={b3s}, B3 and least worst case == tau: {ok}/{b3s}; without B3 and fewer than tau: {gap}")
