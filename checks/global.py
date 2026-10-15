"""Variants silence a FIXED set D (history-dependent silencing is not searched).
MINIMAL_SILENCE §8.17, item 2: per-commitment (ProperAt) vs global Def. 11 (ProperVariant).
Histories = sets R of participants whose invocations took effect after H0 = {} (R1 ⊑ R2 iff R1 ⊆ R2).
Spec: Obs[R] ⊆ Out (nonempty), refinement Leq a partial order on Out; commitment O0 = 0 ∈ Obs[{}].
B3: "O0 has no refinement at R" is upward closed in R; Inv = those R; tau = transversal number of the minimal ones.
A variant silencing D: reachable runs are the R ⊆ N \\ D. Global (Def. 11, all pairs): pick X[R] ⊆ Obs[R], nonempty on every
reachable R, X[{}] ∋ 0, and for R1 ⊆ R2 reachable every o ∈ X[R1] has a refinement in X[R2]. Per-commitment (ProperAt):
only the pairs ({}, R). g = least |D| with a global variant; tau = least with a per-commitment one. Question: is g = tau always?
"""
import itertools, random, sys
def subsets(xs):
    xs = sorted(xs); return [frozenset(c) for r in range(len(xs)+1) for c in itertools.combinations(xs, r)]
def leq_closure(n_out, pairs):
    L = {(a, a) for a in range(n_out)} | set(pairs)
    changed = True
    while changed:
        changed = False
        for (a, b) in list(L):
            for (c, d) in list(L):
                if b == c and (a, d) not in L: L.add((a, d)); changed = True
    return L if all(not ((a, b) in L and (b, a) in L and a != b) for a in range(n_out) for b in range(n_out)) else None
def global_ok(D, N, Obs, L):
    reach = [R for R in subsets(N - D)]                      # includes {}
    reach.sort(key=len, reverse=True)                        # choose larger histories first
    choice = {}
    opts = {R: [frozenset(c) for r in range(1, len(Obs[R])+1) for c in itertools.combinations(sorted(Obs[R]), r)] for R in reach}
    opts[frozenset()] = [x for x in opts[frozenset()] if 0 in x]
    def consistent(R, X):
        for R2, X2 in choice.items():
            lo, hi = (R, R2) if R <= R2 else ((R2, R) if R2 <= R else (None, None))
            if lo is None: continue
            Xlo, Xhi = (X, X2) if lo == R else (X2, X)
            if not all(any((o, o2) in L for o2 in Xhi) for o in Xlo): return False
        return True
    def bt(k):
        if k == len(reach): return True
        R = reach[k]
        for X in opts[R]:
            if consistent(R, X):
                choice[R] = X
                if bt(k + 1): return True
                del choice[R]
        return False
    return bt(0)
def analyse(N, Obs, L):
    refin = {R: any((0, o) in L for o in Obs[R]) for R in subsets(N)}
    Inv = [R for R in subsets(N) if not refin[R]]
    if not all(S in Inv for R in Inv for S in subsets(N) if R <= S): return None   # B3 fails: skip
    F = [S for S in Inv if not any(T < S for T in Inv)]
    tau = min(len(D) for D in subsets(N) if all(D & S for S in F)) if F else 0
    g = min((len(D) for D in subsets(N) if global_ok(D, N, Obs, L)), default=None)
    return tau, g
def run(n, n_out, samples, seed):
    rnd = random.Random(seed); N = frozenset(range(n)); H = subsets(N); seen = sep = none = sep1 = seen1 = 0; ex = None
    for _ in range(samples):
        pairs = [(a, b) for a in range(n_out) for b in range(n_out) if a != b and rnd.random() < 0.3]
        L = leq_closure(n_out, pairs)
        if L is None: continue
        Obs = {R: frozenset(o for o in range(n_out) if rnd.random() < 0.5) or frozenset({rnd.randrange(n_out)}) for R in H}
        Obs[frozenset()] = Obs[frozenset()] | {0}
        r = analyse(N, Obs, L)
        if r is None: continue
        seen += 1; tau, g = r
        seen1 += tau >= 1
        if g is None: none += 1
        elif g != tau:
            sep += 1; sep1 += tau >= 1
            if ex is None: ex = (tau, g, sorted((sorted(R), sorted(Obs[R])) for R in H), sorted(L))
    print(f"n={n} outcomes={n_out}: B3 specifications sampled={seen} (tau>=1: {seen1}), global > tau: {sep} (with tau>=1: {sep1}), no global variant at all: {none}")
    if ex: print("  example (tau, global, Obs, Leq):", ex)
    return sep
if __name__ == "__main__":
    run(2, 3, 20000, 1); run(3, 3, 3000, 2); run(3, 4, 1500, 3)
