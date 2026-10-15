"""Two commitments in sequence (two layers): how many silences in total?
Model (abstract, as MINIMAL_SILENCE §1, §8.2): participants N; a silence about i persists for the scope (i's later
invocations never count again), so a coalition with a silenced member can no longer break anything.
Layer j needs the silenced set to hit every coalition of F_j.
  offline: F1 and F2 known up front            -> least |D| hitting F1 ∪ F2           = tau(F1 ∪ F2)
  online : D1 chosen for F1, then F2 revealed   -> min over D1 hitting F1 of max over F2 of (|D1| + least extra to hit F2)
           (F2 ranges over a given set of possible second families: the environment picks it after D1, Determinations' online setting)
Checks, exhaustively for |N| <= 4: max(t1,t2) <= offline <= t1+t2, offline <= online <= t1 + max t2, and whether online > offline occurs.
"""
import itertools, sys
def subsets(xs):
    xs = list(xs)
    for r in range(len(xs) + 1):
        for c in itertools.combinations(xs, r): yield frozenset(c)
def hits(D, F): return all(D & S for S in F)
def tau(F, N):
    for D in subsets(N):
        if hits(D, F): return len(D)
def extra(D, F, N):  # least number of new silences so that D ∪ E hits F
    rest = [S for S in F if not (D & S)]
    return tau(rest, N - D) if rest else 0
def minimal(F):  # keep only minimal coalitions (antichain), as F_open is defined
    return frozenset(S for S in F if not any(T < S for T in F))
def families(N, maxsize):
    nonempty = [S for S in subsets(N) if S]
    for r in range(1, maxsize + 1):
        for c in itertools.combinations(nonempty, r):
            F = minimal(frozenset(c))
            if len(F) == r: yield F
def main(n, fam_max, seconds_max):
    N = frozenset(range(n)); fams = list(families(N, fam_max))
    viol = 0; gaps = []; checked = 0
    for F1 in fams:
        t1 = tau(F1, N)
        for k in range(1, seconds_max + 1):
            for F2s in itertools.combinations(fams, k):      # the environment's possible second families
                t2max = max(tau(F2, N) for F2 in F2s)
                off = max(tau(F1 | F2, N) for F2 in F2s)      # worst case, but F2 known before choosing
                on = min(len(D1) + max(extra(D1, F2, N) for F2 in F2s)
                         for D1 in subsets(N) if hits(D1, F1))
                checked += 1
                for F2 in F2s:
                    t2 = tau(F2, N); u = tau(F1 | F2, N)
                    if not (max(t1, t2) <= u <= t1 + t2): viol += 1
                if not (off <= on <= t1 + t2max): viol += 1
                if on > off and len(gaps) < 3: gaps.append((sorted(map(sorted, F1)), [sorted(map(sorted, F)) for F in F2s], t1, t2max, off, on))
    print(f"n={n} families={len(fams)} cases={checked} bound violations={viol}")
    for g in gaps: print("  online > offline:", g)
    return viol
if __name__ == "__main__":
    v = main(3, 3, 2) + main(4, 2, 2)
    sys.exit(1 if v else 0)
