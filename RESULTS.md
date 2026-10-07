# Results of the checks in this repository (6 October 2026)

Tools: TLC (tla2tools, Java 26) · TLAPS 1.5.0 (tlapm). TLAPS exits 0 even when obligations fail, so the verdict is the last line.

## TLAPS — proofs for ANY sizes
| module | theorem | verdict |
|---|---|---|
| `CalmEscrow_Proof.tla` | `Safety == Spec => []Inv` — partition of shares · no unit serves two purchases · the decision is local | **All 131 obligations proved** |
| `CalmSeal_Proof.tla` | `Main == Spec => [](Agreement /\ UniqueChoice /\ FastExcludesAbsent /\ NotBoth)` via the inductive `Inv` | **All 330 obligations proved** |
| [`tla/MinimalSilence_Proof.tla`](tla/MinimalSilence_Proof.tla) *(7/10)* | any specification, one commitment: `Safe(D) <=> Hits(D, FOpen)` and `<=> Hits(D, MinFOpen)` — least \|D\| = hitting number (combinatorial core of MINIMAL_SILENCE Thms 1(b), 2(a), 3; + 2(b) mechanism-agnostic, run union, vertex-cover reduction) | **All 112 obligations proved** |
| [`tla/ThreeMoves_Proof.tla`](tla/ThreeMoves_Proof.tla) *(7/10)* | any mechanism = remove + ask for compensation + choose outcome, participants free (may decline/crash): correct ⇒ it removes someone in every open invalidating coalition; choice alone and compensation alone never save | **All 36 obligations proved** · non-vacuity: [`tla/counter/tm/TM_Check.tla`](tla/counter/tm/TM_Check.tla) (TLC: assumptions satisfiable, silence-only mechanism correct, compensation-only not) |

Assumptions used: quorums pairwise intersect (`QuorumAssumption`); shares initially partition the units (`ShareAssumption`); the
markers `FREE`, `ABSENT`, `NONE` are distinct from data values.

## TLC — exhaustive model checking, small sizes

*Counterexamples (7/10): [`tla/counter/RESULTS.md`](tla/counter/RESULTS.md) — 3 breaks at the stated boundaries, 2(b) survives the compensation candidate.*
| model | instance | property | verdict |
|---|---|---|---|
| `MC_CalmEscrow` | 3 participants, 3 units, 4 purchases, ≤ 3 share moves | TypeOK, Partition, NoUnitTwice, **NeverBelowZero**, LocalDecision | **No error.** 62,230 distinct states, complete |
| `MC_CalmSeal` (`_live.cfg`) | 3 participants, 3 events, majority quorums; nobody silent, nobody suspected | **AllFinalEventually** (every participant finalises without a vote) | **No error.** 35,321 distinct states, complete |
| `MC_CalmSeal` (`.cfg`) | same, one participant may fall silent, votes allowed | TypeOK, Agreement, Validity, UniqueChoice, FastExcludesAbsent, NotBoth, Inv | **No error.** 303,544,256 distinct states, **complete** (2.19 billion generated, depth 38, 1 h 08 min). The same invariants are proved for all sizes by TLAPS above. |

## How to read this
- The **safety** of both placements is proved, not sampled.
- The **liveness** claim (no silence ⇒ no vote) is model-checked for three participants only.
- The **conjecture** in PAPER.md §3 (coordination = decisions about silence, in general) is **not** proved by any of this.
