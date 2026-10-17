# Results of the checks in this repository (6–14 October 2026)

Tools: TLC (tla2tools, Java 26) · TLAPS 1.5.0 (tlapm). TLAPS exits 0 even when obligations fail, so the verdict is the last line.

## TLAPS — proofs for ANY sizes
| module | theorem | verdict |
|---|---|---|
| `CalmEscrow_Proof.tla` | `Safety == Spec => []Inv` — partition of shares · no unit serves two purchases · the decision is local; *(17/10)* `NeverBelowZeroThm` (finite Unit; follows from the type alone) · `NoRevokeThm` — an approved purchase stays approved | **All 196 obligations proved** |
| `CalmSeal_Proof.tla` | `Main == Spec => [](Agreement /\ UniqueChoice /\ FastExcludesAbsent /\ NotBoth)` via the inductive `Inv`; *(17/10)* `MainValidity == Spec => []Validity` | **All 340 obligations proved** |
| [`tla/MinimalSilence_Proof.tla`](tla/MinimalSilence_Proof.tla) *(7/10)* | one commitment, any upward-closed family of breaking coalitions: `Safe(D) <=> Hits(D, FOpen)` and `<=> Hits(D, MinFOpen)` — least \|D\| = hitting number (combinatorial core of MINIMAL_SILENCE Thms 1(b), 2(a), 3; + 2(b) mechanism-agnostic, run union, vertex-cover reduction) | **All 112 obligations proved** |
| [`tla/CoordinatedVariant_Proof.tla`](tla/CoordinatedVariant_Proof.tla) *(9/10)* | MINIMAL_SILENCE §8.12, both bounds in Complete CALM's terms: `LemmaA` — a properly coordinated variant (Def. 11) forbids every future that breaks o; `OnlySilence` — for every specification the run it lets take effect never breaks o (the lever "whose invocations count" models Def. 5 for implementations that accept or refuse); `NoVariantIfAttemptsBreak`; `LemmaB`/`Chain` — with B3 it silences ≥ τ; `Sufficiency`/`Exactly` — silencing a minimum transversal is a proper (at the commitment), realizable variant that silences exactly τ. TLC: `tla/cv/tlc_MC_CV.out`, `tla/cv/tlc_MC_Suff.out` (τ = 1); mutants `tlc_MC_CV_mut.out`, `tlc_MC_Suff_mut.out` (silencing nobody) fail | **All 183 obligations proved** (15/10: + `GlobalImpliesAt`, §8.17; + `LemmaAAt`, `LemmaBAt`, `ChainAt`, `ExactlyAt` — both bounds under the per-commitment Def. 11; `PerRunLowerBound` — any order, deferral or partial knowledge; MINIMAL_SILENCE §8.16) · B3 exhaustively: [`checks/b3.py`](checks/b3.py) |
| [`tla/Membership_Proof.tla`](tla/Membership_Proof.tla) *(10/10)* | MINIMAL_SILENCE §8.7: `JoinSafe`, `JoinKeepsTau` — a newcomer that counts only in later scopes leaves every earlier commitment's safe sets and τ unchanged; `LeaveSafe`, `LeaveTau` — removing i changes τ by at most one. TLC model (`tla/mb/tlc_MC_Membership.out`): join keeps τ = 2, leave gives 1; mutant `tlc_MC_Membership_mut.out` (newcomer counts in the old scope) fails | **All 161 obligations proved** |
| [`tla/B3Patterns_Proof.tla`](tla/B3Patterns_Proof.tla) *(15/10)* | MINIMAL_SILENCE §8.16: if breaking is upward closed in the counted events, B3 and B3conv hold (`MonoBroken`, `B3Holds`, `InvUpClosed`); instances Seal, before-w (unique choice, total order), more-than-k (unit budget) are upward closed (`SealUp`, `BeforeUp`, `MoreThanUp`) | **All 41 obligations proved** |
| [`tla/Temporal_Proof.tla`](tla/Temporal_Proof.tla) *(15/10)* | MINIMAL_SILENCE §8.17, the per-run lemma in a state machine (any order, deferral, policy; order cannot matter by construction, the policy has no fairness): `LowerBound` — never broken ⇒ once all have acted, ≥ τ refused or pending; `UpperBound`, `PolicySilencesOnlyD` — refuse D (a transversal), accept the rest. TLC `tla/temporal/` (τ = 1): any mechanism and policy {0} no error; mutant (refuse nobody) violates | **All 45 obligations proved** |
| [`tla/ThreeMoves_Proof.tla`](tla/ThreeMoves_Proof.tla) *(7/10)* | any mechanism = remove + ask for compensation + choose outcome, participants free (may decline/crash): correct ⇒ it removes someone in every open invalidating coalition; choice alone and compensation alone never save | **All 36 obligations proved** · non-vacuity: [`tla/counter/tm/TM_Check.tla`](tla/counter/tm/TM_Check.tla) (TLC: assumptions satisfiable, silence-only mechanism correct, compensation-only not) |

Assumptions used: quorums pairwise intersect (`QuorumAssumption`); shares initially partition the units (`ShareAssumption`); the
markers `FREE`, `ABSENT`, `NONE` are distinct from data values. `MinimalSilence_Proof`: membership finite, invalidating coalitions
upward closed. `ThreeMoves_Proof`: participants are free (an asked participant may decline or crash); protocol actions change outcomes
only through the specification.

## TLC — exhaustive model checking, small sizes

*Counterexamples (7/10): [`tla/counter/RESULTS.md`](tla/counter/RESULTS.md) — 3 breaks at the stated boundaries, 2(b) survives the compensation candidate.*

| model | instance | property | verdict |
|---|---|---|---|
| `MC_CalmEscrow` | 3 participants, 3 units, 4 purchases, ≤ 3 share moves | TypeOK, Partition, NoUnitTwice, **NeverBelowZero**, LocalDecision | **No error.** 62,230 distinct states, complete |
| `MC_CalmSeal` (`_live.cfg`) | 3 participants, 3 events, majority quorums; nobody silent, nobody suspected | **AllFinalEventually** (every participant finalises without a vote) | **No error.** 35,321 distinct states, complete |
| `MC_CalmSeal` (`.cfg`) | same, one participant may fall silent, votes allowed | TypeOK, Agreement, Validity, UniqueChoice, FastExcludesAbsent, NotBoth, Inv | **No error.** 303,544,256 distinct states, **complete** (2.19 billion generated, depth 38, 1 h 08 min). The same invariants are proved for all sizes by TLAPS above. |

**Mutants for the escrow (17/10, `tla/esc_mut/`).** A Buy that may take an already-sold unit of its own share (`ResellOwn`) passed TypeOK, Partition, NoUnitTwice, NeverBelowZero and LocalDecision — none of them says a sale is never taken back. `NoRevoke` was added (TLC on `MC_CalmEscrow`: no error, 62,230 states; the mutant violates it) and proved above. A Buy that may take any unit (`AnyUnit`) is caught only by LocalDecision.

**Mutants for the seal (17/10, `tla/seal_mut/`).** Each of TypeOK, Agreement, Validity, UniqueChoice, FastExcludesAbsent, NotBoth and Inv is violated by a deliberate break (one vote suffices for ABSENT; the slow path invents events; the fast path finalises on its own HaveAll alone; an ill-typed vote). Small model: 3 participants, 2 events.

**About the TLC models for CoordinatedVariant and Membership.** TLC models are one-state specifications whose invariant is the conjunction of the theorem's hypotheses on a concrete instance ("1 distinct state found, no error" = the hypotheses hold together); each has a mutant that must fail ("invariant … is equal to FALSE"): `tla/cv/*_mut`, `tla/mb/*_mut`.

## How to read this
- The **safety** of both placements is proved, not sampled.
- The **liveness** claim (no silence ⇒ no vote) is model-checked for three participants only.
- The **conjecture** in PAPER.md §3 is proved **per commitment**, for specifications with property B3: the core in `MinimalSilence_Proof` and
  `ThreeMoves_Proof` above (lever modelled as "which invocations take effect", MINIMAL_SILENCE §6 item 5), and in Complete CALM's own
  terms in `CoordinatedVariant_Proof` (B3 and an implementation that accepts or refuses needed for "only silence" and the exact count); the rest on paper
  in MINIMAL_SILENCE.md. Several commitments at different times: MINIMAL_SILENCE §8.15 and [`checks/layers.py`](checks/layers.py) (exhaustive, ≤ 4
  participants, 0 violations). Still open: necessity of Ω for liveness; lying participants (mechanised).
