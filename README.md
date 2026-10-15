# Where coordination goes

**Where CALM says coordination is needed, a commitment needs exactly τ silences in the worst case — and we say which — for systems
that accept or refuse, per commitment (under Hellerstein's global definition, τ is a lower bound).**

Companion material for **[PAPER.md](PAPER.md)** — *placing coordination before or after the decision, for the three non-monotone
patterns of Complete CALM*.

Complete CALM (Hellerstein, arXiv 2602.09435) says exactly **when** a specification needs coordination. This repository addresses the
question its conclusion leaves open — **how much, and when** — for the three patterns its Appendix F identifies (total-order,
bounded-cardinality, unique-choice), with two small TLA+ models, machine-checked proofs, and measurements made with **Vortex**, the
author's own leaderless engine.

**The Silence Theorem** — *coordination in Complete CALM is a transversal of silences.* One commitment at a time, for implementations that accept or refuse
and specifications where whether the commitment breaks depends only on, and grows with, the set of participants whose invocations took effect (B3, §8.12): the only coordination is deciding that some open participant's future action will not count (a *silence*), and the least amount
is τ, the size of the smallest set that meets every group able to break the commitment (Berge's transversal number), in the worst case. Stated and
proved in [MINIMAL_SILENCE.md](MINIMAL_SILENCE.md); derived from Complete CALM's own definitions in §8.12.

**Read as CAP.** CALM (Hellerstein 2010; proved by Ameloot, Neven & Van den Bussche, PODS 2011 / J.ACM 2013; Hellerstein & Alvaro,
*Keeping CALM*, CACM 2020, whose Observation 1 reads coordination-freeness as availability under partition) and Complete CALM say
*whether* a specification needs coordination; Complete CAP (§5) says that then a partition costs availability. Refusing an invocation is that loss of availability (Brewer 2012: "limit some operations, thereby reducing availability");
delaying a commitment is the latency side (PACELC; Golab 2018; r + w ≥ d, Lipton–Sandberg, Attiya–Welch). What this note adds is the
count: for implementations that accept or refuse, the least number of participants that must be refused to keep one commitment
consistent is exactly τ, and which ones. Other quantifications of CAP measure time (CAL, Lee et al. 2021) or compute availability per
workload (Yu & Vahdat 2001). Prior art: MINIMAL_SILENCE §7.

## Notes
- [SILENCE.md](SILENCE.md) — silence defined; necessary, nothing else, sufficient, exact count, for the specifications of the paper.
- [MINIMAL_SILENCE.md](MINIMAL_SILENCE.md) — one commitment at a time, for specifications where breaking is monotone in who took effect (**B3**, §8.12): the least coordination is the
  **hitting number** (Berge's transversal number) of silence commitments; for implementations that accept or refuse, only silence is coordination (a response carrying a value the
  implementation picks — renaming — is another lever, §8.12) — grounded in Complete CALM's
  own Defs. 5 and 11 (§8.12); known mechanisms move by move (§8.13); hardness, rounds, liveness, membership, counterexamples; limits
  (§8.14). Prior art and how this differs (§7): Goren & Moses; Chandra, Hadzilacos & Toueg; Taylor 1990; coteries and quorum systems.
  **Not ours (§7a, §8.11):** minimising coordination as a cover of a conflict graph (Houshmand & Lesani, Hamsaz, POPL 2019); the mathematics (Berge; Karp; Johnson/Lovász/Chvátal; Fredman & Khachiyan) and its set-theoretic core,
  which is the classical blocker duality also used for coteries (Edmonds & Fulkerson; Ibaraki & Kameda). What is claimed is the
  modelling: deriving that hypergraph from a CALM specification, and that, for implementations that accept or refuse, silence is the
  only coordination that contributes.

## Models

| model | pattern | coordination | checked |
|---|---|---|---|
| [`tla/CalmEscrow.tla`](tla/CalmEscrow.tla) | bounded-cardinality (a budget, each unit to at most one purchase) | **before** the decision (per-participant shares) | TLC: exhaustive · TLAPS: inductive invariant, any sizes |
| [`tla/CalmSeal.tla`](tla/CalmSeal.tla) | total-order and unique-choice | **after** the decision, a vote only about a participant nobody has heard from | TLC: exhaustive · TLAPS: inductive invariant, any number of participants |

### What is proved (TLAPS, for any sizes)
- **Escrow** (`CalmEscrow_Proof.tla`): shares stay a partition; no unit serves two purchases; a unit is taken only by a purchase made
  at the participant that owns it — *the decision is local*.
- **Seal** (`CalmSeal_Proof.tla`): every participant that finalises a period holds the same content (*Agreement*), hence the same
  order and the same unique winner (*UniqueChoice*); a vote-free finalisation never coexists with an ABSENT decision; nobody is
  decided both PRESENT and ABSENT.
- **One commitment, any family of breaking coalitions** (`MinimalSilence_Proof.tla`, 112/112; lever: which invocations take effect): safe ⇔ the silence commitments hit every open
  coalition that could invalidate the outcome ⇔ they hit every minimal one — the least number is the hitting number; a mechanism
  that keeps the outcome correct silences someone in each such coalition; computing the least amount is NP-hard (our vertex-cover reduction; the hardness is Karp's, 1972).
- **Three moves** (`ThreeMoves_Proof.tla`, 36/36): a mechanism may remove invocations, ask participants for compensation, and choose
  the reported outcome; with free participants (may decline or crash), only removal saves. Assumptions shown satisfiable by TLC.
- **Changing membership** (`Membership_Proof.tla`, 161/161, in the model of §0): a newcomer that counts only in later scopes leaves
  every earlier commitment's τ unchanged; a participant leaving changes τ by at most one.
- **In Complete CALM's own terms** (`CoordinatedVariant_Proof.tla`, 183/183): any properly coordinated variant (Def. 11) must forbid
  every future that breaks the committed outcome (*Lemma A*); since invocations belong to the environment (Def. 5), an implementation that
  accepts or refuses does so only by choosing whose invocations do not count (*OnlySilence*; a response carrying a value the
  implementation picks — renaming — is another lever); if mere attempts break the outcome, no
  variant exists. For specifications where whether the commitment breaks depends only on, and grows with, the set of participants whose invocations took effect (property **B3**), what it
  silences meets every invalidating coalition, and in the run where every open participant acts it silences at least τ (*Lemma B,
  Chain*), even if it chooses whom to silence late. Conversely, silencing a minimum transversal is a properly coordinated variant at the
  commitment that silences exactly τ (*Sufficiency*): **the least coordination of a commitment is exactly τ silences** — both bounds
  against the same **per-commitment** form of Def. 11 (*ChainAt, ExactlyAt*), which is our weakening of his definition. Under his global
  Def. 11 τ is a lower bound (*GlobalImpliesAt*) and the minimum can be larger, because the variant must also repair the specification's
  other non-monotone points (§8.17). The same per-run lemma restated in a state machine: *LowerBound, UpperBound*
  ([`tla/Temporal_Proof.tla`](tla/Temporal_Proof.tla), 45/45) — order cannot matter there by construction (§8.17). B3 is checked exhaustively on 3–4 participants ([`checks/b3.py`](checks/b3.py)) and proved, in the worst case (the environment chooses
  harmful events), for Seal, order-given abstractions of unique choice and total order, and unit budgets, for any number of participants
  ([`tla/B3Patterns_Proof.tla`](tla/B3Patterns_Proof.tla), 41/41; §8.16 for what this does not cover).
  TLC models in `tla/cv/`.

### Counterexamples (TLC) — [`tla/counter/RESULTS.md`](tla/counter/RESULTS.md)
A lying closure, a newcomer in an already-committed scope, and "commit and hope" break the result — exactly at the stated boundaries.
Compensation by a participant that may crash is not a safe mechanism; compensation built into the specification needs no coordination.

### What is only model-checked (TLC, small sizes)
- Escrow: approved purchases never exceed the budget (a cardinality bound).
- Seal: with nobody silent and nobody suspected, every participant finalises **without a vote** (liveness).

### What is not claimed
- The conjecture of the paper (§3) is proved **per commitment** (MINIMAL_SILENCE; core machine-checked). Several commitments taken at
  different times: bounds in MINIMAL_SILENCE §8.15 (the online case is online hitting set, Alon et al. — theirs). Not proved: that the leader oracle Ω is *necessary* for liveness; a mechanised
  version with lying participants. From Complete CALM's Defs. 5 and 11, for every specification: a coordinated variant never lets
  the run break the commitment. That this means silencing someone, and the exact count τ (worst case), need property B3 (above) and an implementation
  that accepts or refuses: with value-carrying responses (renaming) coordination without silence exists.
- Outside the claim: real time (leases, timeouts), probabilistic safety, how a member joins or leaves (the count is in §8.7, in the model
  of §0), lying participants (paper only), liveness.
- The mathematics is prior art (see Notes above).
- The mechanisms are prior art (escrow 1986, demarcation 1992, Calvin 2012, Mencius 2008). See PAPER.md §5.

## Re-running

```bash
# TLC (Java 11+)
java -cp tla2tools.jar tlc2.TLC -deadlock -config tla/MC_CalmEscrow.cfg tla/MC_CalmEscrow.tla
java -cp tla2tools.jar tlc2.TLC -deadlock -config tla/MC_CalmSeal.cfg tla/MC_CalmSeal.tla
java -cp tla2tools.jar tlc2.TLC -config tla/MC_CalmSeal_live.cfg tla/MC_CalmSeal.tla

# TLAPS 1.5 (note: tlapm exits 0 even when obligations fail — read the last line)
tlapm --toolbox 0 0 tla/CalmEscrow_Proof.tla
tlapm --toolbox 0 0 tla/CalmSeal_Proof.tla
tlapm --toolbox 0 0 tla/MinimalSilence_Proof.tla
tlapm --toolbox 0 0 tla/ThreeMoves_Proof.tla
tlapm --toolbox 0 0 tla/CoordinatedVariant_Proof.tla
tlapm --toolbox 0 0 tla/Membership_Proof.tla
tlapm --toolbox 0 0 tla/B3Patterns_Proof.tla
tlapm --toolbox 0 0 tla/Temporal_Proof.tla

# counterexamples: see the table in tla/counter/RESULTS.md (each .cfg sets the variant)
java -cp tla2tools.jar tlc2.TLC -config tla/counter/CE1_Liar_TRUE.cfg tla/counter/CE1_Liar.tla
# non-vacuity of ThreeMoves (needs TLAPS.tla on the library path)
cd tla/counter/tm && java -DTLA-Library=<repo>/tla:<tlapm>/lib/tlapm/stdlib -cp tla2tools.jar tlc2.TLC -config TM_Check.cfg TM_Check.tla
# non-vacuity of CoordinatedVariant_Proof (tau = 1, first-come-wins)
cd tla/cv && java -DTLA-Library=<repo>/tla:<tlapm>/lib/tlapm/stdlib -cp tla2tools.jar tlc2.TLC -config MC_CV.cfg MC_CV.tla
cd tla/cv && java -DTLA-Library=<repo>/tla:<tlapm>/lib/tlapm/stdlib -cp tla2tools.jar tlc2.TLC -config MC_Suff.cfg MC_Suff.tla
# membership; each MC_* has a *_mut twin that must fail
cd tla/mb && java -DTLA-Library=<repo>/tla:<tlapm>/lib/tlapm/stdlib -cp tla2tools.jar tlc2.TLC -config MC_Membership.cfg MC_Membership.tla
```

## Results of the runs in this repository
See [`RESULTS.md`](RESULTS.md).

## Licence
CC BY 4.0. © Vasilis Nasopoulos.
