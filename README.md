# Where coordination goes

Companion material for **[PAPER.md](PAPER.md)** — *placing coordination before or after the decision, for the three non-monotone
patterns of Complete CALM*.

Complete CALM (Hellerstein, arXiv 2602.09435) says exactly **when** a specification needs coordination. This repository addresses the
question its conclusion leaves open — **how much, and when** — for the three patterns its Appendix F identifies (total-order,
bounded-cardinality, unique-choice), with two small TLA+ models, machine-checked proofs, and measurements made with **Vortex**, the
author's own leaderless engine.

## Notes
- [SILENCE.md](SILENCE.md) — silence defined; necessary, nothing else, sufficient, exact count, for the specifications of the paper.
- [MINIMAL_SILENCE.md](MINIMAL_SILENCE.md) — for **any** specification, one commitment at a time: the least coordination is the
  **hitting number** of silence commitments; prior art (Goren & Moses, "Silence"; Chandra, Hadzilacos & Toueg) and how this differs.

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

### What is only model-checked (TLC, small sizes)
- Escrow: approved purchases never exceed the budget (a cardinality bound).
- Seal: with nobody silent and nobody suspected, every participant finalises **without a vote** (liveness).

### What is not claimed
- The conjecture of the paper (§3) is not proved. The models are instances.
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
```

## Results of the runs in this repository
See [`RESULTS.md`](RESULTS.md).

## Licence
CC BY 4.0. © Vasilis Nasopoulos.
