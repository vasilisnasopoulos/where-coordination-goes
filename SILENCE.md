# Silence: definition, necessity, nothing else, sufficiency

Draft, October 2026 · Vasilis Nasopoulos. Companion to [PAPER.md](PAPER.md) §3. Framework and terms: Hellerstein, *Complete CALM*
(arXiv 2602.09435): a specification is (E, Obs, ⪯); it admits a coordination-free implementation iff it is **monotone** — every admissible
outcome at a history H has a refinement at every causal extension H' ⊒ H.

## 0. Setting (the class of specifications this note is about)

- A **fixed, known membership** N = {1..n} (Complete CALM, Remark 3: the one non-monotone act, done once).
- Time is cut into **periods** p = 1, 2, … Participant i puts a finite set of events C_i(p) in period p, then may **close** it by
  sending close(i, p, C_i(p)). After closing, i adds nothing more to p.
- The specification **Seal**: the observable outcome at H is the sequence of *final* periods, each given as the tuple
  (C_1(p), …, C_n(p)) where an entry may be the marker ⊥ ("contributes nothing"). Refinement ⪯ is prefix extension: final periods are
  only appended, never changed.
- Order inside a period is a fixed deterministic function of the tuple (any total order on events); the unique winner of a period is
  its first event under that order. So total-order and unique-choice both reduce to: *the tuple of a period is final*.
- Asynchronous messages; a participant may stop forever (crash or cut) — it is then **silent**.

## 1. Definition — what "silence" is

For an observer o, a history H and a pair (i, p):

> **A silence commitment** is an outcome at H that fixes the entry of i in period p **without** close(i, p, ·) being in o's causal past
> at H. Equivalently, it asserts the negative, universally quantified fact
>
>   S(i, p, X):   ∀ e ∉ X :  e ∉ C_i(p)        ("i will add nothing outside X to p"),
>
> about events i has **not** declared, before i has declared it.

By contrast, a **closure fact** close(i, p, X) is a received message: once in the causal past it stays there under every extension.

## 2. Theorem 1 — silence is non-monotone, hence needs coordination

**Claim.** Any outcome containing a silence commitment for (i, p) is not monotone; by Complete CALM it cannot be produced
coordination-free.

**Proof.** Let o's outcome at H fix i's entry in p to X (possibly ⊥) while close(i, p, ·) ∉ past(H). Because i has not closed p, the
event universe admits an extension H' ⊒ H in which i emits some e ∉ X into p and then closes with C_i(p) ∋ e (i is not constrained by
anything it has not sent). Every admissible outcome at H' must report C_i(p) ∋ e, so no outcome at H' extends o's outcome at H
(the entry is fixed to X ∌ e). The outcome has no refinement at H' — the specification restricted to such outcomes is not monotone. ∎

**Corollary (it cannot be avoided).** If the specification must make period p final while some i may stay silent forever (a crash),
some outcome must fix i's entry without close(i, p): a silence commitment. So any implementation that stays live under one silent
participant needs coordination at least once per (i, p) it finalises without i's closure. *(Lower bound on the amount.)*

## 3. Theorem 2 — nothing else is non-monotone

**Claim.** In Seal, every outcome whose periods' entries all come from closure facts is monotone. Hence the **only** non-monotone
commitments are silence commitments.

**Proof.** Take an outcome at H in which, for every final period p and every i, the entry equals X where close(i, p, X) ∈ past(H).
Let H' ⊒ H. Closure messages, once received, remain in the causal past (histories only grow), and i, having closed p, adds nothing to
p in H' (by the definition of close). So in H' the same entries are still exactly the closed contents, the same deterministic order
and winner follow, and the same final periods are a prefix of the final periods at H'. The outcome refines to itself plus whatever is
appended. The rule that fires finality — "close received from all i ∈ N" — is a threshold over a known set: accumulating, monotone
(Complete CALM, Lemma 1 and Theorem 8). ∎

**The same holds for the bounded-cardinality pattern (escrow).** With units pre-partitioned into shares, a purchase served from its own
share is never invalidated by any extension (no other participant can take a unit outside its share — proved in `CalmEscrow_Proof.tla`,
`NoUnitTwice` and `LocalDecision`, all sizes). A refusal is also a final outcome that no extension contradicts. The only step that
involves another participant is a share transfer; a transfer **from a participant that agrees** is its own declaration (a closure-like
fact). The only transfer that needs a decision *about* someone is **reclaiming the share of a silent participant** — a silence
commitment about its future purchases. So escrow, too, needs coordination only for silence.

## 4. Theorem 3 — silence decisions suffice (safety)

**Claim.** Fixed membership + intersecting quorums deciding, for each (i, p) not closed, PRESENT (with contents) or ABSENT, is enough to
implement Seal safely: every observer that finalises p holds the same tuple, hence the same order and the same winner; a vote-free
finalisation never coexists with an ABSENT decision; no (i, p) is decided both ways.

**Proof.** Machine-checked: `CalmSeal_Proof.tla`, theorem `Main`, **TLAPS, all 330 obligations proved**, for any number of
participants and any pairwise-intersecting quorum system. ∎

## 5. The amount — upper and lower bound meet

Let k(p) be the number of participants whose entry in period p is finalised without their closure.
- **Lower bound** (Theorem 1, corollary): at least k(p) silence commitments, each non-monotone.
- **Upper bound** (Theorem 3, the CalmSeal construction): one quorum decision per such (i, p), and **zero** when everyone closes
  (TLC: with nobody silent and nobody suspected, every participant finalises without a vote — complete for 3 participants).

So, for Seal under fixed membership, **the coordination required in period p is exactly k(p) decisions about silence** — no more is
needed, no less is possible.

## 6. For every specification: an upper bound, and the open question

By Complete CALM, Theorem 8, **any** specification becomes monotone on top of an ordering layer with fixed membership. Seal is such a
layer, and its only coordination is silence decisions (Theorem 3). Hence:

> **Every specification can be implemented so that, once membership is fixed, its only coordination is decisions about silence.**

This is an **upper bound**, not the minimum: a specification that does not depend on participant i's events needs no decision about
i's silence. The minimum is the open question:

> **Conjecture.** The least coordination a specification requires equals the number of silence decisions about participants whose
> undeclared events could still change its outcome (directly, or by causally enabling others' events).

The lower half follows the argument of Theorem 1. **Update:** [MINIMAL_SILENCE.md](MINIMAL_SILENCE.md) corrects the wording — the
least amount is not the *number* of such participants but the **hitting number** of the coalitions that could change the outcome — and
proves it, per commitment, for any specification (paper proofs).

## 7. What this does NOT prove — said plainly

1. **Liveness under silence.** Theorem 3 is safety. That a silent participant's entry *will* eventually be decided needs a
   partial-synchrony / failure-detector assumption (FLP); not proved here.
2. **Suspected ≠ silent.** In an asynchronous system one cannot tell a silent participant from a slow one. An implementation decides
   about participants it has **not heard from**; it may decide about a slow one (it then pays one decision it did not strictly need, and
   the slow participant's late events fall out of p). The bounds count decisions actually taken.
3. **The class.** All of this is for Seal-shaped specifications (periods, known membership, deterministic order inside a period) and
   escrow. It is **not** a theorem about every specification. Whether every non-monotone specification reduces to silence after
   membership is fixed is the open conjecture of PAPER.md §3.
4. **Lying participants and real time.** The model assumes a participant's closure is truthful (crash/omission, not Byzantine), and
   no deadline measured on a clock. Neither is covered.
5. **Changing membership.** Everything assumes the set of participants is fixed; choosing it is itself non-monotone (Complete CALM,
   Remark 3) and is not a silence decision.
6. **Prior art.** Deciding the absence of a silent owner by agreement is the move of Mencius (2008); closure-based finality is the
   idea behind punctuations in stream processing. What is offered here is the statement against Complete CALM's patterns, the exact
   count, and the machine-checked sufficiency.
