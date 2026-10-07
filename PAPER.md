# Where coordination goes: placing it before or after the decision, for the three non-monotone patterns of Complete CALM

**Vasilis Nasopoulos** · draft, October 2026

## Abstract

Complete CALM (Hellerstein, 2026) characterises exactly *when* a specification needs coordination: iff its outcomes are not monotone.
Its conclusion leaves open *how much* coordination a non-monotone specification needs. We give a constructive, measured answer for
the three patterns of non-monotonicity that the same paper identifies in classical problems: **total-order**, **bounded-cardinality**
and **unique-choice** commitment. For each we show where the unavoidable coordination can be *placed in time* — before the decision
or after it — and what it is paid in: refusals, or latency to finality. We conjecture that, once membership is fixed, the only
non-monotone fact any of the three requires is a decision about **silence**: that a participant who stopped talking will add nothing
more to a period. Two small models make the claims precise; both are checked with TLC and their safety invariants are proved with
TLAPS for any number of participants. The measurements come from **Vortex**, the author's own leaderless engine, running on three continents.

## 1. The question

Complete CALM proves: a specification admits a coordination-free implementation iff it is monotone (Hellerstein, arXiv 2602.09435,
Thm. 1). It is exact, and binary. Its conclusion asks the quantitative follow-up — *given a non-monotone specification, how much
coordination does it require?* — and suggests restructuring interactions "to reduce that depth".

Appendix F of the same paper finds that the non-monotonicity of classical problems falls into three patterns. We take these as given
and ask, for each: *at what moment must the coordination happen, and what does each choice cost?*

## 2. The answer, per pattern

| pattern (Complete CALM, App. F) | example | coordination placed | paid in | model |
|---|---|---|---|---|
| **bounded-cardinality** (Lemma 3; renaming row) | a budget: each unit to at most one purchase ("never below zero") | **before** the decision: units are split into per-participant shares ahead of time (escrow; O'Neil 1986, demarcation 1992) | **refusals** when a local share is exhausted while another still has units | `CalmEscrow` |
| **total-order** (Lemma 2) | the order of a log | **after** the decision: once per period, for every decision in the period | **latency to finality**; the number of coordination rounds does not grow with the number of decisions | `CalmSeal` |
| **unique-choice** (Lemma 3, k = 1) | exactly one winner | **after**, in the same round as total-order: once a period is closed, the winner is a pure function of its content | one period of latency | `CalmSeal` |

### 2.1 Before: bounded-cardinality (`CalmEscrow`)
Units are partitioned into shares. A purchase reads and writes only the share of the participant that serves it — no message, no
vote, regardless of the network. Moving units between shares is the only step involving two participants, and it is off the
decision path. **Proved (TLAPS, any sizes):** shares stay a partition; no unit serves two purchases; every taken unit was taken by a
purchase made where the unit lives (*the decision is local*). **Checked (TLC):** approved purchases never exceed the budget.

The price is the gap between the specification and its coordination-free frontier (Complete CALM, §8): a purchase the global budget
would allow is refused because its local share is empty.

### 2.2 After: total-order and unique-choice (`CalmSeal`)
Participants put events in a period and then close it. A period becomes final in one of two ways:
- **without a vote**: a participant that holds every closed content says so; one that hears this from everyone finalises. Both are
  threshold checks over a known membership — monotone (Complete CALM, Remark 3 / Thm. 8);
- **with a vote**, only about a participant somebody has not heard from: a quorum votes it PRESENT or ABSENT.

**Proved (TLAPS, any number of participants, any intersecting quorums):** every participant that finalises holds the same content
(hence the same deterministic order and the same unique winner); a vote-free finalisation never coexists with an ABSENT decision; no
participant is decided both PRESENT and ABSENT. **Checked (TLC):** with nobody silent and nobody suspected, every participant
finalises without a vote.

## 3. Conjecture: coordination is the number of decisions about silence

Under fixed membership, in all three patterns the only step that is not a threshold over known facts is deciding that a silent
participant will contribute nothing more to a period. We conjecture that this is general: **the coordination a specification in
these patterns requires is the number of such decisions it must take, and its placement is *before* for what can be divided and
*after* for what cannot.** Total order cannot be moved entirely before the decision; what must remain after it is, again, a decision
about silence.

For the specifications of §2 this is proved — definition, necessity, nothing else, sufficiency, and the exact count — in
[SILENCE.md](SILENCE.md); for every specification it gives an upper bound, and the minimum remains the conjecture above.

This is close in spirit to Mencius (Mao, Junqueira, Marzullo, OSDI 2008), where a silent server's slots are revoked by agreement; we
state it against the patterns of Complete CALM and measure it.

## 4. Measurements

All measurements were made with **Vortex**, my own leaderless replicated ledger: equal devices, no coordinator.

| what | result |
|---|---|
| total-order, coordination after, one round per period | three 1-vCPU machines on three continents held the **same ledger byte for byte at ~100,000 records/s**, with **one coordination round per second** for all of them; median time to finality 1.76 s |
| bounded-cardinality, coordination before (escrow), network cut 2+2 across three continents | both halves kept selling (~9 in 10 purchases); 0 double spends; 0 balances below zero; refusals 14 % during the cut, 0 % outside it |
| unique-choice under a cut / a device switched off | exactly one holder at any time; 0 diverging decisions |

Raw data and scripts that recompute the bounded-cardinality and normal-operation numbers: https://github.com/vasilisnasopoulos/vortex-festival-demo.
The models here describe *where* coordination sits.

## 5. What this is not
- Not new mechanisms. Escrow (O'Neil 1986; Barbará & Garcia-Molina 1992; bounded counters, Balegas et al. 2015), batched ordering
  (Calvin, 2012), owned positions and revoking a silent owner's slots (Mencius, 2008) are all prior art.
- Not a proof of the conjecture. The models prove safety of two instances; the measurements are examples.
- The vote-free fast path in `CalmSeal` describes the placement the conjecture needs; the measured system uses a more conservative
  variant that votes once per period whether or not anyone is silent. Its coordination is therefore *one round per period*, still
  independent of the number of decisions.

## References
- J. M. Hellerstein, *Complete CALM: A Coordination Criterion for Specifications*, arXiv 2602.09435 (2026).
- J. M. Hellerstein, P. Alvaro, *Keeping CALM: When Distributed Consistency is Easy*, CACM 63(9), 2020.
- P. O'Neil, *The Escrow Transactional Method*, ACM TODS 11(4), 1986.
- D. Barbará, H. Garcia-Molina, *The Demarcation Protocol*, VLDB J. 3, 1994.
- V. Balegas et al., *Extending Eventually Consistent Cloud Databases for Enforcing Numeric Invariants*, SRDS 2015.
- Y. Mao, F. Junqueira, K. Marzullo, *Mencius*, OSDI 2008.
- A. Thomson et al., *Calvin*, SIGMOD 2012.
- P. Bailis et al., *Coordination Avoidance in Database Systems*, VLDB 2014.
