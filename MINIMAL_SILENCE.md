# Silence: the only coordination, and exactly how much of it — for any specification, one commitment at a time

Draft, 7 October 2026 · Vasilis Nasopoulos. Generalises [SILENCE.md](SILENCE.md) (which proves the same for the Seal
specification) to any specification. Framework and terms: Hellerstein, *Complete CALM*, arXiv 2602.09435 — a specification
Spec = (E, Obs, ⪯); an outcome o ∈ Obs(H) is *refinable* at H' ⊒ H if some o' ∈ Obs(H') has o ⪯ o'. Paper proofs; not machine-checked.

## 0. Setting
- Membership N is **fixed and known** (Complete CALM, Remark 3 — the one non-monotone act, taken once, outside this note).
- Every **invocation** in E has an origin participant orig(e) ∈ N. Receipts and protocol messages are not choices of anyone.
- A participant may **close** a scope (a period, a key, an object): a promise in its own history that it will issue no further
  invocation in that scope. Let C(H) be the participants closed at H (for the scope of the outcome at hand). The others are **open**.
- For S ⊆ N, an **S-extension** of H is any H' ⊒ H in which every invocation added in H' \ H has its origin in S.

## 1. Definition — silence

> **A silence commitment about participant i**, made at H for an outcome o, is a restriction of the admissible outcomes
> (a "coordinated variant", Complete CALM §4.1) that makes **some invocation of i that is not yet in H** have **no effect** on o —
> unconditionally or under a condition — **while i has not closed** the scope at H.
>
> In words: deciding, on i's behalf and before i has said so, that something i may still do will not count.

Its content is a negative statement about i's future, "∀ e ∈ X : e ∉ effective(i)", for a set X of invocations i has not issued.
A **closure** is the same statement made by i itself; it is a fact in H and stays one under every extension.

**Invalidating coalitions.** o is **invalidated by S** if some admissible S-extension H' of H leaves o not refinable. S is **minimal**
if no proper subset invalidates o. F(o, H) = the minimal invalidating coalitions; F_open(o, H) = those made only of open participants.
τ(F) = the **hitting number**: the size of a smallest set meeting every member of F (τ(∅) = 0).

**Fact 1 (upward closure).** If S invalidates o, every S' ⊇ S does (the extra members simply do not act). Hence a set R invalidates
o iff R ⊇ S for some S ∈ F(o, H).

## 2. Theorem 1 — silence is necessary

**(a) A silence commitment is non-monotone.** Take a silence commitment about i at H that removes the effect of an invocation e of i
not in H. Since i is open, the event universe admits H' ⊒ H in which i issues e; in the *unrestricted* specification, e's effect must
appear at H', so the commitment's outcome is not refinable there. A non-monotone commitment admits no coordination-free implementation
(Complete CALM, Thm. 1). ∎

**(b) Whenever F_open(o, H) ≠ ∅, committing o needs silence commitments.** Let S ∈ F_open(o, H) and let H' be an admissible
S-extension where o is not refinable. All members of S are open, so nothing prevents H'. For o to stay correct, some invocation added
in H' must have no effect on o — which, decided at H before that invocation exists and before its origin closed, is by definition a
silence commitment about a member of S. ∎

## 3. Theorem 2 — nothing else is needed (and nothing else helps)

**(a) No coalition, no coordination.** If F_open(o, H) = ∅, then every admissible extension is an R-extension for the open set R,
R contains no invalidating coalition (Fact 1), so o is refinable at every admissible extension: committing o is monotone and needs no
coordination at all.

**(b) Every coordination that saves o is a silence commitment.** By (a), coordination is needed exactly when some S ∈ F_open invalidates
o. By the argument of Theorem 1(b), any mechanism that keeps o correct must make some invocation of some member of S ineffective,
decided before it happens and before that member closed — a silence commitment. Ordering, locking, voting, leasing: whatever the
mechanism is called, **what it contributes to o's correctness is one or more silence commitments**; the rest of what it does is
monotone (Complete CALM, Remark 3 and Thm. 8: thresholds over a known membership). ∎

## 4. Theorem 3 — silence suffices, and the exact amount

**Lower bound.** Let D be the participants about whom silence commitments are made for o. By Theorem 1(b), D must meet every
S ∈ F_open(o, H). Hence **|D| ≥ τ(F_open(o, H))**.

**Upper bound.** Let D meet every S ∈ F_open(o, H), and let the commitments about D be agreed by all replicas. After them, only
R = N \ (C ∪ D) can act effectively. If some admissible extension invalidated o it would be an R-extension, so R would contain some
S ∈ F(o, H) (Fact 1), all open — but then S ∩ D = ∅, a contradiction. So o is safe. Agreement on one PRESENT/ABSENT commitment per
member of D is exactly the mechanism proved safe in [`tla/CalmSeal_Proof.tla`](tla/CalmSeal_Proof.tla) (TLAPS, 330/330). Hence **τ(F_open(o, H)) commitments
suffice**.

> **Exact:** the least coordination needed to commit o at H is **τ(F_open(o, H)) silence commitments** — no fewer is possible, no more
> is necessary, and no other kind of coordination contributes.

## 5. Checks against known cases
| specification | F_open | τ | agrees with |
|---|---|---|---|
| monotone (CRDT, set growth) | ∅ | 0 | Complete CALM: coordination-free |
| Seal: a period's content, k participants open | {{i} : i open} | k | [SILENCE.md](SILENCE.md) (k(p)) |
| escrow purchase from the local share | ∅ (no one else can take the unit) | 0 | `tla/CalmEscrow_Proof.tla` (decision is local) |
| escrow: reclaim a silent participant's share | {{i}} | 1 | [SILENCE.md](SILENCE.md) §3 |
| alarm "only if both i and j press", commit "no alarm" | {{i, j}} | **1** | one decision (silence of i *or* j), not two |

## 6. What is NOT shown
1. **Per commitment.** One silence commitment can serve many outcomes (a whole period); the least total over a run is a covering
   problem over time — open.
2. **Liveness.** That commitments get taken needs a partial-synchrony / failure-detector assumption (FLP). Safety only.
3. **Suspected ≠ silent.** In practice the commitment is about a participant not yet heard from; it may be merely slow.
4. **Outside the setting:** changing membership, lying participants, real-time deadlines.
5. **Not machine-checked.** Theorems 1–3 are paper proofs over the definitions in §0–1; §2(b)/§3(b) rest on the definition of a silence
   commitment as *any* restriction that makes a not-yet-issued invocation of an open participant ineffective. A reviewer will test that
   definition first.
6. **Prior art** — searched 7/10/2026; below. Nothing found that states the least coordination of a commitment as a hitting number of
   silences in the CALM / monotonicity framework. Absence of a hit is not proof of absence.

## 7. Prior art (searched 7/10/2026) — what is close, and how this differs

| work | what it shows | how this note differs |
|---|---|---|
| ⚠️ **Goren & Moses, "Silence"**, PODC 2018 / JACM 2020; **Nataf, Goren & Moses, "Null Messages, Information and Coordination"**, arXiv 2208.10866 | in **synchronous** systems, *not sending* carries information (null messages); "silent choir" = f+1 agents whose silence can be relied on; message patterns **necessary and sufficient** for information transfer and for the *Ordered Response* coordination task | **the closest work, and the same word.** They use silence *as a channel* under time bounds; here the system is **asynchronous** and silence is not observed but **decided** — a non-monotone commitment in Complete CALM's sense — and the result is a count (hitting number) per commitment. Must be cited prominently; the term "silence commitment" must be defined against theirs |
| **Chandra, Hadzilacos & Toueg**, J.ACM 1996 — the weakest failure detector for consensus is Ω | exactly **what information about failures** (≈ about silence) is necessary and sufficient to solve **consensus** | same *shape* (necessary and sufficient knowledge about who is silent) for one problem; this note gives a **count** for any specification's commitment, in the monotonicity framework, not the weakest detector |
| **Chandy & Misra**, null messages in conservative distributed simulation (1979); **Tucker, Maier et al.**, punctuations (TKDE 2003) | a participant's **promise** that it will send nothing more below a bound lets blocking operators proceed | this is the **closure** of §0 — prior art for closure; not claimed |
| **Ameloot, Ketsman, Neven, Zinn** (TODS 2015), policy-aware transducers | knowing *who may still contribute* turns some non-monotone queries coordination-free | the open set C(H) plays that role; their results are qualitative (free or not), not a count |
| **Mencius** (OSDI 2008) | a silent owner's slots are revoked by agreement | one instance of a silence commitment (Seal) |
| **Ju, "When Coordination Is Avoidable"**, arXiv 2602.18673 (2026) | classifies organisational tasks as monotone or not; "coordination tax" = share of spending that is avoidable | qualitative per task; no minimum count |
| Quorum-system literature | quorums must intersect | used, not claimed |

**Verdict.** The result appears new as stated (least coordination per commitment = hitting number of silence commitments, in the
Complete CALM framework, asynchronous). It is **not** new that silence/absence carries the essential information (Goren & Moses;
Chandra, Hadzilacos & Toueg) or that closure lets blocking computation proceed (Chandy & Misra; Tucker et al.). A publication must say
both.
