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
1. **Per commitment.** One silence commitment can serve many outcomes (a whole period). Same-time commitments of one scope: §8.2
   (union). Commitments taken at different times inside one scope — open.
2. **Liveness.** That commitments get taken needs a partial-synchrony / failure-detector assumption (FLP). §8.5: Ω suffices; whether it
   is necessary — open.
3. **Suspected ≠ silent.** In practice the commitment is about a participant not yet heard from; it may be merely slow (§8.6).
4. **Outside the setting:** changing membership (§8.7), lying participants (§8.8, paper only), real-time deadlines; counterexamples
   at these boundaries in §8.10.
5. **Partly machine-checked.** [`tla/MinimalSilence_Proof.tla`](tla/MinimalSilence_Proof.tla) (TLAPS, 112/112, 7/10) proves the set-theoretic core, see §8: safe ⇔ D hits every
   open invalidating coalition ⇔ D hits every minimal one — so the least |D| is the hitting number; and Theorem 2(b) for any
   mechanism made of the three moves of §8.9b ([`tla/ThreeMoves_Proof.tla`](tla/ThreeMoves_Proof.tla), 36/36). What stays a modelling
   step: that every mechanism is captured by those moves, with free participants. A reviewer will test that first.
6. **Prior art** — searched 7/10/2026; below. Nothing found that states the least coordination of a commitment as a hitting number of
   silences in the CALM / monotonicity framework. Absence of a hit is not proof of absence.

## 7. Prior art (searched 7/10/2026) — what is close, and how this differs

| work | what it shows | how this note differs |
|---|---|---|
| ⚠️ **Goren & Moses, "Silence"**, PODC 2018 / JACM 2020; **Nataf, Goren & Moses, "Null Messages, Information and Coordination"**, arXiv 2208.10866 | in **synchronous** systems, *not sending* carries information (null messages); "silent choir" = f+1 agents whose silence can be relied on; message patterns **necessary and sufficient** for information transfer and for the *Ordered Response* coordination task | **the closest work, and the same word.** They use silence *as a channel* under time bounds; here the system is **asynchronous** and silence is not observed but **decided** — a non-monotone commitment in Complete CALM's sense — and the result is a count (hitting number) per commitment. cited prominently here, and "silence commitment" is defined against their notion |
| **Chandra, Hadzilacos & Toueg**, J.ACM 1996 — the weakest failure detector for consensus is Ω | exactly **what information about failures** (≈ about silence) is necessary and sufficient to solve **consensus** | same *shape* (necessary and sufficient knowledge about who is silent) for one problem; this note gives a **count** for any specification's commitment, in the monotonicity framework, not the weakest detector |
| **Chandy & Misra**, null messages in conservative distributed simulation (1979); **Tucker, Maier et al.**, punctuations (TKDE 2003) | a participant's **promise** that it will send nothing more below a bound lets blocking operators proceed | this is the **closure** of §0 — prior art for closure; not claimed |
| **Ameloot, Ketsman, Neven, Zinn**, TODS 40(4), 2016 (PODS 2014); policy-aware transducers (Zinn, Green, Ludäscher, ICDT 2012) | knowing *who may still contribute* turns some non-monotone queries coordination-free | the open set C(H) plays that role; their results are qualitative (free or not), not a count |
| **Mencius** (OSDI 2008) | a silent owner's slots are revoked by agreement | one instance of a silence commitment (Seal) |
| **Ju, "When Coordination Is Avoidable"**, arXiv 2602.18673 (2026) | classifies organisational tasks as monotone or not; "coordination tax" = share of spending that is avoidable | qualitative per task; no minimum count |
| Quorum-system literature | quorums must intersect | used, not claimed |
| **Pease, Shostak & Lamport** 1980, *interactive consistency* (agree on a vector, missing entries = null); Klianev, arXiv 2601.16460 (2026) | agreement on the vector of who contributed what | §8.4's "all τ commitments in one agreement instance" is this; not claimed. (Klianev's claim to escape FLP is not relied on) |
| **Taylor**, *Knowledge and Inhibition in Asynchronous Distributed Systems*, Cornell TR 90-1139, 1990 | inhibiting (delaying) actions is closely related to achieving concurrent common knowledge | closest in spirit to "coordination = making actions not count"; qualitative, no count, no mechanism trichotomy |
| **Bailis et al.**, invariant confluence (PVLDB 8(3), 2014) | necessary and sufficient condition for coordination-free execution of invariants | yes/no criterion, like CALM; no amount |
| **Garcia-Molina & Salem**, Sagas (1987); **Helland & Campbell**, "Building on Quicksand" / apologies (CIDR 2009) | compensating actions instead of prevention | move (3) of §8.9b; claimed only: it is either unsafe (relies on a free participant) or a change of specification |

**Second search (7/10, evening):** CALM/coordination+compensation, minimal coordination as hitting set, failure-detector minimality,
knowledge/inhibition, I-confluence. No work found stating (a) coordination of a commitment = silence commitments only, with (b) the
exact count as a hitting number and (c) the three-move exhaustiveness. Closest: Taylor 1990 (inhibition), Goren & Moses (silence,
synchronous), CHT 1996 (information about failures). Absence of a hit is not proof of absence.

**Verdict.** The result appears new as stated (least coordination per commitment = hitting number of silence commitments, in the
Complete CALM framework, asynchronous). It is **not** new that silence/absence carries the essential information (Goren & Moses;
Chandra, Hadzilacos & Toueg) or that closure lets blocking computation proceed (Chandy & Misra; Tucker et al.). A publication must say
both.

## 8. Beyond the count — what else follows (7 October 2026)

Machine-checked parts are in [`tla/MinimalSilence_Proof.tla`](tla/MinimalSilence_Proof.tla) (TLAPS, **112/112**); the rest are paper proofs, marked.

**8.1 Every mechanism silences someone (Theorem 2(b), checked).** Model a mechanism as *any* rule Eff that, in the extension where
coalition S acts, lets only Eff[S] ⊆ S take effect. If it keeps o correct in every extension, then for every S ∈ F_open, S \ Eff[S] ≠ ∅
(`SilenceNecessary`). A commitment taken at H, before anyone acts, is the case Eff[S] = S \ D for one D (`FixedMechanism`), and then
`Exact` gives |D| ≥ τ. *What is still a modelling step:* that "takes effect" is the right abstraction of every mechanism's contribution.

**8.2 Over a run (checked for the union step).** A commitment about i in a scope serves every outcome of that scope. Hitting the families
of several outcomes = hitting their union (`RunUnion`), so the least total per scope is **τ(⋃ₒ F_open(o))**, and over a run the sum over
scopes. Open: when commitments in one scope may be taken at different times (H differs per outcome), the families change in between.

**8.3 Hardness (reduction checked).** For any graph G, the alarm specification "alarm iff both ends of some edge press; commit *no alarm*"
has Inv = the upward closure of the edges, and hitting it is exactly a vertex cover (`VertexCover`). Hence: *computing the least
coordination of a commitment is NP-hard* (decision version NP-complete when F_open is given explicitly; greedy gives a ln n
approximation; polynomial when all minimal coalitions are singletons — the Seal case, τ = number open). *Paper:* deciding τ = 0 is
deciding whether the commitment is monotone, undecidable in general (Complete CALM §3.6); so τ is **uncomputable** in general.

**8.4 Rounds (paper).** τ counts decisions, not rounds. All τ commitments of one scope fit in **one** agreement instance (a vector
PRESENT/ABSENT per member of D). So: τ = 0 ⇒ no round; τ ≥ 1 ⇒ the cost of one agreement instance, **independent of τ**. Messages scale
with τ only through the vector size.

**8.5 Liveness (paper, sufficiency only).** Each commitment is an agreement on PRESENT/ABSENT; with a majority correct and the leader
oracle Ω, Paxos-style agreement terminates (CalmSeal's vote is such an agreement). And with nobody silent no vote is needed at all —
model-checked for 3 participants (`tla/MC_CalmSeal_live.cfg`, [RESULTS](RESULTS.md)). *Open:* that Ω is also **necessary** (a reduction from consensus to one silence
commitment); conjectured, not proved.

**8.6 Suspected ≠ silent (paper).** Safety never depends on the suspicion being right (8.1 uses no detector). A wrong suspicion costs
(i) one commitment that was not needed and (ii) the late invocations of that participant falling out of that scope. With an eventually
perfect detector (◇P) false suspicions are finite per participant, so the excess over τ is finite per run.

**8.7 Changing membership (paper).** Removing i = one commitment that i is silent in every later scope (one agreement, Complete CALM
Remark 3). Adding j is safe if j's invocations count only in scopes opened after its admission — j is *closed by construction* for the
earlier ones, so F_open of every earlier outcome is unchanged. Theorems 1–3 then hold per membership epoch; each change costs one
agreement.

**8.8 A lying closure (paper, partial).** If a participant closes and then issues an invocation, replicas that treat the closure as a fact
must reject the later invocation — detectable equivocation.
With f Byzantine *replicas*, agreement on the commitments needs n ≥ 3f+1; the count τ is unchanged, computed with Inv over coalitions that
may include Byzantine participants. *Open:* a mechanised statement.

**8.9 Against Goren & Moses (paper).** In their synchronous model silence is **observed**: after a round with no message, a process
knows; a "silent choir" of f+1 is needed to learn through silence under f crashes. Here (asynchronous) silence cannot be observed, only
**decided** — that is exactly why it is coordination. Adding a clock turns a decided silence into an observed one; that is the
synchronous special case, not a competing result.

**8.9b Three moves, only one is coordination (checked, [`tla/ThreeMoves_Proof.tla`](tla/ThreeMoves_Proof.tla), TLAPS 36/36).** Whatever a mechanism is called, in
the extension where S acts it can only (1) choose which admissible outcome to report, (2) remove invocations (silence), (3) ask
participants for compensating invocations. With participants free — a mechanism cannot force an invocation, an asked participant may
decline or crash — a correct mechanism removes someone in every open invalidating coalition (`OnlyRemovalSaves`); (1) alone and (3)
alone never save (`ChoiceAlone`, `CompensationAlone`). Assumptions shown satisfiable by TLC ([`tla/counter/tm/TM_Check.tla`](tla/counter/tm/TM_Check.tla)).
*The weight is on two modelling assumptions, not on the proof:* participants are free, and protocol actions change outcomes only
through the specification. Drop the first (a participant that is *guaranteed* to compensate) and silence is no longer necessary — that
participant is then not a free participant but part of the specification. This *speaks to* — does not settle — CALM 2019 ("Keeping CALM", the
paragraph on compensation): Hellerstein asks whether coordination and compensation could be "up-leveled" into one concept of eventual
non-deterministic agreement. The result here points the other way: compensation that *changes the specification* (the apology is an
acceptable outcome) is not coordination at all; compensation that *relies on a participant* is unsafe. Whether his unified concept
exists at the level of specifications is a different question, not answered here.

**8.10 Counterexamples (TLC, [`tla/counter/RESULTS.md`](tla/counter/RESULTS.md)).** A lying closure, a newcomer in a committed scope, and "commit and hope" each
break the result — exactly the boundaries of §0. A mechanism that forces another participant to compensate instead of silencing breaks
safety when that participant crashes; made deterministic, it removes the coalition and τ = 0. Theorem 2(b) survives both.

**Still open after §8:** necessity of Ω (8.5) · different commitment times inside a scope (8.2) · mechanised Byzantine version (8.8) ·
mechanising 8.1's abstraction against a concrete language (e.g. Hydro).
