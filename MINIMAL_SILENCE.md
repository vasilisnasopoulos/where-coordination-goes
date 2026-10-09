# The Silence Theorem — coordination in Complete CALM is a transversal of silences

*Silence is the only coordination, and τ (a transversal number) is exactly how much of it — for any specification, one commitment
at a time.*

Draft, 7 October 2026 · Vasilis Nasopoulos. Generalises [SILENCE.md](SILENCE.md) (which proves the same for the Seal
specification) to any specification. Framework and terms: Hellerstein, *Complete CALM*, arXiv 2602.09435 — a specification
Spec = (E, Obs, ⪯); an outcome o ∈ Obs(H) is *refinable* at H' ⊒ H if some o' ∈ Obs(H') has o ⪯ o'. Paper proofs; the parts marked *checked* are machine-checked (TLAPS).

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
τ(F) = the **hitting number**: the size of a smallest set meeting every member of F (τ(∅) = 0). This is the classical
**transversal number** of the hypergraph F (Berge, *Graphes et hypergraphes*, 1970); τ and the term are his, not ours (§7a).

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
   **Update 9/10:** §8.12 derives this from Complete CALM's Defs. 5 and 11 (Lemmas A–C and the chain: TLAPS 52/52; B under assumptions B1–B3); §8.13 maps known mechanisms;
   §8.14 states what is outside. The remaining gap is assumption B3, stated explicitly.
6. **Prior art** — searched 7/10 and 9/10/2026; §7–§7a and §8.11. The mathematics (transversals, their hardness, their duality) and the
   use of transversals in distributed systems (coteries, quorums) are prior art. What may be new is only the statement in the §7
   verdict. Absence of a hit is not proof of absence.

## 7. Prior art (searched 7/10/2026) — what is close, and how this differs

| work | what it shows | how this note differs |
|---|---|---|
| ⚠️ **Goren & Moses, "Silence"**, PODC 2018 / JACM 2020; **Nataf, Goren & Moses, "Null Messages, Information and Coordination"**, arXiv 2208.10866 | in **synchronous** systems, *not sending* carries information (null messages); "silent choir" = f+1 agents whose silence can be relied on; message patterns **necessary and sufficient** for information transfer and for the *Ordered Response* coordination task | **the closest work, and the same word.** They use silence *as a channel* under time bounds; here the system is **asynchronous** and silence is not observed but **decided** — a non-monotone commitment in Complete CALM's sense — and the result is a count (hitting number) per commitment. cited prominently here, and "silence commitment" is defined against their notion |
| **Chandra, Hadzilacos & Toueg**, J.ACM 1996 — the weakest failure detector for consensus is Ω | exactly **what information about failures** (≈ about silence) is necessary and sufficient to solve **consensus** | same *shape* (necessary and sufficient knowledge about who is silent) for one problem; this note gives a **count** for any specification's commitment, in the monotonicity framework, not the weakest detector |
| **Chandy & Misra**, null messages in conservative distributed simulation (1979); **Tucker, Maier et al.**, punctuations (TKDE 2003) | a participant's **promise** that it will send nothing more below a bound lets blocking operators proceed | this is the **closure** of §0 — prior art for closure; not claimed |
| **Ameloot, Ketsman, Neven, Zinn**, TODS 40(4), 2016 (PODS 2014); policy-aware transducers (Zinn, Green, Ludäscher, ICDT 2012) | knowing *who may still contribute* turns some non-monotone queries coordination-free | the open set C(H) plays that role; their results are qualitative (free or not), not a count |
| **Mencius** (OSDI 2008) | a silent owner's slots are revoked by agreement | one instance of a silence commitment (Seal) |
| **Ju, "When Coordination Is Avoidable"**, arXiv 2602.18673 (2026) | classifies organisational tasks as monotone or not; "coordination tax" = share of spending that is avoidable | qualitative per task; no minimum count |
| ⚠️ **Garcia-Molina & Barbara**, "How to assign votes in a distributed system", JACM 1985; **Ibaraki & Kameda**, "A Theory of Coteries", IEEE TPDS 4(7), 1993 | coteries = hypergraphs of process sets; a family is a coterie ⇔ its positive (monotone) Boolean function is dual-minor; non-dominated ⇔ self-dual; ND coteries decompose into 3-majorities | **same mathematical language** (monotone Boolean functions, duality, hypergraph transversals) in distributed systems, 1985–93. Their question is the *structure* of quorum families an engineer designs; ours is the *least coordination* of a commitment, with the family derived from the specification. The relation of F_open / D to coterie duality must be stated explicitly — open (§6). Read via Feng Xiao, PhD thesis, SFU 1998 (restates I–K); original not read in full |
| **Peleg & Wool** (1995), **Naor & Wool**, SIAM J. Comput. 1998; **Malkhi & Reiter**, Distrib. Comput. 1998 | quorum fault tolerance / vulnerability = **size of the smallest transversal** (failures that block every quorum); load via LP duality; Byzantine quorums | the **same number** (min transversal) in distributed systems, for **availability** of a designed family; here it measures **safety coordination** of a commitment. Hence: transversals in distributed systems are **not** new |
| **Pease, Shostak & Lamport** 1980, *interactive consistency* (agree on a vector, missing entries = null); Klianev, arXiv 2601.16460 (2026) | agreement on the vector of who contributed what | §8.4's "all τ commitments in one agreement instance" is this; not claimed. (Klianev's claim to escape FLP is not relied on) |
| **Taylor**, *Knowledge and Inhibition in Asynchronous Distributed Systems*, Cornell TR 90-1139, 1990 | inhibiting (delaying) actions is closely related to achieving concurrent common knowledge | closest in spirit to "coordination = making actions not count"; qualitative, no count, no mechanism trichotomy |
| **Power, Koutris & Hellerstein**, "The Free Termination Property of Queries Over Time", ICDT 2025 | when a node can terminate unilaterally without coordination, although more input may arrive — the completeness side of CALM | closest in the CALM line to **closure** (§0): a participant's own promise that nothing more comes. Not a count, and not about deciding *for* an open participant |
| **Attiya, Enea & Román-Calvo**, "Arbitration-Free Consistency", arXiv 2510.21304 (2025) | a storage specification admits an available implementation iff it needs no total arbitration order | detects one pattern (total-order), yes/no; this note gives a count per commitment |
| **Bailis et al.**, invariant confluence (PVLDB 8(3), 2014) | necessary and sufficient condition for coordination-free execution of invariants | yes/no criterion, like CALM; no amount |
| **Garcia-Molina & Salem**, Sagas (1987); **Helland & Campbell**, "Building on Quicksand" / apologies (CIDR 2009) | compensating actions instead of prevention | move (3) of §8.9b; claimed only: it is either unsafe (relies on a free participant) or a change of specification |

**Second search (7/10, evening):** CALM/coordination+compensation, minimal coordination as hitting set, failure-detector minimality,
knowledge/inhibition, I-confluence. No work found stating (a) coordination of a commitment = silence commitments only, with (b) the
exact count as a hitting number and (c) the three-move exhaustiveness. Closest: Taylor 1990 (inhibition), Goren & Moses (silence,
synchronous), CHT 1996 (information about failures). Absence of a hit is not proof of absence.

**Third search (9/10/2026).** Both earlier searches used the word "hitting set"; the distributed-systems literature says
*transversal*, *blocking set*, *coterie*. Under those words the quorum/coterie line above (1985–98) was found — missed on 7/10.

### 7a. Mathematical tools — not ours (added 9/10/2026)

| tool used here | source |
|---|---|
| hypergraph, transversal, transversal number τ | **Berge**, *Graphes et hypergraphes*, Dunod 1970 (Engl. 1973) |
| vertex cover (τ of a graph) | **Kőnig** 1931; **Gallai** 1959 |
| Vertex Cover / Hitting Set NP-complete (used in §8.3) | **Karp**, "Reducibility Among Combinatorial Problems", 1972 |
| greedy ln n approximation (§8.3) | **Johnson** 1974; **Lovász** 1975; **Chvátal** 1979 |
| ln n essentially optimal | **Feige** 1998; **Dinur & Steurer** 2014 |
| blocker / transversal duality; positive Boolean dual f^d (§8.11) | **Edmonds & Fulkerson** 1970; Berge; **Ibaraki & Kameda** 1993 |
| listing all minimal transversals (monotone dualization) | **Fredman & Khachiyan** 1996 |
| transversals / blocking sets in distributed systems | coteries and quorum systems, §7 table (Garcia-Molina & Barbara 1985; Ibaraki & Kameda 1993; Peleg & Wool; Naor & Wool; Malkhi & Reiter) |

**The question itself is Hellerstein's:** Complete CALM's conclusion names it — "Complexity theory invites quantitative questions:
given a non-monotone specification, how much coordination does it require?" This note is one answer to it.

**Verdict (revised 9/10/2026).** The mathematics is not ours (§7a), and neither is the use of transversals in distributed systems
(coteries, quorum fault tolerance). What may be new, and only as stated: in the Complete CALM framework, asynchronous, for **any**
specification, the least coordination of **one commitment** equals τ of F_open, and every mechanism contributes only silence
commitments (modulo the modelling step of §6.5). Not shown to be new: the relation to coterie duality (Ibaraki & Kameda) is not yet
written down. It is also **not** new that silence/absence carries the essential information (Goren & Moses; Chandra, Hadzilacos &
Toueg) or that closure lets blocking computation proceed (Chandy & Misra; Tucker et al.). A publication must say all of this.

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
has Inv = the upward closure of the edges, and hitting it is exactly a vertex cover (`VertexCover`). The reduction is ours; the
hardness is inherited: Vertex Cover is NP-complete (Karp 1972). Hence: *computing the least
coordination of a commitment is NP-hard* (decision version NP-complete when F_open is given explicitly; greedy gives a ln n
approximation (Johnson 1974, Lovász 1975, Chvátal 1979); polynomial when all minimal coalitions are singletons — the Seal case, τ = number open). *Paper:* deciding τ = 0 is
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

**8.11 Relation to coterie duality — the core is classical (9/10/2026, paper).** Let g(X) = 1 iff coalition X invalidates o. By
Fact 1, g is a positive (monotone) Boolean function whose minimal true sets are F(o, H). Its dual is g^d(D) = ¬g(N \ D). Then
D is safe ⇔ the free set N \ D invalidates nothing ⇔ g(N \ D) = 0 ⇔ **g^d(D) = 1**. So the safe silence sets are exactly the true sets
of the dual, the minimal ones are the minimal transversals (the *blocker*) of F, and τ is the size of a shortest prime implicant
of g^d. This is the classical transversal / blocker duality (Berge; Edmonds & Fulkerson 1970), the same duality f ↦ f^d that
Ibaraki & Kameda (1993) use for coteries: there, *coterie* ⇔ f ≤ f^d and *non-dominated* ⇔ f = f^d. Read here: if every two
invalidating coalitions intersect (g ≤ g^d), each coalition is itself a safe D; if g = g^d (e.g. majority), the coalitions that can
break o and the sets that must be silenced are the same family. Checks: Seal, g = i₁ ∨ … ∨ i_k, g^d = i₁ ∧ … ∧ i_k, τ = k; alarm,
g = i ∧ j, g^d = i ∨ j, τ = 1 (§5). Listing **all** minimal safe D is monotone dualization (hypergraph transversal enumeration),
solvable in quasi-polynomial time (Fredman & Khachiyan 1996).

**Consequence for novelty.** The set-theoretic core of Theorem 3 (safe ⇔ D is a transversal), and most of what
`MinimalSilence_Proof.tla` checks, is this classical duality. Our contribution, if any, is the modelling around it: (i) that a
Complete CALM specification yields such a monotone g at each commitment (origins of invocations + Fact 1), and (ii) that silence
is the only coordination that contributes (Theorem 2, three moves) — the step §6.5 names as the weak point. In I–K the engineer
chooses f (who may act); here the specification determines g (who can break the outcome) and g^d says whom to silence.

**8.12 Closing §6.5 from Complete CALM's own definitions (9/10/2026; Lemmas A and C checked, [`tla/CoordinatedVariant_Proof.tla`](tla/CoordinatedVariant_Proof.tla), TLAPS 52/52, with Lemma B under the named assumptions B1–B3).** The modelling step of §6.5 / §8.9b ("every mechanism
is captured by three moves, with free participants") is replaced here by two definitions of Complete CALM itself.
*Def. 5:* the environment controls invocations (E_inv) and deliveries; an implementation controls only responses, internal events
and sends. *Def. 11:* a properly coordinated variant Spec' = (E, Obs', ⪯) has Obs'(H) ⊆ Obs(H) and is monotone over its admitted
histories; coordination is expressed only by shrinking Obs or setting Obs'(H) = ∅ (forbidding H).

- **Lemma A (any coordinated variant must forbid every invalidating extension).** Let Spec' be a properly coordinated variant of Spec,
  o ∈ Obs'(H), S ∈ F_open(o, H), and H' an admissible S-extension with no refinement of o in Obs(H'). Then Obs'(H') = ∅.
  *Proof.* If Obs'(H') ≠ ∅, monotonicity of Spec' (Def. 11(2)) gives o' ∈ Obs'(H') ⊆ Obs(H') with o ⪯ o' — contradiction. ∎
- **Lemma B (forbidding = withholding someone's effect; checked under B1–B3).** H' differs from H by invocations of S
  (environment-controlled, Def. 5) and by the implementation's own events. Stated as three assumptions in
  [`tla/CoordinatedVariant_Proof.tla`](tla/CoordinatedVariant_Proof.tla) (`AssmB`): **B1** the environment may make any set A of open
  participants act; the implementation only chooses which of them get an effective response, Eff[A] ⊆ A (Def. 5); **B2** the variant
  admits some outcome on every run the environment can produce (it is realizable); **B3** if the *effective* set invalidates o, the
  run is an invalidating future (Def. 6) — outcomes are exposed only through responses. Then `LemmaB`: every properly coordinated
  variant keeps what takes effect outside Inv, i.e. silences someone in every coalition; and `Chain`: it silences ≥ τ in the run where
  all open participants act. "Free participants" is B1 = Def. 5, not our assumption. Non-vacuous: TLC finds a model of all
  assumptions with τ = 1 (alarm, first-come-wins), and a mechanism that silences nobody violates B2 (`tla/cv/`).
- **Lemma C (adaptive mechanisms pay τ in the worst case).** A mechanism need not fix D at H; it may decide whom to silence as invocations
  arrive (first-come-wins). In the run where **every** open participant acts, every S ∈ F_open is present, so by Lemma A–B the set
  silenced in that run meets every S: it has size ≥ τ. Adaptive mechanisms can pay less in a lucky run, never less than τ in the worst.

What remains a modelling step: **B3** — that a run's effect on o is determined by which invocations got effective responses. It is
the faithful reading of Def. 5 (the implementation acts only through responses), but it is an assumption, stated, not derived.

**8.13 Known mechanisms, move by move (9/10/2026; a reading, not a per-mechanism proof).** Where each one silences. "Silence" = the effect of an open participant's future
invocation is excluded before that participant has closed.

| mechanism | what it does | where the silence is | τ it pays |
|---|---|---|---|
| Lock / mutex (and 2PL) | holder proceeds; others wait | every other requester's acquire is held back until release | one per waiting conflicting participant |
| Lease | holder acts until expiry | others silenced until expiry; holder silenced *after* expiry, decided by a clock | as lock; **real time — outside §0** |
| Paxos / Raft (one slot) | a value is chosen by a quorum | proposers whose value is not chosen; acceptors that promised refuse lower ballots | one agreement instance per slot (§8.4) |
| 2PC | all vote, then commit/abort | after "prepared", a participant's later abort is excluded; coordinator decides for a silent one | one per participant not yet voted |
| Escrow / demarcation | each spends only its own share | none for local spends (F_open = ∅); reclaiming a silent holder's share | 0 / 1 (§5) |
| Mencius / owned slots | owner fills its own slots | a silent owner's slots revoked (no-op) | one per silent owner |
| Seal per period | close a period | every open participant's late records excluded | number open |
| CRDT, monotone queries | merge | none | 0 — not coordination (Complete CALM) |
| Sagas / apologies | act, compensate later | **none** if the apology is admissible (the spec changed); unsafe if it relies on a participant who may decline (§8.9b) | 0 or unsafe |
| Speculation + rollback | expose, roll back on conflict | exposed outcome is not committed until the rollback window closes; closing it silences late conflicting invocations | as the closing mechanism |
| Admission control at ingress (e.g. each key owned by one participant) | reject at the door | rejection of a non-owner = closure by design: the invocation never had effect | 0 at commit; the cost moved into the spec |

**8.14 Outside the claim — stated plainly.** The result does **not** cover: (i) **real time** — leases, timeouts, deadlines decide
silence by a clock; Complete CALM has no time, and neither does this note; (ii) **probabilistic** correctness (o is safe with probability
p) — Def. 7 is all-or-nothing; (iii) **changing the specification** — weakening Obs (accepting apologies, reordering) is not
coordination; it removes coalitions and lowers τ, possibly to 0; (iv) **changing membership** (§8.7) and **lying participants** (§8.8);
(v) **liveness** (§8.5). Within these limits, Lemmas A–C say: every properly coordinated variant silences, and pays at least τ in the
worst case.

**Still open after §8:** necessity of Ω (8.5) · different commitment times inside a scope (8.2) · mechanised Byzantine version (8.8) ·
mechanising 8.1's abstraction against a concrete language (e.g. Hydro).
