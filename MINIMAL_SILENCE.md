# The Silence Theorem — coordination in Complete CALM is a transversal of silences

*For implementations that accept or refuse (B1), silence is the only coordination, and τ (a transversal number) is exactly how much of it in the worst case — one commitment at a
time, for specifications where whether the commitment breaks depends only on, and grows with, the set of participants whose invocations took effect (property B3, §8.12), with the
implementation's lever modelled as "which invocations take effect" (§6 item 5). Read as CAP: a silence is a refusal, i.e. lost
availability; τ is the least number of participants that must be refused to keep one commitment consistent (README; prior art §7).*

Draft, 7 October 2026 · Vasilis Nasopoulos. Generalises [SILENCE.md](SILENCE.md) (which proves the same for the Seal
specification) to one commitment of any specification with properties B1 and B3 (§8.12, §8.16). Framework and terms: Hellerstein, *Complete CALM*, arXiv 2602.09435 — a specification
Spec = (E, Obs, ⪯); an outcome o ∈ Obs(H) is *refinable* at H' ⊒ H if some o' ∈ Obs(H') has o ⪯ o'. Paper proofs; the parts marked *checked* are machine-checked (TLAPS).

## 0. Setting
- Membership N is **fixed and known** (Complete CALM, Remark 3 — the one non-monotone act, taken once, outside this note).
- Every **invocation** in E has an origin participant orig(e) ∈ N. Receipts and protocol messages are not choices of anyone.
  This is Complete CALM's own *process assignment* π (§5, used for Complete CAP), restricted to invocations.
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

> **Scope of Theorems 1–3.** Read §2–4 under two conditions, made precise in §8.12. **B1** (the mechanism): the environment
> decides who acts; the implementation only accepts or refuses each invocation — it does not pick values for responses (when it
> does, coordination without silence exists: renaming, §7). **B3** (the specification): an outcome changes only through invocations
> that take effect (a refusal leaves no trace, and more participants taking effect can only break more). B3 is exactly what the proof uses (§8.16);
> "a refusal leaves no trace" alone is not enough (§8.16, counterexample). Without B3 the exact count need not be τ. What holds for *every*
> specification, from B1 and B2 alone, is only that the realised run never breaks o (`OnlySilence`, §8.12). Throughout: one
> commitment at a time, membership fixed and known (§0).

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
member of D is an agreement of the kind proved safe in [`tla/CalmSeal_Proof.tla`](tla/CalmSeal_Proof.tla) (TLAPS, 340/340) for the Seal case, where every
coalition is a single participant; for a general D the upper bound in Complete CALM's terms is `Sufficiency` (§8.12). Hence **τ(F_open(o, H)) commitments
suffice**.

> **Exact:** the least coordination needed to commit o at H is **τ(F_open(o, H)) silence commitments** — no fewer is possible, no more
> is necessary, and no other kind of coordination contributes — under B1 and B3 (scope above), in the worst case (every open
> participant acts; §8.12, Lemma C).

**What the count measures, and what it leaves out.**

| measures | does not measure |
|---|---|
| how many participants must be refused (silenced) to keep one commitment consistent | rounds: τ ≥ 1 costs one agreement instance, independent of τ (§8.4) |
| the worst case over runs (adaptive mechanisms may pay less in a lucky run) | messages, bytes, or time — the latency axis of CAL / PACELC (§7) |
| per commitment, for a fixed and known membership | liveness: Theorem 3 is safety only (§8.5) |
| | the cost of a membership change (paid once per epoch, §8.7) |
| | implementations whose responses carry values they choose (renaming, §7) |

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
   (union). Commitments taken at different times inside one scope: §8.15 (bounds; the online case is online hitting set, prior art).
2. **Liveness.** That commitments get taken needs a partial-synchrony / failure-detector assumption (FLP). §8.5: Ω suffices; whether it
   is necessary — open.
3. **Suspected ≠ silent.** In practice the commitment is about a participant not yet heard from; it may be merely slow (§8.6).
4. **Outside the setting:** the admission mechanism itself (how a member joins or leaves; the count is in §8.7), lying participants (§8.8, paper only), real-time deadlines; counterexamples
   at these boundaries in §8.10.
5. **Partly machine-checked.** [`tla/MinimalSilence_Proof.tla`](tla/MinimalSilence_Proof.tla) (TLAPS, 112/112, 7/10) proves the set-theoretic core, see §8: safe ⇔ D hits every
   open invalidating coalition ⇔ D hits every minimal one — so the least |D| is the hitting number; and Theorem 2(b) for any
   mechanism made of the three moves of §8.9b ([`tla/ThreeMoves_Proof.tla`](tla/ThreeMoves_Proof.tla), 36/36). What stays a modelling
   step: that every mechanism is captured by those moves, with free participants. A reviewer will test that first.
   **Update 9/10:** §8.12 derives this from Complete CALM's Defs. 5 and 11 (Lemmas A–C, OnlySilence, Sufficiency: TLAPS 121/121 on 9/10; 183/183 with the additions of 15/10, §8.16–8.17; the exact count needs property B3 of the specification); §8.13 maps known mechanisms;
   §8.14 states what is outside. For every specification, a coordinated variant keeps the realised run from breaking o; that this
   means silencing someone needs B3, and so does the exact count τ. The reduction of Def. 5 to "which invocations take effect"
   remains a modelling step, and a real restriction: it holds for implementations that accept or refuse, not for ones that assign
   values (seats, identifiers, positions) — the renaming problem (Attiya, Bar-Noy, Dolev, Peleg & Reischuk, J.ACM 1990) — where
   coordination without silence exists (§8.12, B1).
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
| ⚠️ **Hellerstein, Complete CALM §5 — Complete CAP** (Defs. 12–13: process assignment π, partition-constrained futures, distributed-monotone) | attributes events to processes and asks whether an outcome survives every future in which the process set is cut into **two** sides that keep acting | **the closest step in the same paper.** The S-extensions of §0 restrict **who invokes**; his partition-constrained futures restrict **which messages cross a cut** — related, but not shown to be a generalisation (referee 15/10). The question moves from yes/no to **how many** participants must be silenced (τ). The bridge to transversals is built on his process assignment |
| **Power, Koutris & Hellerstein**, "The Free Termination Property of Queries Over Time", ICDT 2025 | when a node can terminate unilaterally without coordination, although more input may arrive — the completeness side of CALM | closest in the CALM line to **closure** (§0): a participant's own promise that nothing more comes. Not a count, and not about deciding *for* an open participant |
| ⚠️ **Houshmand & Lesani, Hamsaz**, PACMPL 3 (POPL 2019), art. 74 | from a sequential spec + invariant, a conflict graph over **methods** (pairwise); synchronise only a **minimum vertex cover** of it (or one total-order broadcast per maximal clique); well-coordination is a **sufficient** condition | **the same shape** — least coordination as a cover of a conflict graph — six years earlier. Differences: vertices are participants here, not methods; edges are coalitions of any size (hypergraph), not pairs; a **lower bound** is proved here (Thm 1(b), Lemma C), not only sufficiency. §8.3's vertex-cover reduction must cite it. |
| **Gotsman, Yang, Ferreira, Najafzadeh, Shapiro**, CISE, POPL 2016; **Balegas et al.**, Indigo, EuroSys 2015; **Li et al.**, RedBlue, OSDI 2012 | which operations of a replicated application must synchronise to preserve invariants: token/conflict relations, reservations, red/blue labels | the same family as Hamsaz (pairs of operations, sufficiency); no lower bound per commitment, no silence. Added after review 15/10; read from abstracts and summaries |
| **Attiya, Guerraoui, Hendler, Kuznetsov, Michael, Vechev**, *Laws of Order*, POPL 2011 | in shared memory, every strongly non-commutative method must use a fence (RAW) or an atomic read-modify-write (AWAR) | a **lower bound on synchronisation**, existence only, shared memory; here a count per commitment in message passing. Read: introduction and definitions |
| **Mazières**, Stellar Consensus Protocol, 2015 | *v-blocking sets*: sets that intersect every slice of a node — transversals used for safety and liveness in federated agreement | transversals again, for a designed slice system; not a count derived from a specification. Added after review 15/10, not read in full |
| **Halpern & Moses**, J. ACM 37(3), 1990 | common knowledge cannot be attained asynchronously | background for §8.9 (silence observed vs decided); Hellerstein's *Determinations* (2026) re-derives it as a depth threshold |
| **Whittaker & Hellerstein**, *Interactive Checks for Coordination Avoidance*, PVLDB 12(1), 2018; **Balegas et al.**, IPA, PVLDB 2018; **Houshmand, Saberlatibari & Lesani**, Hamband, PLDI 2022; **Chu et al.**, protocol rewrites in Hydro, SIGMOD 2024 | which operations or protocol steps need coordination, decided or rewritten automatically | qualitative or sufficiency, per operation; no per-commitment lower bound. Added after review 15/10, not read in full |
| **Attiya, Enea & Román-Calvo**, "Arbitration-Free Consistency", arXiv 2510.21304 (2025) | a storage specification admits an available implementation iff it needs no total arbitration order | detects one pattern (total-order), yes/no; this note gives a count per commitment |
| **Bailis et al.**, invariant confluence (PVLDB 8(3), 2014) | necessary and sufficient condition for coordination-free execution of invariants | yes/no criterion, like CALM; no amount |
| **Brewer**, *CAP Twelve Years Later: How the "Rules" Have Changed*, IEEE Computer 45(2), 2012 | in partition mode, *limit some operations, thereby reducing availability* (ATM: withdraw at most k), or record intent and execute after recovery; which operations depends on the invariants | refusing = losing availability, delaying = acting later — said here, qualitatively; no count of who must be refused — that count (τ) is this note |
| **Kleppmann**, *A Critique of the CAP Theorem*, arXiv 1509.05393, 2015; **Golab**, *Proving PACELC*, SIGACT News 49(1), 2018; **Lipton & Sandberg** 1988; **Attiya & Welch** 1994 | latency side: operations O(d) vs O(1); for a consistent register r + w ≥ d (tight); PACELC = CAP + this bound | the time axis of the same trade-off; not counted here |
| **Lee, Bateni, Lin, Lohstroh & Menard**, *Quantifying and Generalizing the CAP Theorem* (CAL theorem), arXiv 2109.07771, 2021 | inconsistency and unavailability as **time** intervals; an algebraic relation with apparent latency; CAP as the unbounded-latency case | quantifies CAP **in time**; this note counts **who** must be refused (participants, per commitment, worst case) — a different axis; the phrase "quantifying CAP" is theirs |
| **Yu & Vahdat**, TACT (OSDI 2000; TOCS 2002) and *The Costs and Limits of Availability for Replicated Services* (SOSP 2001) | numerical error / order error / staleness traded for availability; availability = accepted ÷ submitted accesses; **upper bounds** per workload and faultload by search / LP | the closest on **counting refusals**; per workload and consistency model, computed — not a structural statement per commitment (τ of the breaking coalitions) |
| **Fox & Brewer**, *Harvest, Yield, and Scalable Tolerant Systems*, HotOS 1999 | yield = fraction of requests answered; harvest = fraction of the data in an answer | a metric, no lower bound |
| **Abadi**, PACELC, IEEE Computer 45(2), 2012 | under a partition, availability vs consistency; else latency vs consistency — a classification | qualitative; no amount |
| **Attiya, Bar-Noy, Dolev, Peleg & Reischuk**, *Renaming in an Asynchronous Environment*, J.ACM 37(3), 1990; wait-free shared memory: 2n−1 names (Attiya & Welch; Aspnes notes); Castañeda & Rajsbaum (Distrib. Comput. 2010, J.ACM 2012): 2n−2 solvable for some n; Castañeda, Imbs, Rajsbaum & Raynal, LATIN 2012: n ≤ M ≤ 2n−2 stronger than registers, weaker than 2-consensus | **renaming**: give each participant a distinct name from a small namespace — measured by namespace size and synchronization power | the "coordination without silence" found 13/10 (an implementation that **assigns values**, e.g. seats) is this problem; it is prior art, and the theorem's class excludes it (B1: accept or refuse). |
| **Alvaro, Conway, Hellerstein & Maier**, *Blazes: Coordination Analysis for Distributed Programs*, arXiv 1309.3324 (2013; ICDE 2014 not verified) | dataflow analysis that places coordination; **sealing** = a producer's punctuation that a partition of a stream stopped changing, chosen over global ordering when compatible; "a minimum of coordination" as a design goal | the word **Seal** in this group's line since 2013 — must be cited. Sealing there is **closure** (the producer's own promise, §0), not silence of a producer that does not seal; no count, no lower bound |
| **Kuper, Turon, Krishnaswami & Newton**, *Freeze After Writing*, POPL 2014 (LVars) | lattice-valued shared variables; threshold reads are deterministic; **freeze** forbids further writes and lets the exact value be read — quasi-determinism | freeze ≈ closure/seal for one variable in **shared memory**, decided after local quiescence; no participants, coalitions or count |
| **Laddad, Power, Milano, Cheung, Crooks & Hellerstein**, *Keep CALM and CRDT On*, PVLDB 16(4), 2022 | queries over CRDTs: threshold (monotone) queries need no coordination; non-monotone ones: "the simple and safe solution is to coordinate", along the Bernstein–Goodman read/write-quorum spectrum | qualitative (monotone or not); the remedy is generic quorums — no least amount, no silence |
| **Garcia-Molina & Salem**, Sagas (1987); **Helland & Campbell**, "Building on Quicksand" / apologies (CIDR 2009) | compensating actions instead of prevention | move (3) of §8.9b; claimed only: it is either unsafe (relies on a free participant) or a change of specification |

**Second search (7/10, evening):** CALM/coordination+compensation, minimal coordination as hitting set, failure-detector minimality,
knowledge/inhibition, I-confluence. No work found stating (a) coordination of a commitment = silence commitments only, with (b) the
exact count as a hitting number and (c) the three-move exhaustiveness. Closest: Taylor 1990 (inhibition), Goren & Moses (silence,
synchronous), CHT 1996 (information about failures). Absence of a hit is not proof of absence.

**Searches 13–14/10/2026 (rows above):** CRDT/lattice line (Blazes, LVars, Keep CALM and CRDT On), renaming, and the CAP/PACELC line
(Brewer 2012, CAL, Yu & Vahdat, harvest/yield, PACELC, Kleppmann, Golab). None counts or bounds who must be refused for one commitment.
Absence of a hit is not proof of absence.

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
(coteries, quorum fault tolerance). What may be new, and only as stated — building on Complete CALM's process assignment and partition-constrained futures (§5,
Defs. 12–13), with S-extensions in place of his partition-constrained futures (a related restriction, not shown to be a generalisation, §7): in the Complete CALM framework, asynchronous, for any
specification with property B3 and an implementation that accepts or refuses (B1, §8.12), the least coordination of **one commitment** equals τ of F_open, and every mechanism contributes only silence
commitments (modulo the modelling step of §6 item 5). Not shown to be new: the relation to coterie duality (Ibaraki & Kameda) is not yet
written down. Nor is minimising coordination as a cover of a conflict graph (Hamsaz, POPL 2019). It is also **not** new that silence/absence carries the essential information (Goren & Moses; Chandra, Hadzilacos &
Toueg) or that closure lets blocking computation proceed (Chandy & Misra; Tucker et al.). A publication must say all of this.

## 8. Beyond the count — what else follows (7 October 2026)

Machine-checked parts are in [`tla/MinimalSilence_Proof.tla`](tla/MinimalSilence_Proof.tla) (112/112), [`tla/CoordinatedVariant_Proof.tla`](tla/CoordinatedVariant_Proof.tla) (183/183), [`tla/Temporal_Proof.tla`](tla/Temporal_Proof.tla) (45/45), [`tla/B3Patterns_Proof.tla`](tla/B3Patterns_Proof.tla) (41/41), [`tla/ThreeMoves_Proof.tla`](tla/ThreeMoves_Proof.tla) (36/36) and [`tla/Membership_Proof.tla`](tla/Membership_Proof.tla) (161/161); the rest are paper proofs, marked. The machine-checked parts are short set-theoretic lemmas; the substance is the modelling (B1, B3, the per-commitment form of Def. 11).

**8.1 Every mechanism silences someone (Theorem 2(b), checked).** Model a mechanism as *any* rule Eff that, in the extension where
coalition S acts, lets only Eff[S] ⊆ S take effect. If it keeps o correct in every extension, then for every S ∈ F_open, S \ Eff[S] ≠ ∅
(`SilenceNecessary`). A commitment taken at H, before anyone acts, is the case Eff[S] = S \ D for one D (`FixedMechanism`), and then
`Exact` gives |D| ≥ τ. *What is still a modelling step:* that "takes effect" is the right abstraction of every mechanism's contribution.

**8.2 Over a run (checked for the union step).** A commitment about i in a scope serves every outcome of that scope. Hitting the families
of several outcomes = hitting their union (`RunUnion`), so the least total per scope is **τ(⋃ₒ F_open(o))**, and over a run the sum over
scopes. When commitments in one scope are taken at different times (H differs per outcome), the families change in between: §8.15.

**8.3 Hardness (reduction checked).** For any graph G, the alarm specification "alarm iff both ends of some edge press; commit *no alarm*"
has Inv = the upward closure of the edges, and hitting it is exactly a vertex cover (`VertexCover`). The reduction is ours; minimising synchronisation by a minimum vertex cover of a conflict graph is Hamsaz's (Houshmand & Lesani, POPL 2019, over methods); the
hardness is inherited: Vertex Cover is NP-complete (Karp 1972). Hence: *computing the least
coordination of a commitment is NP-hard* (decision version NP-complete when F_open is given explicitly; greedy gives a ln n
approximation (Johnson 1974, Lovász 1975, Chvátal 1979); polynomial when all minimal coalitions are singletons — the Seal case, τ = number open). *Paper:* deciding τ = 0 is
deciding whether the commitment is monotone, undecidable in general (Complete CALM §3.6); so τ is **uncomputable** in general.

**8.3b Quick lower bound (Berge).** If ν coalitions in F_open are pairwise disjoint, any transversal needs a distinct member of
each, so τ ≥ ν (matching number ≤ transversal number; Berge, *Graphes et hypergraphes*; for graphs, Kőnig 1931). In practice: finding
ν disjoint coalitions that can break a commitment shows that at least ν silences are needed, without computing τ — and a system that
pays fewer is unsafe.

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

**8.7 Changing membership (checked, [`tla/Membership_Proof.tla`](tla/Membership_Proof.tla), TLAPS 161/161; TLC model in `tla/mb/`).** Removing i = one commitment that i is silent in every later scope (one agreement, Complete CALM
Remark 3). Adding j is safe if j's invocations count only in scopes opened after its admission — j is *closed by construction* for the
earlier ones, so F_open of every earlier outcome is unchanged. Theorems 1–3 then hold per membership epoch; each change costs one
agreement.
Checked: after a join, D is safe iff D \ {j} was safe before — silencing the newcomer never helps an earlier commitment — and τ of
every earlier commitment is unchanged (`JoinSafe`, `JoinKeepsTau`). After i leaves, D is safe iff D ∪ {i} was, and
τ_without_i ≤ τ_with_i ≤ τ_without_i + 1 (`LeaveSafe`, `LeaveTau`): a removal saves at most one silence, at the price of the one
agreement that removes i. TLC: τ = 2 kept by a join, dropped to 1 by a leave (the bound is tight). How a system admits or removes a
member is not modelled. *Scope:* this is in the model of §0, not in Complete CALM's own definitions. It carries over to them through `Exactly` (§8.12)
for specifications with property B3 — on paper: that a join or a leave preserves B3 is not machine-checked.

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
is the only coordination that contributes (Theorem 2, three moves) — the step §6 item 5 names as the weak point. In I–K the engineer
chooses f (who may act); here the specification determines g (who can break the outcome) and g^d says whom to silence.

**8.12 Closing §6 item 5 from Complete CALM's own definitions (9/10/2026; Lemmas A–C, OnlySilence, Sufficiency checked, [`tla/CoordinatedVariant_Proof.tla`](tla/CoordinatedVariant_Proof.tla), TLAPS 121/121 then, 183/183 with §8.16–8.17; only the exact count needs property B3).** The modelling step of §6 item 5 / §8.9b ("every mechanism
is captured by three moves, with free participants") is replaced here by two definitions of Complete CALM itself.
*Def. 5:* the environment controls invocations (E_inv) and deliveries; an implementation controls only responses, internal events
and sends. *Def. 11:* a properly coordinated variant Spec' = (E, Obs', ⪯) has Obs'(H) ⊆ Obs(H) and is monotone over its admitted
histories; coordination is expressed only by shrinking Obs or setting Obs'(H) = ∅ (forbidding H).

- **Lemma A (any coordinated variant must forbid every invalidating extension).** Let Spec' be a properly coordinated variant of Spec,
  o ∈ Obs'(H), S ∈ F_open(o, H), and H' an admissible S-extension with no refinement of o in Obs(H'). Then Obs'(H') = ∅.
  *Proof.* If Obs'(H') ≠ ∅, monotonicity of Spec' (Def. 11(2)) gives o' ∈ Obs'(H') ⊆ Obs(H') with o ⪯ o' — contradiction. ∎
- **Lemma B (forbidding = withholding someone's effect).** H' differs from H by invocations of S (environment-controlled, Def. 5)
  and by the implementation's own events. In [`tla/CoordinatedVariant_Proof.tla`](tla/CoordinatedVariant_Proof.tla): **B1** the
  environment may make any set A of open participants act; the implementation only chooses which of them take effect, Eff[A] ⊆ A
  (B1 models Def. 5 for implementations whose only choice per invocation is accept or refuse; it is narrower than Def. 5: a response
  that carries a value the implementation picks is a lever B1 does not have — e.g. two bookings, alone each gets seat a, together
  one gets a and the other b: coordination, and no one is silenced); **B2** the variant admits some outcome on every run the environment can produce (it is realizable).
  - `OnlySilence` — **from B1 and B2 alone, for every specification:** in every run, what a realizable properly coordinated variant
    lets take effect never breaks o. Its only lever is whose invocations count — but that is how B1 models Def. 5, not a consequence
    of it, and the theorem does not exclude silencing nobody (Eff[A] = A). That someone in every open invalidating coalition is
    silenced needs B3 (`LemmaB`).
  - `NoVariantIfAttemptsBreak` — if the mere attempt of some set A breaks o whatever is silenced, no realizable properly coordinated
    variant exists at all: no coordination can save that commitment.
  - **B3** (whether the commitment breaks depends only on, and grows with, the set of participants whose invocations took effect) is now a *property of the specification*, not an
    assumption of the theorem. With it, `LemmaB`: what is silenced meets every invalidating coalition; and `Chain`: in the run where all
    open participants act, at least τ are silenced. Non-vacuous: TLC finds a model of B1–B3 with τ = 1 (alarm, first-come-wins), and a
    mechanism that silences nobody violates B2 (`tla/cv/`, with mutants).
- **Sufficiency, in the same terms (`Sufficiency`, `Exactly`).** Silence a minimum transversal D of F_open: let everyone take effect
  except D, and admit on each run exactly the outcomes that refine o. This is a properly coordinated variant at the commitment
  (Def. 11 for the pairs that start at H, the per-commitment form used throughout), it is realizable on every run, and it silences
  exactly D, i.e. τ participants — for specifications where an outcome is broken exactly when what took effect is an invalidating
  coalition (B3, both halves). With Lemma C: **in Complete CALM's terms, per commitment (`ProperAt`, our weakening of Def. 11), the
  least coordination of a commitment is exactly τ silences**; under the global Def. 11, τ is a lower bound (§8.17). TLC: the τ = 1 silence variant is proper and realizable; silencing nobody is not (`tla/cv/tlc_MC_Suff.out`, mutant `tlc_MC_Suff_mut.out`).
- **Lemma C (adaptive mechanisms pay τ in the worst case).** A mechanism need not fix D at H; it may decide whom to silence as invocations
  arrive (first-come-wins). In the run where **every** open participant acts, every S ∈ F_open is present, so by Lemma A–B the set
  silenced in that run meets every S: it has size ≥ τ. Adaptive mechanisms can pay less in a lucky run, never less than τ in the worst.

What remains: for every specification (B1, B2) the realised run never breaks o; *only silence coordinates*, in the sense that
someone in every open invalidating coalition is silenced, and the **exact count τ** (worst case: the run where every open
participant acts) hold for specifications with property B3; for one where a refused invocation still changes the outcome (e.g. the outcome reports
how many were refused), the count is the least number of invocations that must be kept from counting — still silence, but not
necessarily τ(F_open).

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
coordination; it removes coalitions and lowers τ, possibly to 0; (iv) **how** membership changes (the counting is in §8.7, in the model of §0) and **lying participants** (§8.8);
(v) **liveness** (§8.5). Within these limits, Lemmas A–C say: every properly coordinated variant silences, and pays at least τ in the
worst case.

**8.15 Several commitments taken at different times (15/10/2026; bounds elementary, online case is prior art).** This answers the
open part of §8.2 as far as it goes. A silence about i stays in force for the scope, so a coalition with a silenced member breaks nothing
later. For commitments o₁, o₂ in one scope:
- **Future known** (both families known when the first silence is chosen): the least total is τ(F₁ ∪ F₂), and
  max(τ₁, τ₂) ≤ τ(F₁ ∪ F₂) ≤ τ₁ + τ₂. Both ends are reached (the same family twice → the max; disjoint families → the sum). So
  "number of commitments × τ" is only an upper bound.
- **Future unknown** (F₂ revealed after the first silences are chosen): this is **online hitting set**, the dual of online set cover
  (Alon, Awerbuch, Azar, Buchbinder & Naor, STOC 2003; SIAM J. Comput. 2009) — a coalition that arrives is their element, a participant
  whose silence hits it is their set, and a set once taken stays. Their results carry over unchanged and are theirs: over a sequence of
  up to |N| commitments, each revealed after the previous silences, an adversary can force silencing **every** participant where one
  would have sufficed with the future known (their Prop. 8: the coalition "everyone", then "everyone but those already silenced", …), and a deterministic strategy within O(log m · log n) of the offline least exists
  (m = participants, n = the coalitions that can actually arrive; with n up to 2^|N| the bound is weaker than the trivial |N|, so it helps only when n is polynomial in |N|). Smallest instance: F₁ = {{a,b}}, F₂ ∈ {{{a}}, {{b}}} — 1 silence with the future known, 2 without.
- **Relation to determination depth** (Hellerstein, *On the Complexity of Determinations*, arXiv 2603.28031, 2026): depth counts the
  sequential layers of commitments, and its framework leaves fault-tolerant settings outside; τ counts the silences within one
  commitment — where a participant that may have stopped enters. The online/offline distinction above is his, measured here in silences.
- Checked: [`checks/layers.py`](checks/layers.py) — every first family F₁ with every set of up to two possible second families, among families of ≤ 3 coalitions on 3 participants and ≤ 2 on 4 (3,078 and 173,950 cases), 0 violations
  of the bounds above, and online > offline found ([`checks/layers.out`](checks/layers.out)). Not machine-proved (TLAPS); the bounds are
  elementary properties of hitting sets, and the online bounds are Alon et al.'s.

**8.16 After an independent review (15/10/2026) — what B3 is, one notion of variant, time.**
- **B3 as proved.** `CoordinatedVariant_Proof.tla` uses B3 (if the participants whose invocations took effect include an invalidating
  coalition, o breaks) and B3conv (if they do not, o still has a refinement). Together: *whether o breaks depends only on, and grows
  with, the set of participants that took effect*. "A refusal leaves no trace" is the first half only, and is **not enough**:
  "alarm iff **exactly one** of i, j presses; commit *no alarm*" leaves no trace of a refusal, has F_open = {{i}, {j}} and τ = 2, yet a
  mechanism that refuses a lone presser and accepts both together silences at most one in any run — even with deferral (a lone
  presser waits forever = is refused). It breaks the "grows with" half: both pressing does not break o.
  [`checks/b3.py`](checks/b3.py) ([`checks/b3.out`](checks/b3.out)), exhaustive over every commitment on 3 and 4 participants
  (128 and 32,768): B3 holds for exactly the monotone ones (19 and 167); for **all** of them the least worst-case number silenced equals
  τ (19/19, 167/167); without B3 it is below τ in 61 and 26,473 — counted against mechanisms that see the whole set of actors, so
  these gaps bound what an asynchronous mechanism could save from above. The check covers commitments whose breaking depends on E
  only (a refusal leaves no trace); within that class B3 ⇔ monotone. Seal, escrow reclaim, "alarm iff both", majority: B3 holds.
  **For the patterns, for any number of participants** ([`tla/B3Patterns_Proof.tla`](tla/B3Patterns_Proof.tla), TLAPS 41/41): when the
  outcome depends only on the events that counted and adding counted events never repairs o (`UpClosed`), breaking grows with the
  set of participants that took effect and `Broken(E) ⇔ E ∈ Inv` (`MonoBroken`, `B3Holds`). ⚠️ Here `Broken(E)` is **existential**:
  *some* choice of events by E breaks o — the worst case, with the environment choosing the harmful events. That is B3/B3conv of
  `CoordinatedVariant_Proof` when the run's history is the worst one for E; for a run in which a participant submits a harmless event it
  is not (independent review 15/10: in *before w*, a participant may submit an event after w; it takes effect and o does not break). Instances proved upward
  closed: Seal (any new event in a closed period), *before w* (an event ordered before w — unique choice with w the winner, total order
  with w the last event of the committed prefix), and *more than k* (a budget of k units, unit purchases). These are our formalisations
  of the Appendix F patterns, not his text, and *before w* uses an order on events given in advance (a timestamp-like order); in an
  asynchronous system the order is what coordination produces, so for unique choice and total order this is an abstraction; budgets with weighted purchases are not covered here. The referee's counterexample is not
  upward closed ({press_i} breaks o, {press_i, press_j} does not), so `B3Holds` does not apply to it.
- **One notion of variant for both bounds.** The lower bound `Chain` assumed Def. 11 over all pairs of histories (`ProperVariant`), the
  upper bound `Sufficiency` only over pairs that start at the commitment (`ProperAt`). `LemmaAAt`, `LemmaBAt`, `ChainAt`, `ExactlyAt`
  prove the lower bound under `ProperAt` too, so "exactly τ" now holds for one, per-commitment notion (the weaker one, so the lower
  bound is the stronger statement). Under the global Def. 11 the lower bound holds and the minimum can be larger (§8.17).
- **Time, deferral, arrival order — worst case only** (the step from a run to E is a paper argument; `PerRunLowerBound` is the set
  lemma it rests on). The model chose Eff[A] knowing the whole set A. In the run where every open participant acts **with the events
  that break o** (B1 lets the environment produce it; this is the worst case — with harmless events fewer may suffice),
  whatever set E took effect — chosen in any order, after any deferral, with any partial knowledge; a deferral that
  never ends is a refusal — correctness says o is not broken; by B3 (its "depends only on E" half: the same E breaks o or not, whatever the order) E is not
  an invalidating coalition; then Open \ E hits F_open (`PerRunLowerBound`), so at least τ are silenced. The upper bound is already
  online: the τ-variant refuses a fixed D and accepts everyone else, a rule needing no knowledge of who else will act.
- **What `MinimalSilence_Proof` checks** is the statement for any upward-closed family of coalitions; how that family arises from a
  specification is this note's modelling (§1, §8.12), not part of that module.
- TLAPS for `CoordinatedVariant_Proof.tla` after these additions: **All 173 obligations proved** (183 with §8.17).

**8.17 Executions in time, and the global Def. 11 (15/10/2026).**
- **The per-run lemma in a state machine** ([`tla/Temporal_Proof.tla`](tla/Temporal_Proof.tla), TLAPS 45/45). An asynchronous run: the environment makes open
  participants act one at a time in any order; the mechanism answers each pending invocation with accept or refuse whenever it likes,
  or never (deferral), under any policy — the next-state relation is fully nondeterministic. With B3 (breaking = the accepted set is in
  Inv, proved for the patterns in §8.16): `LowerBound` — in every behaviour that never breaks o, every state where all open participants
  have acted has at least τ refused or still pending; `UpperBound` — the policy "refuse D, accept everyone else" never breaks o when D
  hits F_open, and `PolicySilencesOnlyD` — it refuses nobody outside D. *What this does and does not add* (independent review 15/10):
  because breaking depends only on the current accepted set and each participant invokes once with a harmful event, order cannot
  matter by construction; `LowerBound` is the per-state lemma `Core` (= `PerRunLowerBound`) holding in every reachable state, and the
  mechanism may know everything. The policy has no fairness: a run that accepts nobody also satisfies it, so `PolicySilencesOnlyD` says
  only that refusals stay inside D, not that everyone else is accepted. If ∅ ∈ Inv (o breaks with nobody acting) there is no τ and the
  theorems hold vacuously. TLC ([`tla/temporal/`](tla/temporal/)): three participants, "alarm iff 0 and 1"
  (τ = 1), any mechanism and the policy D = {0}: no error; the mutant policy that refuses nobody violates safety.
- **Global Def. 11 — the lower bound carries over, the upper bound does not.** `GlobalImpliesAt` (`CoordinatedVariant_Proof.tla`,
  183/183): a variant that is properly coordinated over all pairs of histories is one at the commitment, so at least τ (and `Chain`
  states it directly). But [`checks/global.py`](checks/global.py) ([`checks/global.out`](checks/global.out)) finds specifications with B3
  where every globally proper variant **that silences a fixed set D** silences more than τ (892 of 10,164 sampled on 2 participants; 299
  of 677 and 109 of 263 on 3). Almost all have τ = 0 (the commitment itself is never at risk): with τ ≥ 1 the gap appears in 0 of 4,747,
  1 of 223 and 4 of 85. Smallest: τ = 0, Obs({}) = {0,2}, Obs({a}) = {1}, Obs({b}) = {2}, Obs({a,b}) = {0}, with 0 ⪯ 1, 0 ⪯ 2, 2 ⪯ 1: after a acts
  the only outcome is 1, after both only 0, and 1 has no refinement 0 — so someone must be silenced. The reason: the global Def. 11 makes
  the variant **repair the specification's non-monotonicity everywhere it can reach**, also where o is not involved. That cost belongs
  to the specification's other non-monotone points, not to o. *Conjecture (not proved):* the global minimum is the cost of all those points
  together, i.e. a sequence of commitments as in §8.15. History-dependent silencing is not searched. *Statement, precisely:* τ is the least
  coordination of one commitment under the per-commitment form (our weakening of Def. 11); under Hellerstein's global Def. 11 it is a lower
  bound, attained when the specification has no other non-monotone point the variant can reach.

**Still open after §8:** the global minimum (8.17, conjectured: the cost of all reachable non-monotone points) · B3 for runs with harmless events, and for orders not given in advance (8.16) · necessity of Ω (8.5) · whether the online gap (8.15) is reached by real specifications · mechanised Byzantine version (8.8) ·
mechanising 8.1's abstraction against a concrete language (e.g. Hydro).
