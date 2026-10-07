# Counterexamples — where the silence theorems stop (7 October 2026)

Predictions were written before running (see each module's header). TLC 2026.04.18, exhaustive, small models.

| model | setting | prediction | TLC |
|---|---|---|---|
| `CE1_Liar` Liar=FALSE | honest closure (the theorem's setting) | holds | **No error** (62 states) |
| `CE1_Liar` Liar=TRUE | a closes, then acts, differently per replica | breaks | **Agreement violated**: r1 decides "one", r2 "zero" |
| `CE2_Unknown` EpochRule=FALSE | newcomer acts in a scope committed with τ = 0 | breaks | **Safe violated** (9 states) |
| `CE2_Unknown` EpochRule=TRUE | newcomer counts only in later scopes (§8.7) | holds | **No error** |
| `CE3_Guess` | commit while a is open, no silence ("hope") | bad run exists | **Safe violated** (4 states) |
| `CE6_Compensate` Auto=FALSE | mechanism forces b to give back instead of silencing a; b may crash | breaks ⇒ not a safe mechanism ⇒ 2(b) stands | **SafeAtRest violated**: a took, b crashed, net = −1 |
| `CE6_Compensate` Auto=TRUE | compensation is a deterministic rule of every replica | {a} no longer invalidates ⇒ τ = 0, holds with no silence | **No error** (`-deadlock`: terminal states are normal) |

**Reading.** 1–3 break exactly where MINIMAL_SILENCE says the setting ends (lying closure, changing membership, probabilistic
correctness). 6 was the real risk to Theorem 2(b) — "a mechanism that adds an action instead of silencing": forcing another participant
to act is not safe when that participant can crash; making the compensation part of the specification removes the invalidating
coalition, and the theorem then correctly says zero. Small models only; not a proof that no other mechanism shape exists.
