# Silence-coordination experiment

This dependency-free Python harness exercises the per-commitment result in
[`MINIMAL_SILENCE.md`](../MINIMAL_SILENCE.md): a set of silence commitments is
safe exactly when it hits every minimal open coalition that invalidates the
decision. It reports this combinatorial safety result separately from a
small, explicit network-and-load simulation.

## Scope and assumptions

- `escrow` generates bounded-capacity demand instances and their minimal
  over-budget coalitions. `total-order` and `unique-choice` each use singleton
  invalidating coalitions: any open participant may still change the period's
  content. `synthetic` generates fixed-size hyperedges with a configurable
  shared core, giving exact small hitting-set instances with different overlap.
- The exact minimum is found by exhaustive search, so participant counts are
  limited to 20. These generated instances are experiments, not a proof or a
  substitute for the TLA+ models.
- `minimum` chooses an exact minimum hitting set; `overcommit` adds open
  participants beyond it; `undercommit` removes one member from the selected
  minimum set. Safety is computed directly from the theorem's hitting-set
  criterion. The `escrow_preallocated` comparison is a separate policy: it
  splits the capacity before requests and counts safe approvals and refusals
  caused by stranded capacity.
- A nonempty commitment set is charged a toy all-to-all majority-agreement
  service: messages are independently lost or delayed, a static partition can
  heal after a specified duration, and a round succeeds only if some majority
  fully exchanges messages. This is a deliberately simple cost model, not an
  implementation of Paxos, CalmSeal, Vortex, or a validated network simulator.
- Requests arrive according to a Poisson process at the selected rate. Each
  trial serializes its decisions through one agreement service queue. Thus
  latency and throughput are conditional on these assumptions and cannot be
  inferred from the hitting number alone.

## Run

Python 3.10+; no third-party packages:

```bash
python3 experiments/silence_coordination.py \
  --output /tmp/silence-results \
  --seed 20261009 \
  --participants 3,5,8 \
  --trials 10 --decisions 200 \
  --arrival-rates 20,100 \
  --families escrow,total-order,unique-choice,synthetic \
  --coalition-size 3 --edge-count 12 --overlaps 0,0.5,1 \
  --loss-rates 0,0.02 \
  --partition-durations-ms 0,150
```

Each comma-separated option creates a parameter sweep. Large sweeps grow
multiplicatively; begin with small participant and trial counts.

## Output and interpretation

- `summary.csv`: one row per family, protocol, trial, and parameter setting.
  It reports unsafe decisions and failed finalizations separately from mean
  commitments, rounds, messages, latency, throughput, and escrow refusals.
- `traces.jsonl`: one record per decision, including the open participants,
  minimal invalidating coalitions, exact minimum and selected commitments,
  safety/finalization, and per-decision network cost. The `seed` field allows
  each case to be regenerated.

Expected invariant: `minimum` is safe and uses exactly the calculated hitting
number; `undercommit` is unsafe whenever the minimum is positive; extra
commitments do not improve this safety predicate. Availability and performance
may vary with network conditions and load. The experiment checks the harness
and illustrates costs under its assumptions; it does not experimentally prove
the theorem or establish performance claims about a production protocol.
