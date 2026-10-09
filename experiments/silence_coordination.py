#!/usr/bin/env python3
"""Reproducible, abstract workload experiment for silence commitments."""

from __future__ import annotations

import argparse
import csv
import hashlib
import itertools
import json
import math
import random
import statistics
from pathlib import Path
from typing import Any


FAMILIES = ("escrow", "total-order", "unique-choice", "synthetic")
PROTOCOLS = ("minimum", "overcommit", "undercommit")
LOCAL_SERVICE_MS = 0.1


def parse_csv(value: str, cast: Any) -> list[Any]:
    try:
        return [cast(item.strip()) for item in value.split(",") if item.strip()]
    except ValueError as error:
        raise argparse.ArgumentTypeError(str(error)) from error


def stable_seed(*parts: object) -> int:
    payload = "|".join(map(str, parts)).encode()
    return int.from_bytes(hashlib.blake2b(payload, digest_size=8).digest(), "big")


def exact_hitting_set(edges: list[int], participants: int) -> int:
    """Return an exact minimum hitting-set mask; intended for small instances."""
    if not edges:
        return 0
    for size in range(participants + 1):
        for selected in itertools.combinations(range(participants), size):
            mask = sum(1 << node for node in selected)
            if all(mask & edge for edge in edges):
                return mask
    raise AssertionError("all participants must hit every nonempty edge")


def minimal_edges(edges: list[int]) -> list[int]:
    ordered = sorted(set(edges), key=lambda edge: (edge.bit_count(), edge))
    minimal: list[int] = []
    for edge in ordered:
        if not any(existing & edge == existing for existing in minimal):
            minimal.append(edge)
    return minimal


def make_case(
    family: str,
    participants: int,
    open_fraction: float,
    coalition_size: int,
    edge_count: int,
    overlap: float,
    rng: random.Random,
) -> dict[str, Any]:
    open_nodes = [node for node in range(participants) if rng.random() < open_fraction]
    if open_fraction > 0 and not open_nodes:
        open_nodes = [rng.randrange(participants)]
    demands: list[int] = []
    capacity: int | None = None

    if family in ("total-order", "unique-choice"):
        edges = [1 << node for node in open_nodes]
    elif family == "escrow":
        demands = [rng.randint(1, 3) if node in open_nodes else 0 for node in range(participants)]
        total = sum(demands)
        capacity = rng.randint(0, total - 1) if total > 1 else 0
        candidates = []
        for mask in range(1, 1 << participants):
            amount = sum(demands[node] for node in range(participants) if mask & (1 << node))
            if amount <= capacity:
                continue
            if all(
                sum(
                    demands[member]
                    for member in range(participants)
                    if mask & (1 << member) and member != node
                )
                <= capacity
                for node in range(participants)
                if mask & (1 << node)
            ):
                candidates.append(mask)
        edges = candidates
    else:
        size = min(coalition_size, len(open_nodes))
        if size == 0:
            edges = []
        else:
            shared_count = min(size, round((size - 1) * overlap))
            shared = rng.sample(open_nodes, shared_count)
            pool = [node for node in open_nodes if node not in shared]
            candidates = set()
            attempts = max(edge_count * 20, 20)
            while len(candidates) < edge_count and attempts:
                attempts -= 1
                edge_nodes = set(shared)
                edge_nodes.update(rng.sample(pool, size - shared_count))
                candidates.add(sum(1 << node for node in edge_nodes))
            edges = list(candidates)

    edges = minimal_edges(edges)
    optimum = exact_hitting_set(edges, participants)
    return {
        "open_nodes": open_nodes,
        "edges": edges,
        "minimum_mask": optimum,
        "demands": demands,
        "capacity": capacity,
    }


def policy_mask(policy: str, minimum_mask: int, open_nodes: list[int], n: int) -> int:
    if policy == "minimum":
        return minimum_mask
    selected = [node for node in range(n) if minimum_mask & (1 << node)]
    if policy == "undercommit":
        return sum(1 << node for node in selected[:-1]) if selected else 0
    if policy == "overcommit":
        extras = max(1, math.ceil(n * 0.2))
        available = [node for node in open_nodes if node not in selected]
        return minimum_mask | sum(1 << node for node in available[:extras])
    raise ValueError(f"unknown policy: {policy}")


def is_safe(selected_mask: int, edges: list[int]) -> bool:
    return all(selected_mask & edge for edge in edges)


def connected_majority(delivered: list[list[bool]], n: int) -> bool:
    """Whether a majority forms a fully exchanging quorum during one round."""
    quorum_size = n // 2 + 1
    return any(
        all(delivered[a][b] and delivered[b][a] for a, b in itertools.combinations(group, 2))
        for group in itertools.combinations(range(n), quorum_size)
    )


def agreement_cost(
    n: int,
    start_ms: float,
    network: dict[str, float | int],
    rng: random.Random,
) -> tuple[int, int, float, bool]:
    """Toy all-to-all majority agreement with retries and a healing partition."""
    timeout = float(network["timeout_ms"])
    max_rounds = int(network["max_rounds"])
    partition_duration = float(network["partition_duration_ms"])
    partition_fraction = float(network["partition_fraction"])
    nodes = list(range(n))
    rng.shuffle(nodes)
    has_partition = n > 1 and 0 < partition_fraction < 1
    split = max(1, min(n - 1, round(n * partition_fraction))) if has_partition else n
    side = {node: int(node in nodes[split:]) for node in nodes}

    for round_number in range(1, max_rounds + 1):
        elapsed = round_number * timeout
        healed = elapsed >= partition_duration
        delivered = [[False] * n for _ in range(n)]
        for source in range(n):
            delivered[source][source] = True
            for target in range(n):
                if source == target:
                    continue
                if not healed and side[source] != side[target]:
                    continue
                if rng.random() < float(network["loss_rate"]):
                    continue
                delay = float(network["latency_ms"]) + rng.random() * float(network["jitter_ms"])
                delivered[source][target] = delay <= timeout
        if connected_majority(delivered, n):
            return round_number, n * (n - 1) * round_number, start_ms + elapsed, True
    elapsed = max_rounds * timeout
    return max_rounds, n * (n - 1) * max_rounds, start_ms + elapsed, False


def escrow_preallocation(case: dict[str, Any], n: int) -> dict[str, int | bool]:
    """Serve unit requests against fixed shares; distinguish avoidable refusals."""
    demands = case["demands"]
    capacity = int(case["capacity"] or 0)
    shares = [capacity // n] * n
    for node in range(capacity % n):
        shares[node] += 1
    local_left = shares[:]
    global_left = capacity
    approved = 0
    avoidable_refusals = 0
    total_refusals = 0
    for node, demand in enumerate(demands):
        for _ in range(demand):
            if local_left[node] > 0 and global_left > 0:
                local_left[node] -= 1
                global_left -= 1
                approved += 1
            else:
                total_refusals += 1
                if global_left > 0:
                    avoidable_refusals += 1
    return {
        "safe": approved <= capacity,
        "approved_units": approved,
        "avoidable_refusals": avoidable_refusals,
        "total_refusals": total_refusals,
    }


def percentile95(values: list[float]) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    return ordered[max(0, math.ceil(0.95 * len(ordered)) - 1)]


def run_policy(
    policy: str,
    cases: list[dict[str, Any]],
    arrivals: list[float],
    n: int,
    family: str,
    network: dict[str, float | int],
    seed: int,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    availability_ms = 0.0
    records: list[dict[str, Any]] = []
    agreement_rng = random.Random(seed)
    for index, (case, arrival) in enumerate(zip(cases, arrivals)):
        if policy == "escrow_preallocated":
            selected = 0
            safe = True
        else:
            selected = policy_mask(policy, case["minimum_mask"], case["open_nodes"], n)
            safe = is_safe(selected, case["edges"])
        commitments = selected.bit_count()
        start = max(arrival * 1000, availability_ms)
        if commitments:
            rounds, messages, completed_at, finalized = agreement_cost(n, start, network, agreement_rng)
        else:
            rounds, messages = 0, 0
            completed_at, finalized = start + LOCAL_SERVICE_MS, True
        availability_ms = completed_at
        escrow_metrics: dict[str, Any] = {}
        if family == "escrow" and policy == "escrow_preallocated":
            escrow_metrics = escrow_preallocation(case, n)
            safe = bool(escrow_metrics["safe"])
        records.append(
            {
                "decision": index,
                "arrival_ms": round(arrival * 1000, 3),
                "minimum_commitments": case["minimum_mask"].bit_count(),
                "commitments": commitments,
                "safe": safe,
                "finalized": finalized,
                "rounds": rounds,
                "messages": messages,
                "latency_ms": round(completed_at - arrival * 1000, 3),
                "completion_ms": round(completed_at, 3),
                **escrow_metrics,
            }
        )
    span_seconds = max(
        0.001,
        (max(record["completion_ms"] for record in records) - arrivals[0] * 1000) / 1000,
    )
    successful = sum(record["finalized"] for record in records)
    summary = {
        "decisions": len(records),
        "unsafe_decisions": sum(not record["safe"] for record in records),
        "failed_finalizations": len(records) - successful,
        "commitments": statistics.mean(record["commitments"] for record in records),
        "minimum_commitments": statistics.mean(record["minimum_commitments"] for record in records),
        "rounds": statistics.mean(record["rounds"] for record in records),
        "messages": statistics.mean(record["messages"] for record in records),
        "latency_ms_mean": statistics.mean(record["latency_ms"] for record in records),
        "latency_ms_p95": percentile95([record["latency_ms"] for record in records]),
        "throughput_per_second": successful / span_seconds,
        "avoidable_refusals": sum(record.get("avoidable_refusals", 0) for record in records),
        "total_refusals": sum(record.get("total_refusals", 0) for record in records),
    }
    return records, summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("experiment-output"))
    parser.add_argument("--seed", type=int, default=20261009)
    parser.add_argument("--participants", default="3,5")
    parser.add_argument("--families", default=",".join(FAMILIES))
    parser.add_argument("--trials", type=int, default=3)
    parser.add_argument("--decisions", type=int, default=100)
    parser.add_argument("--arrival-rates", default="20,100", help="comma-separated decisions/second")
    parser.add_argument("--open-fraction", type=float, default=1.0)
    parser.add_argument("--coalition-size", type=int, default=2)
    parser.add_argument("--edge-count", type=int, default=8)
    parser.add_argument("--overlaps", default="0,0.75", help="comma-separated shared-core fractions")
    parser.add_argument("--latency-ms", type=float, default=10.0)
    parser.add_argument("--jitter-ms", type=float, default=5.0)
    parser.add_argument("--timeout-ms", type=float, default=30.0)
    parser.add_argument("--loss-rates", default="0,0.02")
    parser.add_argument("--partition-fraction", type=float, default=0.5)
    parser.add_argument("--partition-durations-ms", default="0,150")
    parser.add_argument("--max-rounds", type=int, default=8)
    args = parser.parse_args()

    participants_values = parse_csv(args.participants, int)
    families = parse_csv(args.families, str)
    arrival_rates = parse_csv(args.arrival_rates, float)
    overlaps = parse_csv(args.overlaps, float)
    loss_rates = parse_csv(args.loss_rates, float)
    partition_durations = parse_csv(args.partition_durations_ms, float)
    if not participants_values or any(n < 1 or n > 20 for n in participants_values):
        parser.error("--participants values must be between 1 and 20 (exact search)")
    if not families or any(family not in FAMILIES for family in families):
        parser.error(f"--families must be selected from {', '.join(FAMILIES)}")
    if args.trials < 1 or args.decisions < 1 or args.arrival_rates == "":
        parser.error("--trials and --decisions must be positive")
    if any(rate <= 0 for rate in arrival_rates) or any(not 0 <= x <= 1 for x in overlaps + loss_rates):
        parser.error("arrival rates must be positive; overlap and loss rates must be in [0, 1]")
    if not 0 <= args.open_fraction <= 1:
        parser.error("--open-fraction must be in [0, 1]")
    if args.coalition_size < 1 or args.edge_count < 1 or args.max_rounds < 1:
        parser.error("coalition size, edge count, and max rounds must be positive")
    if min(args.latency_ms, args.jitter_ms, args.timeout_ms, args.partition_fraction, *partition_durations) < 0:
        parser.error("network parameters cannot be negative")
    if args.timeout_ms <= 0 or not 0 <= args.partition_fraction <= 1:
        parser.error("timeout must be positive and partition fraction must be in [0, 1]")

    args.output.mkdir(parents=True, exist_ok=True)
    trace_path = args.output / "traces.jsonl"
    summary_path = args.output / "summary.csv"
    summary_rows: list[dict[str, Any]] = []
    trace_fields = [
        "seed", "family", "participants", "trial", "protocol", "arrival_rate",
        "overlap", "loss_rate", "partition_duration_ms", "decision", "open_nodes",
        "minimal_invalidating_coalitions", "minimum_commitments", "commitments",
        "safe", "finalized", "rounds", "messages", "arrival_ms", "completion_ms",
        "latency_ms", "approved_units", "avoidable_refusals", "total_refusals",
    ]

    with trace_path.open("w", encoding="utf-8") as trace_file:
        for n, family, arrival_rate, overlap, loss_rate, partition_duration in itertools.product(
            participants_values, families, arrival_rates, overlaps, loss_rates, partition_durations
        ):
            for trial in range(args.trials):
                case_seed = stable_seed(args.seed, n, family, trial, arrival_rate, overlap, loss_rate, partition_duration)
                case_rng = random.Random(case_seed)
                cases = [
                    make_case(
                        family, n, args.open_fraction, args.coalition_size, args.edge_count, overlap, case_rng
                    )
                    for _ in range(args.decisions)
                ]
                arrivals = []
                elapsed = 0.0
                for _ in cases:
                    elapsed += case_rng.expovariate(arrival_rate)
                    arrivals.append(elapsed)
                network: dict[str, float | int] = {
                    "latency_ms": args.latency_ms,
                    "jitter_ms": args.jitter_ms,
                    "timeout_ms": args.timeout_ms,
                    "loss_rate": loss_rate,
                    "partition_fraction": args.partition_fraction,
                    "partition_duration_ms": partition_duration,
                    "max_rounds": args.max_rounds,
                }
                protocols = list(PROTOCOLS) + (["escrow_preallocated"] if family == "escrow" else [])
                for protocol_index, protocol in enumerate(protocols):
                    records, metrics = run_policy(
                        protocol,
                        cases,
                        arrivals,
                        n,
                        family,
                        network,
                        stable_seed(case_seed, protocol_index),
                    )
                    summary_rows.append(
                        {
                            "seed": case_seed,
                            "family": family,
                            "participants": n,
                            "trial": trial,
                            "protocol": protocol,
                            "arrival_rate": arrival_rate,
                            "overlap": overlap,
                            "loss_rate": loss_rate,
                            "partition_duration_ms": partition_duration,
                            **metrics,
                        }
                    )
                    for case, record in zip(cases, records):
                        trace_file.write(
                            json.dumps(
                                {
                                    "seed": case_seed,
                                    "family": family,
                                    "participants": n,
                                    "trial": trial,
                                    "protocol": protocol,
                                    "arrival_rate": arrival_rate,
                                    "overlap": overlap,
                                    "loss_rate": loss_rate,
                                    "partition_duration_ms": partition_duration,
                                    "open_nodes": case["open_nodes"],
                                    "minimal_invalidating_coalitions": [
                                        [node for node in range(n) if edge & (1 << node)]
                                        for edge in case["edges"]
                                    ],
                                    **record,
                                },
                                sort_keys=True,
                            )
                            + "\n"
                        )

    with summary_path.open("w", newline="", encoding="utf-8") as summary_file:
        writer = csv.DictWriter(summary_file, fieldnames=list(summary_rows[0]))
        writer.writeheader()
        writer.writerows(summary_rows)
    print(f"Wrote {len(summary_rows)} trial summaries and {len(summary_rows) * args.decisions} traces.")
    print(f"Summary: {summary_path.resolve()}")
    print(f"Traces:  {trace_path.resolve()}")


if __name__ == "__main__":
    main()
