#!/usr/bin/env python3
"""Generate small-n lower-bound candidate-cycle data.

This stays strictly on the SmallN side. The current focus is `n = 5`:

- enumerate canonical-start simple good cycles for a fixed exact profile
- keep only cycles where every processor fires at least once
- summarize counts by profile and cycle length

The search rules match the existing SmallN exploration scripts:

- one processor moves per step
- the next mover must be adjacent to the previous mover
- determined transition entries must remain locally consistent
- the closed path must have unique privilege at every good configuration
- canonical-start pruning keeps only cycles whose start is lexicographically
  minimal along the cycle
The script now also supports the normalization pipeline described in
`LeanMn/SmallN/M56_CLOSURE_PLAN_2026-04-14.md`:

1. cycle rotation
2. cycle reversal
3. ring rotation
4. per-processor first-seen relabeling
5. determined-entry table serialization

This lets us compare the raw canonical-start cycle census with the much smaller
residual candidate census that is expected to feed the eventual Lean proof.
"""

from __future__ import annotations

import argparse
import json
import time
from collections import Counter
from dataclasses import dataclass
from itertools import product
from typing import Dict, Iterable, List, Mapping, Sequence, Tuple


Config = Tuple[int, ...]
Determined = Dict[Tuple[int, int, int, int], int]


@dataclass(frozen=True)
class CycleRecord:
    profile: Tuple[int, ...]
    configs: Tuple[Config, ...]
    movers: Tuple[int, ...]


SerializedEntry = Tuple[int, int, int, int, int]
SerializedRecord = Tuple[
    Tuple[int, ...],
    Tuple[Config, ...],
    Tuple[int, ...],
]
SerializedDetermined = Tuple[SerializedEntry, ...]


@dataclass(frozen=True)
class NormalizationResult:
    cycle_normalized: CycleRecord
    ring_normalized: CycleRecord
    relabeled: CycleRecord
    determined: SerializedDetermined


@dataclass(frozen=True)
class BlockerSummary:
    blocked: bool
    kernel_nonempty: bool
    kernel_size: int
    scc_count: int
    largest_scc_size: int
    shortest_bad_cycle_length: int | None
    non_good_count: int
    determined_entry_count: int


N5_TAIL_PROFILES: List[Tuple[int, ...]] = [
    (2, 2, 2, 3, 3),
    (2, 2, 3, 2, 3),
]


def neighbors(n: int, i: int) -> Tuple[int, int]:
    return ((i - 1) % n, (i + 1) % n)


def rotate_left(seq: Sequence[int] | Tuple[int, ...], amount: int) -> Tuple[int, ...]:
    seq_t = tuple(seq)
    if not seq_t:
        return ()
    amount %= len(seq_t)
    return seq_t[amount:] + seq_t[:amount]


def mover_step_sign(a: int, b: int, n: int) -> int:
    if b == a:
        return 0
    if b == (a + 1) % n:
        return 1
    if b == (a - 1) % n:
        return -1
    raise ValueError(f"non-adjacent mover transition {a}->{b} on C_{n}")


def single_step_data(config: Config, proc: int, new_val: int) -> Tuple[Tuple[int, int, int, int], int]:
    left, right = neighbors(len(config), proc)
    return (proc, config[left], config[proc], config[right]), new_val


def privilege_set(config: Config, n: int, det: Determined) -> List[int]:
    priv = []
    for i in range(n):
        left, right = neighbors(n, i)
        key = (i, config[left], config[i], config[right])
        if key in det and det[key] != config[i]:
            priv.append(i)
    return priv


def extend_determined(config: Config, proc: int, new_val: int, det: Determined) -> Determined | None:
    new_det = dict(det)

    mover_key, mover_out = single_step_data(config, proc, new_val)
    prev = new_det.get(mover_key)
    if prev is not None and prev != mover_out:
        return None
    new_det[mover_key] = mover_out

    n = len(config)
    for i in range(n):
        if i == proc:
            continue
        left, right = neighbors(n, i)
        key = (i, config[left], config[i], config[right])
        prev = new_det.get(key)
        if prev is not None and prev != config[i]:
            return None
        new_det[key] = config[i]

    return new_det


def serialize_record(record: CycleRecord) -> SerializedRecord:
    return (record.profile, record.configs, record.movers)


def serialize_determined(det: Mapping[Tuple[int, int, int, int], int]) -> SerializedDetermined:
    return tuple(sorted((proc, left, state, right, out) for (proc, left, state, right), out in det.items()))


def cyclic_sign_runs(signs: Sequence[int]) -> int:
    nonzero = [sign for sign in signs if sign != 0]
    if not nonzero:
        return 0
    runs = 1
    for prev, cur in zip(nonzero, nonzero[1:]):
        if prev != cur:
            runs += 1
    if len(nonzero) > 1 and nonzero[0] == nonzero[-1] and runs > 1:
        runs -= 1
    return runs


def mover_word_stats(record: CycleRecord) -> Dict[str, int | str]:
    n = len(record.profile)
    cyclic_movers = record.movers[1:] + record.movers[:1]
    signs = [mover_step_sign(a, b, n) for a, b in zip(record.movers, cyclic_movers)]
    nonzero_signs = [sign for sign in signs if sign != 0]
    nonzero_total = sum(nonzero_signs)
    if nonzero_total % n != 0:
        winding = 0
        winding_kind = "nonintegral"
    else:
        winding = nonzero_total // n
        winding_kind = "integral"
    runs = cyclic_sign_runs(nonzero_signs)
    reversals = max(0, runs - 1) if nonzero_signs else 0
    if winding_kind == "integral" and abs(winding) >= 2:
        kind = "sweep"
    elif winding_kind == "integral" and abs(winding) == 1:
        kind = "odd_winding"
    elif winding_kind == "integral" and winding == 0 and runs == 2:
        kind = "baf"
    elif winding_kind == "integral" and winding == 0 and runs >= 4:
        kind = "wiggle"
    else:
        kind = "other"
    return {
        "winding": winding,
        "winding_kind": winding_kind,
        "direction_runs": runs,
        "reversals": reversals,
        "self_steps": sum(1 for sign in signs if sign == 0),
        "nonself_steps": len(nonzero_signs),
        "kind": kind,
    }


def reverse_cycle_record(record: CycleRecord) -> CycleRecord:
    if not record.configs:
        return record
    return CycleRecord(
        profile=record.profile,
        configs=(record.configs[0],) + tuple(reversed(record.configs[1:])),
        movers=tuple(reversed(record.movers)),
    )


def rotate_cycle_record(record: CycleRecord, amount: int) -> CycleRecord:
    return CycleRecord(
        profile=record.profile,
        configs=rotate_left(record.configs, amount),
        movers=rotate_left(record.movers, amount),
    )


def canonicalize_cycle_presentation(record: CycleRecord) -> CycleRecord:
    candidates = [rotate_cycle_record(record, amount) for amount in range(len(record.configs))]
    return min(candidates, key=serialize_record)


def cycle_rotation_reversal_key(record: CycleRecord) -> SerializedRecord:
    candidates: List[CycleRecord] = []
    for base in (record, reverse_cycle_record(record)):
        for amount in range(len(base.configs)):
            candidates.append(rotate_cycle_record(base, amount))
    return serialize_record(min(candidates, key=serialize_record))


def rotate_processor_record(record: CycleRecord, amount: int) -> CycleRecord:
    n = len(record.profile)
    return CycleRecord(
        profile=rotate_left(record.profile, amount),
        configs=tuple(rotate_left(config, amount) for config in record.configs),
        movers=tuple((mover - amount) % n for mover in record.movers),
    )


def canonicalize_ring_rotation(record: CycleRecord) -> CycleRecord:
    candidates = [rotate_processor_record(record, amount) for amount in range(len(record.profile))]
    return min(candidates, key=serialize_record)


def first_seen_relabelings(record: CycleRecord) -> Tuple[Dict[int, int], ...]:
    relabelings: List[Dict[int, int]] = []
    for proc, state_count in enumerate(record.profile):
        order: List[int] = []
        seen: set[int] = set()
        for config in record.configs:
            state = config[proc]
            if state not in seen:
                seen.add(state)
                order.append(state)
        for state in range(state_count):
            if state not in seen:
                order.append(state)
        relabelings.append({state: idx for idx, state in enumerate(order)})
    return tuple(relabelings)


def relabel_cycle_record(record: CycleRecord) -> CycleRecord:
    relabelings = first_seen_relabelings(record)
    configs = tuple(
        tuple(relabelings[proc][config[proc]] for proc in range(len(config)))
        for config in record.configs
    )
    return CycleRecord(profile=record.profile, configs=configs, movers=record.movers)


def determined_entries_from_record(record: CycleRecord) -> Determined:
    det: Determined = {}
    for idx, config in enumerate(record.configs):
        proc = record.movers[idx]
        next_cfg = record.configs[(idx + 1) % len(record.configs)]
        new_det = extend_determined(config, proc, next_cfg[proc], det)
        if new_det is None:
            raise ValueError(f"normalized record has inconsistent determined entries: {record}")
        det = new_det
    return det


def normalize_record(record: CycleRecord) -> NormalizationResult:
    cycle_normalized = canonicalize_cycle_presentation(record)
    ring_normalized = canonicalize_ring_rotation(cycle_normalized)
    relabeled = relabel_cycle_record(ring_normalized)
    determined = serialize_determined(determined_entries_from_record(relabeled))
    return NormalizationResult(
        cycle_normalized=cycle_normalized,
        ring_normalized=ring_normalized,
        relabeled=relabeled,
        determined=determined,
    )


def normalization_summary(records: Iterable[CycleRecord]) -> Dict[str, object]:
    records = list(records)
    cycle_keys = set()
    ring_keys = set()
    relabeled_keys = set()
    post_relabel_cycle_keys = set()
    determined_keys = set()
    determined_length_map: Dict[Tuple[Tuple[int, ...], SerializedDetermined], int] = {}
    determined_length_counts: Counter[int] = Counter()
    post_relabel_type_counts: Counter[str] = Counter()
    post_relabel_unique_type_keys: Dict[SerializedRecord, str] = {}

    for record in records:
        cycle_keys.add(cycle_rotation_reversal_key(record))
        normalized = normalize_record(record)
        ring_keys.add(serialize_record(normalized.ring_normalized))
        relabeled_keys.add(serialize_record(normalized.relabeled))
        recanon_key = cycle_rotation_reversal_key(normalized.relabeled)
        post_relabel_cycle_keys.add(recanon_key)
        final_key = (normalized.relabeled.profile, normalized.determined)
        determined_keys.add(final_key)
        determined_length_map.setdefault(final_key, len(normalized.relabeled.configs))
        kind = mover_word_stats(normalized.relabeled)["kind"]
        post_relabel_type_counts[kind] += 1
        post_relabel_unique_type_keys.setdefault(recanon_key, kind)

    for key in determined_keys:
        determined_length_counts[determined_length_map[key]] += 1

    return {
        "raw_count": len(records),
        "cycle_rotation_reversal_count": len(cycle_keys),
        "ring_rotation_count": len(ring_keys),
        "first_seen_relabel_count": len(relabeled_keys),
        "post_relabel_cycle_rotation_reversal_count": len(post_relabel_cycle_keys),
        "determined_table_count": len(determined_keys),
        "raw_lengths": dict(sorted(Counter(len(r.configs) for r in records).items())),
        "normalized_lengths": dict(sorted(determined_length_counts.items())),
        "post_relabel_type_counts": dict(sorted(post_relabel_type_counts.items())),
        "post_relabel_unique_type_counts": dict(
            sorted(Counter(post_relabel_unique_type_keys.values()).items())
        ),
    }


def full_mask(size: int) -> int:
    return (1 << size) - 1


def sink_kernel_mask(size: int, succ_masks: Sequence[int]) -> int:
    remaining = full_mask(size)
    for _ in range(size):
        sinks = 0
        for v in range(size):
            if ((remaining >> v) & 1) == 0:
                continue
            if succ_masks[v] & remaining == 0:
                sinks |= 1 << v
        if sinks == 0:
            return remaining
        remaining &= full_mask(size) ^ sinks
    return remaining


def tarjan_sccs_on_mask(size: int, succ_masks: Sequence[int], active_mask: int) -> List[List[int]]:
    index = 0
    stack: List[int] = []
    on_stack: set[int] = set()
    indices: Dict[int, int] = {}
    lowlink: Dict[int, int] = {}
    sccs: List[List[int]] = []

    def strongconnect(v: int) -> None:
        nonlocal index
        indices[v] = index
        lowlink[v] = index
        index += 1
        stack.append(v)
        on_stack.add(v)

        succ_mask = succ_masks[v] & active_mask
        for w in range(size):
            if ((succ_mask >> w) & 1) == 0:
                continue
            if w not in indices:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], indices[w])

        if lowlink[v] == indices[v]:
            scc: List[int] = []
            while True:
                w = stack.pop()
                on_stack.remove(w)
                scc.append(w)
                if w == v:
                    break
            if len(scc) > 1 or (succ_masks[v] & active_mask & (1 << v)) != 0:
                sccs.append(scc)

    for v in range(size):
        if ((active_mask >> v) & 1) == 0:
            continue
        if v not in indices:
            strongconnect(v)
    return sccs


def shortest_directed_cycle_length(size: int, succ_masks: Sequence[int], active_mask: int) -> int | None:
    best: int | None = None
    for start in range(size):
        if ((active_mask >> start) & 1) == 0:
            continue
        queue: List[Tuple[int, int]] = [(start, 0)]
        seen = {start}
        head = 0
        while head < len(queue):
            v, dist = queue[head]
            head += 1
            succ_mask = succ_masks[v] & active_mask
            for w in range(size):
                if ((succ_mask >> w) & 1) == 0:
                    continue
                if w == start:
                    cycle_len = dist + 1
                    if best is None or cycle_len < best:
                        best = cycle_len
                    continue
                if w not in seen:
                    seen.add(w)
                    queue.append((w, dist + 1))
        if best == 1:
            return best
    return best


def blocker_summary_for_record(record: CycleRecord) -> BlockerSummary:
    det = determined_entries_from_record(record)
    profile = record.profile
    all_configs = list(product(*[range(m) for m in profile]))
    good_set = set(record.configs)
    non_good = [cfg for cfg in all_configs if cfg not in good_set]
    index = {cfg: i for i, cfg in enumerate(non_good)}
    succ_masks = [0] * len(non_good)

    for cfg in non_good:
        src = index[cfg]
        mask = 0
        for proc in range(len(profile)):
            left, right = neighbors(len(profile), proc)
            key = (proc, cfg[left], cfg[proc], cfg[right])
            if key in det and det[key] != cfg[proc]:
                nxt = list(cfg)
                nxt[proc] = det[key]
                nxt_t = tuple(nxt)
                if nxt_t in index:
                    mask |= 1 << index[nxt_t]
        succ_masks[src] = mask

    kernel_mask = sink_kernel_mask(len(non_good), succ_masks)
    kernel_size = kernel_mask.bit_count()
    sccs = tarjan_sccs_on_mask(len(non_good), succ_masks, kernel_mask) if kernel_size else []
    largest_scc_size = max((len(scc) for scc in sccs), default=0)
    shortest = shortest_directed_cycle_length(len(non_good), succ_masks, kernel_mask) if kernel_size else None
    return BlockerSummary(
        blocked=kernel_size > 0,
        kernel_nonempty=kernel_size > 0,
        kernel_size=kernel_size,
        scc_count=len(sccs),
        largest_scc_size=largest_scc_size,
        shortest_bad_cycle_length=shortest,
        non_good_count=len(non_good),
        determined_entry_count=len(det),
    )


def blocker_summary(records: Iterable[CycleRecord]) -> Dict[str, object]:
    normalized: Dict[Tuple[Tuple[int, ...], SerializedDetermined], CycleRecord] = {}
    for record in records:
        norm = normalize_record(record)
        key = (norm.relabeled.profile, norm.determined)
        normalized.setdefault(key, norm.relabeled)

    summaries = [blocker_summary_for_record(record) for record in normalized.values()]
    shortest_counter = Counter(
        summary.shortest_bad_cycle_length for summary in summaries if summary.shortest_bad_cycle_length is not None
    )
    return {
        "candidate_count": len(summaries),
        "blocked_count": sum(1 for summary in summaries if summary.blocked),
        "kernel_size_distribution": dict(sorted(Counter(summary.kernel_size for summary in summaries).items())),
        "largest_scc_distribution": dict(sorted(Counter(summary.largest_scc_size for summary in summaries).items())),
        "shortest_bad_cycle_distribution": dict(sorted(shortest_counter.items())),
    }


def lean_nat_list(xs: Sequence[int]) -> str:
    return "[" + ", ".join(str(x) for x in xs) + "]"


def lean_nat_array(xs: Sequence[int]) -> str:
    return "#[" + ", ".join(str(x) for x in xs) + "]"


def lean_nat_matrix(xss: Sequence[Sequence[int]]) -> str:
    return "#[" + ", ".join(lean_nat_array(xs) for xs in xss) + "]"


def lean_profile_tag(profile: Sequence[int]) -> str:
    profile_t = tuple(profile)
    mapping = {
        (2, 2, 2, 3, 3): ".tailA",
        (2, 2, 3, 2, 3): ".tailB",
    }
    if profile_t not in mapping:
        raise ValueError(f"no N5ProfileTag mapping for profile {profile_t}")
    return mapping[profile_t]


def emit_lean_n5_tail_candidates(records: Iterable[CycleRecord]) -> str:
    normalized = normalized_records(records)
    lines = [
        "import LeanMn.SmallN.LowerBound.N5Check",
        "",
        "namespace LeanMn.SmallN.LowerBound",
        "",
        "set_option maxHeartbeats 0 in",
        "set_option maxRecDepth 1000000 in",
        "/-- Generated from `gen_smalln_lower_bound.py --n5-tail-summary --emit-lean-tail-candidates`. -/",
        "def n5TailCandidates : Array N5TailCandidate :=",
        "  #[",
    ]
    for record in normalized:
        lines.append("    {")
        lines.append(f"      profile := {lean_profile_tag(record['profile'])}")
        lines.append(f"      configs := {lean_nat_matrix(record['configs'])}")
        lines.append(f"      movers := {lean_nat_array(record['movers'])}")
        lines.append("    },")
    lines.extend([
        "  ]",
        "",
        "end LeanMn.SmallN.LowerBound",
    ])
    return "\n".join(lines)


def normalized_records(records: Iterable[CycleRecord]) -> List[Dict[str, object]]:
    keep: Dict[Tuple[Tuple[int, ...], SerializedDetermined], CycleRecord] = {}
    for record in records:
        normalized = normalize_record(record)
        key = (normalized.relabeled.profile, normalized.determined)
        keep.setdefault(key, normalized.relabeled)

    payload: List[Dict[str, object]] = []
    for profile, determined in sorted(keep, key=lambda item: (item[0], item[1])):
        relabeled = keep[(profile, determined)]
        block = blocker_summary_for_record(relabeled)
        payload.append(
            {
                "profile": profile,
                "configs": relabeled.configs,
                "movers": relabeled.movers,
                "determined": determined,
                "topology": mover_word_stats(relabeled),
                "blocker": {
                    "blocked": block.blocked,
                    "kernel_nonempty": block.kernel_nonempty,
                    "kernel_size": block.kernel_size,
                    "scc_count": block.scc_count,
                    "largest_scc_size": block.largest_scc_size,
                    "shortest_bad_cycle_length": block.shortest_bad_cycle_length,
                    "non_good_count": block.non_good_count,
                    "determined_entry_count": block.determined_entry_count,
                },
            }
        )
    return payload


def enumerate_canonical_start_cycles(
    profile: Sequence[int],
    *,
    max_path_len: int | None = None,
    require_full_processor_support: bool = True,
) -> List[CycleRecord]:
    n = len(profile)
    if max_path_len is None:
        max_path_len = 5 * n

    all_configs = list(product(*[range(m) for m in profile]))
    results: List[CycleRecord] = []

    for start in sorted(all_configs):
        stack: List[Tuple[Config, List[Config], set[Config], Determined, List[int]]] = [
            (start, [start], {start}, {}, [])
        ]

        while stack:
            config, path, path_set, det, movers = stack.pop()

            for proc in range(n):
                if movers:
                    last = movers[-1]
                    diff = min(abs(proc - last), n - abs(proc - last))
                    if diff > 1:
                        continue

                for new_val in range(profile[proc]):
                    if new_val == config[proc]:
                        continue

                    new_det = extend_determined(config, proc, new_val, det)
                    if new_det is None:
                        continue

                    next_cfg = list(config)
                    next_cfg[proc] = new_val
                    next_cfg_t = tuple(next_cfg)

                    if next_cfg_t == start and len(path) >= n:
                        if require_full_processor_support and set(movers + [proc]) != set(range(n)):
                            continue
                        if any(c < start for c in path[1:]):
                            continue
                        if all(len(privilege_set(c, n, new_det)) == 1 for c in path):
                            results.append(
                                CycleRecord(
                                    profile=tuple(profile),
                                    configs=tuple(path),
                                    movers=tuple(movers + [proc]),
                                )
                            )
                        continue

                    if next_cfg_t in path_set:
                        continue
                    if next_cfg_t < start:
                        continue
                    if len(path) >= max_path_len:
                        continue

                    stack.append(
                        (
                            next_cfg_t,
                            path + [next_cfg_t],
                            path_set | {next_cfg_t},
                            new_det,
                            movers + [proc],
                        )
                    )

    return results


def enumerate_legacy_bounded_cycles(
    profile: Sequence[int],
    *,
    max_cycles: int = 200,
    max_time_sec: float = 120.0,
    max_path_len: int | None = None,
    node_cap_per_start: int = 500_000,
    require_full_processor_support: bool = False,
) -> List[CycleRecord]:
    """Replay the bounded DFS shape used in the old CIC scripts.

    This is intentionally *not* an exact enumerator. It is here only so the
    historical `82` / `164` style counts can be reproduced from inside the
    SmallN workspace without relying on external ad hoc snippets.
    """
    n = len(profile)
    if max_path_len is None:
        max_path_len = 5 * n

    start_time = time.time()
    product_val = 1
    for m in profile:
        product_val *= m
    if product_val > 500:
        return []

    all_configs = list(product(*[range(m) for m in profile]))
    results: List[CycleRecord] = []

    for start_idx in range(min(len(all_configs), product_val)):
        if time.time() - start_time > max_time_sec:
            break
        start = all_configs[start_idx]
        stack: List[Tuple[Config, List[Config], Determined, List[int]]] = [(start, [start], {}, [])]
        nodes = 0

        while stack and nodes < node_cap_per_start:
            if time.time() - start_time > max_time_sec:
                break
            nodes += 1
            config, path, det, movers = stack.pop()
            path_set = set(path)

            for proc in range(n):
                if movers:
                    last = movers[-1]
                    diff = min(abs(proc - last), n - abs(proc - last))
                    if diff > 1:
                        continue

                for new_val in range(profile[proc]):
                    if new_val == config[proc]:
                        continue

                    new_det = extend_determined(config, proc, new_val, det)
                    if new_det is None:
                        continue

                    next_cfg = list(config)
                    next_cfg[proc] = new_val
                    next_cfg_t = tuple(next_cfg)

                    if next_cfg_t == start and len(path) >= n:
                        if require_full_processor_support and set(movers + [proc]) != set(range(n)):
                            continue
                        if all(len(privilege_set(c, n, new_det)) == 1 for c in path):
                            cycle_tup = tuple(path)
                            if cycle_tup not in [record.configs for record in results]:
                                results.append(
                                    CycleRecord(
                                        profile=tuple(profile),
                                        configs=cycle_tup,
                                        movers=tuple(movers + [proc]),
                                    )
                                )
                                if len(results) >= max_cycles:
                                    return results
                        continue

                    if next_cfg_t in path_set or len(path) >= max_path_len:
                        continue

                    stack.append((next_cfg_t, path + [next_cfg_t], new_det, movers + [proc]))

    return results


def summarize(records: Iterable[CycleRecord]) -> Dict[str, object]:
    records = list(records)
    length_counts = Counter(len(r.configs) for r in records)
    return {
        "count": len(records),
        "lengths": dict(sorted(length_counts.items())),
    }


N5_ROTATION_PROFILES: List[Tuple[int, ...]] = [
    (2, 2, 2, 2, 2),
    (2, 2, 2, 2, 3),
    (2, 2, 2, 2, 4),
    (2, 2, 2, 3, 3),
    (2, 2, 3, 2, 3),
    (2, 2, 2, 2, 5),
]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--profile",
        action="append",
        type=str,
        help="Comma-separated exact profile, e.g. 2,2,2,3,3. Pass multiple times to aggregate.",
    )
    parser.add_argument("--max-path-len", type=int, default=None)
    parser.add_argument("--allow-partial", action="store_true")
    parser.add_argument("--n5-summary", action="store_true")
    parser.add_argument("--n5-tail-summary", action="store_true")
    parser.add_argument("--normalized", action="store_true")
    parser.add_argument("--emit-normalized-records", action="store_true")
    parser.add_argument("--analyze-blockers", action="store_true")
    parser.add_argument("--emit-lean-tail-candidates", action="store_true")
    parser.add_argument("--enumerator", choices=["exact", "legacy"], default="exact")
    parser.add_argument("--legacy-max-cycles", type=int, default=200)
    parser.add_argument("--legacy-max-time-sec", type=float, default=120.0)
    parser.add_argument("--legacy-node-cap-per-start", type=int, default=500000)
    parser.add_argument(
        "--legacy-post-filter-full-support",
        action="store_true",
        help="Replay the old CIC pattern: cap legacy DFS first, then filter to full-processor cycles.",
    )
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    if args.n5_summary:
        payload = {}
        for profile in N5_ROTATION_PROFILES:
            if args.enumerator == "exact":
                records = enumerate_canonical_start_cycles(
                    profile,
                    max_path_len=args.max_path_len,
                    require_full_processor_support=not args.allow_partial,
                )
            else:
                records = enumerate_legacy_bounded_cycles(
                    profile,
                    max_cycles=args.legacy_max_cycles,
                    max_time_sec=args.legacy_max_time_sec,
                    max_path_len=args.max_path_len,
                    node_cap_per_start=args.legacy_node_cap_per_start,
                    require_full_processor_support=(not args.allow_partial) and (not args.legacy_post_filter_full_support),
                )
                if args.legacy_post_filter_full_support and not args.allow_partial:
                    records = [record for record in records if set(record.movers) == set(range(len(record.profile)))]
            payload[",".join(map(str, profile))] = summarize(records)
        if args.json:
            print(json.dumps(payload, indent=2, sort_keys=True))
        else:
            for profile, stats in payload.items():
                print(f"{profile}: {stats['count']} cycles  lengths={stats['lengths']}")
        return

    requested_profiles: List[Tuple[int, ...]] = []
    if args.profile:
        requested_profiles.extend(tuple(int(x) for x in text.split(",")) for text in args.profile)
    if args.n5_tail_summary:
        requested_profiles.extend(N5_TAIL_PROFILES)

    if not requested_profiles:
        parser.error("pass --profile/--n5-tail-summary or --n5-summary")

    records: List[CycleRecord] = []
    per_profile_summary: Dict[str, Dict[str, object]] = {}
    for profile in requested_profiles:
        if args.enumerator == "exact":
            profile_records = enumerate_canonical_start_cycles(
                profile,
                max_path_len=args.max_path_len,
                require_full_processor_support=not args.allow_partial,
            )
        else:
            profile_records = enumerate_legacy_bounded_cycles(
                profile,
                max_cycles=args.legacy_max_cycles,
                max_time_sec=args.legacy_max_time_sec,
                max_path_len=args.max_path_len,
                node_cap_per_start=args.legacy_node_cap_per_start,
                require_full_processor_support=(not args.allow_partial) and (not args.legacy_post_filter_full_support),
            )
            if args.legacy_post_filter_full_support and not args.allow_partial:
                profile_records = [
                    record for record in profile_records
                    if set(record.movers) == set(range(len(record.profile)))
                ]
        records.extend(profile_records)
        per_profile_summary[",".join(map(str, profile))] = summarize(profile_records)

    payload = {
        "profiles": requested_profiles,
        "per_profile_summary": per_profile_summary,
        "summary": summarize(records),
    }
    if args.normalized or args.emit_normalized_records:
        payload["normalization"] = normalization_summary(records)
    if args.analyze_blockers:
        payload["blockers"] = blocker_summary(records)
    if args.emit_lean_tail_candidates:
        payload["lean_tail_candidates"] = emit_lean_n5_tail_candidates(records)
    if args.emit_normalized_records:
        payload["normalized_records"] = normalized_records(records)
    else:
        payload["records"] = [
            {
                "profile": record.profile,
                "configs": record.configs,
                "movers": record.movers,
            }
            for record in records
        ]
    if args.json:
        print(json.dumps(payload, indent=2))
    else:
        if "lean_tail_candidates" in payload:
            print(payload["lean_tail_candidates"])
            return
        print(f"profiles={','.join('(' + ','.join(map(str, profile)) + ')' for profile in requested_profiles)}")
        print(f"enumerator={args.enumerator}")
        if args.legacy_post_filter_full_support:
            print("legacy_post_filter_full_support=true")
        print(f"raw={payload['summary']['count']} lengths={payload['summary']['lengths']}")
        if "normalization" in payload:
            norm = payload["normalization"]
            print(
                "normalized="
                f"cycle={norm['cycle_rotation_reversal_count']} "
                f"ring={norm['ring_rotation_count']} "
                f"relabel={norm['first_seen_relabel_count']} "
                f"recanon={norm['post_relabel_cycle_rotation_reversal_count']} "
                f"determined={norm['determined_table_count']}"
            )
            print(f"types_raw={norm['post_relabel_type_counts']}")
            print(f"types_unique={norm['post_relabel_unique_type_counts']}")
        if "blockers" in payload:
            print(f"blockers={payload['blockers']}")


if __name__ == "__main__":
    main()
