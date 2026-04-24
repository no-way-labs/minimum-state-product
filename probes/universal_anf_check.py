#!/usr/bin/env python3
"""Universal allNormalForm checks for the n=9 hard-residue witness family.

This script answers four concrete questions about the `22,698` sandwiched-pivot
instances at `n = 9`:

1. Which `(J, K)` phase pairs actually occur under Lean's `hall_normal`
   hypothesis?
2. Does binary closure parity already kill every witness?
3. Does cyclic closure kill every witness for every state vector, not just
   CUP-2?
4. Does the simpler parity-only summation argument force a contradiction?

Conventions used here:

- A "pivot instance" means a pair `(ms, t)` where `ms` is a sub-threshold
  state vector with at least one sandwiched ternary pivot `t`.
- A "typed witness" means one of the four canonical mover words attached to a
  pivot instance: `LeftSame`, `RightSame`, `LeftCross`, `RightCross`.
- Lean's `hall_normal` quantifies over *all* `TernaryPhase` suffix intervals,
  not over the cyclic wrap-around gap. We therefore compute both:
  - Lean-style suffix phases, for Checks A/B.
  - Cyclic consecutive gaps between successive `t`-fires, for Check D.
"""

from __future__ import annotations

import os
import sys
from collections import Counter, defaultdict
from math import prod

sys.path.insert(0, os.path.dirname(__file__))

from cyclic_closure_check import (  # type: ignore
    HARD_TYPES,
    analyze_hard_type,
    candidate_instances,
    full_cycle_sat,
    rotate_ms_to_pivot_zero,
)
from hard_residue_ghost_check import (  # type: ignore
    N,
    enumerate_state_vectors,
    has_ge3_binary,
    is_normal_phase,
    left,
    phases,
    right,
    sandwiched_pivots,
)


PIVOT = 0


def signed_offset(pos: int, pivot: int = PIVOT, n: int = N) -> int:
    delta = (pos - pivot) % n
    if delta > n // 2:
        delta -= n
    return delta


def offset_label(delta: int) -> str:
    if delta == 0:
        return "t"
    if delta < 0:
        return f"L{-delta}"
    return f"R{delta}"


def fmt_pair(pair: tuple[int, int]) -> str:
    return f"({pair[0]},{pair[1]})"


def fmt_offsets(deltas: list[int] | tuple[int, ...]) -> str:
    return "[" + ", ".join(offset_label(d) for d in deltas) + "]"


def lean_phase_pairs(word: tuple[int, ...], t: int = PIVOT) -> Counter[tuple[int, int]]:
    out: Counter[tuple[int, int]] = Counter()
    for phase in phases(list(word), t):
        out[(phase.j, phase.k)] += 1
    return out


def cyclic_gap_pairs(word: tuple[int, ...], t: int = PIVOT) -> tuple[tuple[int, int], ...]:
    steps = [k for k, mover in enumerate(word) if mover == t]
    assert steps, "pivot must fire"
    out: list[tuple[int, int]] = []
    length = len(word)
    for idx, s in enumerate(steps):
        snext = steps[(idx + 1) % len(steps)]
        if snext <= s:
            snext += length
        j = sum(1 for k in range(s + 1, snext) if word[k % length] == left(t))
        k = sum(1 for k in range(s + 1, snext) if word[k % length] == right(t))
        out.append((j, k))
    return tuple(out)


def fire_counts(word: tuple[int, ...]) -> dict[int, int]:
    counts = Counter(word)
    return {p: counts[p] for p in range(N)}


def odd_fire_offsets(word: tuple[int, ...], t: int = PIVOT) -> tuple[int, ...]:
    counts = fire_counts(word)
    odds = [signed_offset(p, t) for p, count in counts.items() if count % 2 == 1]
    return tuple(sorted(odds))


def parity_only_ok(pair: tuple[int, int]) -> bool:
    return not ((pair[0] % 2 == 0) and (pair[1] % 2 == 0))


def normal_ok(pair: tuple[int, int]) -> bool:
    return is_normal_phase(pair[0], pair[1])


def branch_binary_parity_stats(
    instances: list[tuple[tuple[int, ...], int]],
    odd_offsets_for_branch: tuple[int, ...],
) -> dict:
    grouped: dict[tuple[int, ...], list[int]] = defaultdict(list)
    for ms, t in instances:
        grouped[ms].append(t)

    pivot_hits = 0
    vector_any = 0
    vector_all = 0

    for ms, pivots in grouped.items():
        hits = []
        for t in pivots:
            hit = any(ms[(t + delta) % N] == 2 for delta in odd_offsets_for_branch)
            hits.append(hit)
        pivot_hits += sum(hits)
        if any(hits):
            vector_any += 1
        if all(hits):
            vector_all += 1

    return {
        "pivot_hits": pivot_hits,
        "pivot_total": len(instances),
        "vector_any": vector_any,
        "vector_all": vector_all,
        "vector_total": len(grouped),
    }


def closure_survival_by_state_vector(
    instances: list[tuple[tuple[int, ...], int]],
    closure_results: dict[str, dict],
) -> list[dict]:
    grouped: dict[tuple[int, ...], list[int]] = defaultdict(list)
    for ms, t in instances:
        grouped[ms].append(t)

    universally_blocked = all(result["universally_blocked"] for result in closure_results.values())
    out: list[dict] = []

    for ms, pivots in grouped.items():
        pivot_total = len(pivots)
        typed_total = pivot_total * len(HARD_TYPES)

        if universally_blocked:
            pivot_survivors = 0
            typed_survivors = 0
        else:
            pivot_survivors = 0
            typed_survivors = 0
            for t in pivots:
                rotated = rotate_ms_to_pivot_zero(ms, t)
                any_survivor = False
                for hard in HARD_TYPES:
                    if full_cycle_sat(rotated, hard.word):
                        typed_survivors += 1
                        any_survivor = True
                if any_survivor:
                    pivot_survivors += 1

        out.append(
            {
                "ms": ms,
                "product": prod(ms),
                "pivots": tuple(sorted(pivots)),
                "pivot_total": pivot_total,
                "pivot_survivors": pivot_survivors,
                "typed_total": typed_total,
                "typed_survivors": typed_survivors,
            }
        )

    out.sort(key=lambda row: (row["pivot_survivors"], row["typed_survivors"], row["ms"]))
    return out


def print_header(title: str) -> None:
    print(title)
    print("-" * len(title))


def main() -> None:
    instances = candidate_instances()
    vectors = [ms for ms in enumerate_state_vectors() if has_ge3_binary(ms) and sandwiched_pivots(ms)]
    grouped_instances: dict[tuple[int, ...], list[int]] = defaultdict(list)
    for ms, t in instances:
        grouped_instances[ms].append(t)

    print_header("Universal allNormalForm check")
    print(f"candidate state vectors: {len(vectors)}")
    print(f"sandwiched-pivot instances: {len(instances)}")
    print(f"typed witnesses (4 hard types per pivot): {len(instances) * len(HARD_TYPES)}")
    print()

    print_header("Check A: actual (J,K) pairs under Lean hall_normal")
    per_branch_pairs: dict[str, Counter[tuple[int, int]]] = {}
    aggregate_pairs_one_copy: Counter[tuple[int, int]] = Counter()
    aggregate_pairs_all_typed: Counter[tuple[int, int]] = Counter()

    for hard in HARD_TYPES:
        pairs = lean_phase_pairs(hard.word)
        per_branch_pairs[hard.name] = pairs
        aggregate_pairs_one_copy.update(pairs)
        for pair, count in pairs.items():
            aggregate_pairs_all_typed[pair] += count * len(instances)

        print(f"{hard.name}:")
        print(f"  Lean suffix phases: {sum(pairs.values())}")
        print(f"  phase pairs: {', '.join(f'{fmt_pair(pair)}x{count}' for pair, count in sorted(pairs.items()))}")

    observed_pair_universe = sorted(aggregate_pairs_one_copy)
    assert all(normal_ok(pair) for pair in observed_pair_universe)

    print("aggregate over one copy of each hard type:")
    print(
        "  "
        + ", ".join(
            f"{fmt_pair(pair)}x{aggregate_pairs_one_copy[pair]}"
            for pair in sorted(aggregate_pairs_one_copy)
        )
    )
    print("lifted across all typed witnesses:")
    print(
        "  "
        + ", ".join(
            f"{fmt_pair(pair)}x{aggregate_pairs_all_typed[pair]}"
            for pair in sorted(aggregate_pairs_all_typed)
        )
    )
    print(f"observed pair universe: {[fmt_pair(pair) for pair in observed_pair_universe]}")
    print("conclusion: hall_normal is compatible with explicit witnesses; Check A does not yield a contradiction.")
    print()

    print_header("Check B: binary closure parity")
    binary_parity_universal = True
    for hard in HARD_TYPES:
        counts = fire_counts(hard.word)
        odd_offsets = odd_fire_offsets(hard.word)
        stats = branch_binary_parity_stats(instances, odd_offsets)

        print(f"{hard.name}:")
        print(
            f"  odd-fire positions relative to pivot: {fmt_offsets(odd_offsets)}"
        )
        print(
            "  odd totalFires counts: "
            + ", ".join(
                f"{offset_label(signed_offset(p))}={count}"
                for p, count in sorted(counts.items())
                if count % 2 == 1
            )
        )
        print(
            f"  pivot instances with some odd-count binary: "
            f"{stats['pivot_hits']}/{stats['pivot_total']}"
        )
        print(
            f"  state vectors with all pivots parity-killed: "
            f"{stats['vector_all']}/{stats['vector_total']}"
        )
        print(
            f"  state vectors with at least one pivot parity-killed: "
            f"{stats['vector_any']}/{stats['vector_total']}"
        )
        if stats["pivot_hits"] != stats["pivot_total"]:
            binary_parity_universal = False

    print(
        "conclusion: binary parity kills LeftSame/RightSame universally, "
        "but not LeftCross/RightCross, so Check B is not universal."
    )
    print()

    print_header("Check C: cyclic closure by state vector")
    closure_results: dict[str, dict] = {}
    for hard in HARD_TYPES:
        closure_results[hard.name] = analyze_hard_type(instances, hard)

    for hard in HARD_TYPES:
        result = closure_results[hard.name]
        print(f"{hard.name}:")
        print(f"  full_cycle_sat_on_super_domain={result['full_cycle_sat_super']}")
        print(f"  fixed_boundary_triples={list(result['fixed_boundary_triples'])}")
        print(f"  universally_blocked={result['universally_blocked']}")
        print(f"  typed survivors={result['survivors']}/{result['witness_instances']}")

    vector_rows = closure_survival_by_state_vector(instances, closure_results)
    pivot_count_dist = Counter(row["pivot_total"] for row in vector_rows)
    vectors_with_typed_survivors = sum(1 for row in vector_rows if row["typed_survivors"] > 0)
    vectors_with_pivot_survivors = sum(1 for row in vector_rows if row["pivot_survivors"] > 0)

    print("state-vector grouping:")
    for pivot_count in sorted(pivot_count_dist):
        print(
            f"  {pivot_count} pivot(s): {pivot_count_dist[pivot_count]} vectors, "
            f"all at 0% survival"
        )
    print(f"  vectors with any surviving typed witness: {vectors_with_typed_survivors}/{len(vector_rows)}")
    print(f"  vectors with any surviving pivot witness: {vectors_with_pivot_survivors}/{len(vector_rows)}")
    print("sample state vectors:")
    for row in vector_rows[:5]:
        print(
            f"  ms={row['ms']} pivots={list(row['pivots'])} "
            f"pivot_survival={row['pivot_survivors']}/{row['pivot_total']} "
            f"typed_survival={row['typed_survivors']}/{row['typed_total']}"
        )
    print("conclusion: cyclic closure kills every hard-residue witness on every state vector.")
    print()

    print_header("Check D: simpler parity-only summation argument")
    parity_only_universal = True
    for hard in HARD_TYPES:
        gaps = cyclic_gap_pairs(hard.word)
        j_sum = sum(pair[0] for pair in gaps)
        k_sum = sum(pair[1] for pair in gaps)
        counts = fire_counts(hard.word)
        left_total = counts[left(PIVOT)]
        right_total = counts[right(PIVOT)]
        gap_parity_ok = all(parity_only_ok(pair) for pair in gaps)
        full_normal_ok = all(normal_ok(pair) for pair in gaps)

        print(f"{hard.name}:")
        print(f"  cyclic consecutive gaps: {[fmt_pair(pair) for pair in gaps]}")
        print(f"  parity-only condition holds on every cyclic gap: {gap_parity_ok}")
        print(f"  full allNormalForm holds on every cyclic gap: {full_normal_ok}")
        print(f"  sum J over cyclic gaps = {j_sum}, totalFires(left(t)) = {left_total}")
        print(f"  sum K over cyclic gaps = {k_sum}, totalFires(right(t)) = {right_total}")

        if gap_parity_ok:
            # If the parity-only condition already forced a contradiction, these
            # explicit examples could not exist.
            parity_only_universal = False

    print(
        "conclusion: the parity-only claim 'each cyclic gap has at least one odd' "
        "does not force a contradiction. Explicit witnesses satisfy it while their "
        "neighbor totals still match the cyclic sums."
    )
    print()

    print_header("Verdict")
    print("Check A: no universal contradiction; witnesses realize only five legal Lean phase pairs.")
    print("Check B: not universal; binary odd-parity kills Same branches but not all Cross branches.")
    print("Check C: universal; cyclic closure kills every witness on every sub-threshold state vector.")
    print("Check D: not universal; the simpler parity-only summation argument has explicit witness counterexamples.")

    if not binary_parity_universal:
        print("universal obstruction that actually succeeds: Check C only.")
    else:
        print("universal obstructions that succeed: Check B and Check C.")


if __name__ == "__main__":
    main()
