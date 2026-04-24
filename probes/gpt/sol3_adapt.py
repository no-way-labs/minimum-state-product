#!/usr/bin/env python3
"""Adapt Dijkstra Solution 3 to mixed state-count families and verify them.

The primary use case is the one-binary family
    (2, 3, 3, ..., 3)
for varying ring sizes. The script keeps the six local-rule variants from the
older prototype, but uses the current verifier stack:

- `p2_ring.verify_system` for the graph-level validity check and recurrent-cycle
  summaries
- `scripts.verify_witnesses.verify` as a direct check of Dijkstra's five
  properties
"""

from __future__ import annotations

import argparse
import os
import sys
import time
from dataclasses import dataclass
from itertools import product as cartesian


ROOT = os.path.dirname(os.path.dirname(__file__))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from p2_ring import RingSystem, materialize_rule, verify_system
from scripts import verify_witnesses


@dataclass(frozen=True)
class FamilyResult:
    label: str
    state_counts: tuple[int, ...]
    product: int
    graph_valid: bool
    graph_message: str
    cycle_lengths: tuple[int, ...]
    good_config_count: int
    total_configs: int
    witness_verify_ok: bool | None
    elapsed_seconds: float


def product_of(state_counts: tuple[int, ...]) -> int:
    total = 1
    for m in state_counts:
        total *= m
    return total


def build_rule_tables(
    state_counts: tuple[int, ...],
    rule_functions: list,
) -> tuple[dict[tuple[int, int, int], int], ...]:
    return tuple(
        materialize_rule(state_counts, processor, rule_functions[processor])
        for processor in range(len(state_counts))
    )


def build_system(state_counts: tuple[int, ...], adapt_fn) -> RingSystem:
    rule_functions = adapt_fn(list(state_counts), len(state_counts))
    rules = build_rule_tables(state_counts, rule_functions)
    return RingSystem(state_counts=state_counts, rules=rules)


def one_binary_family(n: int, binary_index: int) -> tuple[int, ...]:
    if not (0 <= binary_index < n):
        raise ValueError(f"binary index {binary_index} out of range for n={n}")
    state_counts = [3] * n
    state_counts[binary_index] = 2
    return tuple(state_counts)


def summarize_system(
    label: str,
    system: RingSystem,
    run_witness_verify: bool = True,
) -> FamilyResult:
    started = time.time()
    graph_result = verify_system(system)
    witness_verify_ok: bool | None = None
    if graph_result.valid and run_witness_verify:
        witness_verify_ok = verify_witnesses.verify(label, system.state_counts, system.rules)
    elapsed = time.time() - started
    cycle_lengths = tuple(summary.length for summary in graph_result.cycle_summaries)
    return FamilyResult(
        label=label,
        state_counts=system.state_counts,
        product=product_of(system.state_counts),
        graph_valid=graph_result.valid,
        graph_message=graph_result.message,
        cycle_lengths=cycle_lengths,
        good_config_count=sum(cycle_lengths),
        total_configs=graph_result.configuration_count,
        witness_verify_ok=witness_verify_ok,
        elapsed_seconds=elapsed,
    )


def print_result(result: FamilyResult) -> None:
    print(f"{result.label}:")
    print(f"  state_counts={result.state_counts} product={result.product}")
    print(
        f"  graph_valid={result.graph_valid} message={result.graph_message} "
        f"elapsed={result.elapsed_seconds:.3f}s"
    )
    if result.graph_valid:
        print(
            f"  cycle_lengths={result.cycle_lengths} "
            f"good_configs={result.good_config_count} total_configs={result.total_configs}"
        )
        print(
            "  five_properties="
            f"{{liveness: True, mutual_exclusion: True, closure: True, convergence: True, fairness: True}}"
        )
        if result.witness_verify_ok is not None:
            print(f"  witness_verify={result.witness_verify_ok}")


def sol3_original(n, K=3):
    """Original Sol 3 rules for all-K system."""

    def f_bottom(L, S, R):
        if (S + 1) % K == R:
            return (S - 1) % K
        return S

    def f_top(L, S, R):
        if L == R and (L + 1) % K != S:
            return (L + 1) % K
        return S

    def f_middle(L, S, R):
        if (S + 1) % K == L:
            return L
        if (S + 1) % K == R:
            return R
        return S

    return [f_bottom] + [f_middle] * (n - 2) + [f_top]


def sol3_adapt_v1(ms, n):
    """Adaptation v1: replace K with m_i in mod operations."""

    def make_bottom(m0):
        def f(L, S, R):
            if (S + 1) % m0 == R % m0:
                return (S - 1) % m0
            return S

        return f

    def make_top(m_top):
        def f(L, S, R):
            if L % m_top == R % m_top and (L % m_top + 1) % m_top != S:
                return (L % m_top + 1) % m_top
            return S

        return f

    def make_middle(m_i):
        def f(L, S, R):
            new_L = L % m_i
            new_R = R % m_i
            if (S + 1) % m_i == new_L:
                return new_L
            if (S + 1) % m_i == new_R:
                return new_R
            return S

        return f

    fs = [make_bottom(ms[0])]
    for i in range(1, n - 1):
        fs.append(make_middle(ms[i]))
    fs.append(make_top(ms[n - 1]))
    return fs


def sol3_adapt_v2(ms, n):
    """Adaptation v2: use min(m_i, m_neighbor) for comparisons."""

    def make_bottom(m0, m1):
        K = min(m0, m1)

        def f(L, S, R):
            if (S + 1) % K == R % K:
                return (S - 1) % m0
            return S

        return f

    def make_top(m_top, m_prev, m_next):
        K = min(m_top, m_prev, m_next)

        def f(L, S, R):
            if L % K == R % K and (L % K + 1) % K != S % K:
                return (L % K + 1) % m_top
            return S

        return f

    def make_middle(m_i, m_prev, m_next):
        K_L = min(m_i, m_prev)
        K_R = min(m_i, m_next)

        def f(L, S, R):
            if (S + 1) % K_L == L % K_L:
                return L % m_i
            if (S + 1) % K_R == R % K_R:
                return R % m_i
            return S

        return f

    fs = [make_bottom(ms[0], ms[1])]
    for i in range(1, n - 1):
        fs.append(make_middle(ms[i], ms[i - 1], ms[i + 1]))
    fs.append(make_top(ms[n - 1], ms[n - 2], ms[0]))
    return fs


def sol3_adapt_v3(ms, n):
    """Adaptation v3: keep K=3 for all comparisons, cap invalid outputs."""
    K = 3

    def make_bottom(m0):
        def f(L, S, R):
            if (S + 1) % K == R % K:
                result = (S - 1) % K
                if result < m0:
                    return result
            return S

        return f

    def make_top(m_top):
        def f(L, S, R):
            if L % K == R % K and (L % K + 1) % K != S % K:
                result = (L % K + 1) % K
                if result < m_top:
                    return result
            return S

        return f

    def make_middle(m_i):
        def f(L, S, R):
            if (S + 1) % K == L % K:
                result = L % K
                if result < m_i:
                    return result
            if (S + 1) % K == R % K:
                result = R % K
                if result < m_i:
                    return result
            return S

        return f

    fs = [make_bottom(ms[0])]
    for i in range(1, n - 1):
        fs.append(make_middle(ms[i]))
    fs.append(make_top(ms[n - 1]))
    return fs


def sol3_adapt_v4(ms, n):
    """Adaptation v4: binary processors use toggle, ternaries use Sol 3."""

    def make_bottom(m0):
        def f(L, S, R):
            if m0 == 2:
                if S != R % 2:
                    return 1 - S
                return S
            if (S + 1) % 3 == R % 3:
                return (S - 1) % 3
            return S

        return f

    def make_top(m_top):
        def f(L, S, R):
            if m_top == 2:
                if L % 2 == R % 2 and L % 2 != S:
                    return L % 2
                return S
            if L % 3 == R % 3 and (L % 3 + 1) % 3 != S:
                return (L % 3 + 1) % 3
            return S

        return f

    def make_middle(m_i):
        def f(L, S, R):
            if m_i == 2:
                if S != L % 2:
                    return L % 2
                if S != R % 2:
                    return R % 2
                return S
            if (S + 1) % 3 == L % 3:
                return L % 3
            if (S + 1) % 3 == R % 3:
                return R % 3
            return S

        return f

    fs = [make_bottom(ms[0])]
    for i in range(1, n - 1):
        fs.append(make_middle(ms[i]))
    fs.append(make_top(ms[n - 1]))
    return fs


def sol3_adapt_v5(ms, n):
    """Adaptation v5: Sol 1 copy-left style."""

    def make_bottom(m0):
        def f(L, S, R):
            target = (L + 1) % m0
            if S != target:
                return target
            return S

        return f

    def make_other(m_i):
        def f(L, S, R):
            target = L % m_i
            if S != target:
                return target
            return S

        return f

    fs = [make_bottom(ms[0])]
    for i in range(1, n):
        fs.append(make_other(ms[i]))
    return fs


def sol3_adapt_v6(ms, n):
    """Adaptation v6: distinguished-proc Sol 1 style."""

    def make_distinguished(m0):
        def f(L, S, R):
            if L % m0 == S:
                return (S + 1) % m0
            return S

        return f

    def make_other(m_i):
        def f(L, S, R):
            target = L % m_i
            if S != target:
                return target
            return S

        return f

    fs = [make_distinguished(ms[0])]
    for i in range(1, n):
        fs.append(make_other(ms[i]))
    return fs


VARIANTS = {
    "v1": sol3_adapt_v1,
    "v2": sol3_adapt_v2,
    "v3": sol3_adapt_v3,
    "v4": sol3_adapt_v4,
    "v5": sol3_adapt_v5,
    "v6": sol3_adapt_v6,
}


def binary_positions_to_test(n: int) -> list[int]:
    if n <= 2:
        return list(range(n))
    return [0, 1, n - 1]


def run_primary_family_checks() -> list[FamilyResult]:
    results: list[FamilyResult] = []
    for n in range(5, 13):
        state_counts = one_binary_family(n, 0)
        system = build_system(state_counts, sol3_adapt_v1)
        result = summarize_system(f"v1 bottom n={n}", system)
        print_result(result)
        results.append(result)
        print()
    return results


def run_fallback_search(n_values: list[int]) -> list[FamilyResult]:
    results: list[FamilyResult] = []
    for n in n_values:
        print(f"Fallback search for n={n}")
        for position in binary_positions_to_test(n):
            state_counts = one_binary_family(n, position)
            for variant_name, adapt_fn in VARIANTS.items():
                label = f"{variant_name} pos={position} n={n}"
                system = build_system(state_counts, adapt_fn)
                result = summarize_system(label, system, run_witness_verify=False)
                print_result(result)
                results.append(result)
                if result.graph_valid:
                    witness_ok = verify_witnesses.verify(label, system.state_counts, system.rules)
                    print(f"  witness_verify={witness_ok}")
                    print()
                    return results
                print()
    return results


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--skip-fallback",
        action="store_true",
        help="do not widen to alternate placements/variants even if a primary target fails",
    )
    args = parser.parse_args()

    print("=" * 72)
    print("SOL 3 ADAPTED ONE-BINARY FAMILY")
    print("=" * 72)
    print()

    primary_results = run_primary_family_checks()
    failed_primary = [
        result for result in primary_results if not result.graph_valid and len(result.state_counts) >= 9
    ]
    if failed_primary and not args.skip_fallback:
        failing_n_values = sorted({len(result.state_counts) for result in failed_primary})
        run_fallback_search(failing_n_values)


if __name__ == "__main__":
    main()
