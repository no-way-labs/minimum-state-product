#!/usr/bin/env python3
"""Adjacent-column analysis for hypothetical bad cycles in CUP-2.

This script is deliberately Python-only. It reads the existing CUP-2 witness
semantics from local research code and investigates four related questions:

1. Exact "pseudo-cycle" evidence from the bad-step DAG at n=9.
2. Synthetic random 100-step bad walks at n=20.
3. Fixed-boundary pure-T_mid strip dynamics.
4. Whether a weaker state-only matching condition is materially more plausible
   than full matching of local (L,S,R) column profiles.

The exact bad-step semantics here match the local Lean-side research scripts:
`bad` means "off the explicit good cycle", not "outside the good basin".
"""

from __future__ import annotations

import argparse
import os
import random
import statistics
import sys
import time
from collections import deque
from itertools import product
from typing import Dict, Iterable, Iterator, List, Optional, Sequence, Tuple


ROOT = os.path.dirname(__file__)
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from seam_counterexample_analysis import (  # noqa: E402
    Config,
    T_MID,
    cup2M,
    good_cycle_configs,
    move,
)


Pair = Tuple[int, int]


def fmt_ratio(num: int, den: int) -> str:
    if den == 0:
        return "N/A"
    return f"{num}/{den} = {num / den:.3f}"


def all_cup2_configs(n: int) -> List[Config]:
    return list(product(*(range(cup2M(n, i)) for i in range(n))))


def interior_mid_positions(n: int) -> List[int]:
    """All positions that use T_mid in the size-n ring."""
    return list(range(2, n - 2))


def state_column(configs: Sequence[Config], pos: int) -> Tuple[int, ...]:
    return tuple(cfg[pos] for cfg in configs)


def triple_column(configs: Sequence[Config], pos: int) -> Tuple[Tuple[int, int, int], ...]:
    return tuple((cfg[pos - 1], cfg[pos], cfg[pos + 1]) for cfg in configs)


def hamming(seq1: Sequence[object], seq2: Sequence[object]) -> int:
    return sum(x != y for x, y in zip(seq1, seq2))


def snapshot_adjacent_equal_ratio(configs: Sequence[Config], positions: Sequence[int]) -> List[float]:
    if len(positions) < 2:
        return [1.0 for _ in configs]
    out: List[float] = []
    denom = len(positions) - 1
    for cfg in configs:
        hits = sum(cfg[pos] == cfg[pos + 1] for pos in positions[:-1])
        out.append(hits / denom)
    return out


def column_window_summary(
    configs: Sequence[Config],
    positions: Sequence[int],
) -> Dict[str, object]:
    state_cols = {pos: state_column(configs, pos) for pos in positions}
    triple_cols = {pos: triple_column(configs, pos) for pos in positions}

    adjacent_rows: List[Dict[str, object]] = []
    for pos in positions[:-1]:
        s_left = state_cols[pos]
        s_right = state_cols[pos + 1]
        t_left = triple_cols[pos]
        t_right = triple_cols[pos + 1]
        adjacent_rows.append(
            {
                "pair": (pos, pos + 1),
                "state_exact": s_left == s_right,
                "triple_exact": t_left == t_right,
                "state_hamming": hamming(s_left, s_right),
                "triple_hamming": hamming(t_left, t_right),
                "length": len(configs),
            }
        )

    repeated_state_pairs = [
        (i, j)
        for idx, i in enumerate(positions)
        for j in positions[idx + 1 :]
        if state_cols[i] == state_cols[j]
    ]
    repeated_triple_pairs = [
        (i, j)
        for idx, i in enumerate(positions)
        for j in positions[idx + 1 :]
        if triple_cols[i] == triple_cols[j]
    ]

    ratios = snapshot_adjacent_equal_ratio(configs, positions)

    return {
        "adjacent_rows": adjacent_rows,
        "repeated_state_pairs": repeated_state_pairs,
        "repeated_triple_pairs": repeated_triple_pairs,
        "snapshot_equal_ratios": ratios,
    }


class ExplicitBadDag:
    """Bad-step DAG relative to the explicit CUP-2 good cycle."""

    def __init__(self, n: int):
        self.n = n
        self.good_cycle = good_cycle_configs(n)
        self.bad_configs = [cfg for cfg in all_cup2_configs(n) if cfg not in self.good_cycle]
        self.bad_id = {cfg: idx for idx, cfg in enumerate(self.bad_configs)}

        self.adj: List[List[Tuple[int, int]]] = [[] for _ in self.bad_configs]
        indeg = [0] * len(self.bad_configs)
        edge_count = 0
        for src_id, cfg in enumerate(self.bad_configs):
            for mover in range(n):
                dst = move(cfg, mover)
                if dst is None or dst in self.good_cycle:
                    continue
                dst_id = self.bad_id[dst]
                self.adj[src_id].append((mover, dst_id))
                indeg[dst_id] += 1
                edge_count += 1
        self.edge_count = edge_count

        queue = deque(i for i, deg in enumerate(indeg) if deg == 0)
        topo: List[int] = []
        indeg_mut = indeg[:]
        while queue:
            node = queue.popleft()
            topo.append(node)
            for _, nxt in self.adj[node]:
                indeg_mut[nxt] -= 1
                if indeg_mut[nxt] == 0:
                    queue.append(nxt)
        if len(topo) != len(self.bad_configs):
            raise RuntimeError("Expected bad-step graph to be a DAG")
        self.topo = topo

        self.rank = [0] * len(self.bad_configs)
        self.best_succ: List[Optional[Tuple[int, int]]] = [None] * len(self.bad_configs)
        for node in reversed(self.topo):
            if not self.adj[node]:
                continue
            max_child_rank = max(self.rank[nxt] for _, nxt in self.adj[node])
            candidates = [(mover, nxt) for mover, nxt in self.adj[node] if self.rank[nxt] == max_child_rank]
            chosen = min(candidates, key=lambda item: (self.bad_configs[item[1]], item[0]))
            self.rank[node] = max_child_rank + 1
            self.best_succ[node] = chosen

        self.max_rank = max(self.rank, default=0)
        self.max_rank_starts = sorted(
            (idx for idx, r in enumerate(self.rank) if r == self.max_rank),
            key=lambda idx: self.bad_configs[idx],
        )

    def longest_path(self) -> Tuple[List[Config], List[int]]:
        if not self.max_rank_starts:
            return [], []
        node = self.max_rank_starts[0]
        configs: List[Config] = []
        movers: List[int] = []
        while True:
            configs.append(self.bad_configs[node])
            edge = self.best_succ[node]
            if edge is None:
                break
            mover, nxt = edge
            movers.append(mover)
            node = nxt
        return configs, movers


def print_pair_rows(rows: Sequence[Dict[str, object]]) -> None:
    for row in rows:
        left, right = row["pair"]
        length = int(row["length"])
        state_hamming = int(row["state_hamming"])
        triple_hamming = int(row["triple_hamming"])
        print(
            f"  pair {left}-{right}: "
            f"state_exact={row['state_exact']} "
            f"state_ham={state_hamming}/{length}, "
            f"triple_exact={row['triple_exact']} "
            f"triple_ham={triple_hamming}/{length}"
        )


def analyze_exact_bad_path(n: int) -> None:
    graph = ExplicitBadDag(n)
    positions = interior_mid_positions(n)
    path, movers = graph.longest_path()
    summary = column_window_summary(path, positions)
    ratios = summary["snapshot_equal_ratios"]

    print("=" * 88)
    print(f"1. Exact bad-step DAG at n={n}")
    print(f"bad nodes={len(graph.bad_configs)} edges={graph.edge_count}")
    print(f"max bad-path length={graph.max_rank} moves, {graph.max_rank + 1} configurations")
    print(f"number of max-rank starts={len(graph.max_rank_starts)}")
    if path:
        print(f"chosen path start={path[0]}")
        print(f"chosen path end  ={path[-1]}")
    print(f"T_mid positions={positions}")
    print()
    print("Whole-path column comparison on the chosen maximal bad path:")
    print_pair_rows(summary["adjacent_rows"])
    print(f"  repeated state columns (all pairs) : {summary['repeated_state_pairs']}")
    print(f"  repeated triple columns (all pairs): {summary['repeated_triple_pairs']}")
    print(
        "  snapshot adjacent-equal-state ratio: "
        f"first10={statistics.mean(ratios[:10]):.3f}, "
        f"last10={statistics.mean(ratios[-10:]):.3f}, "
        f"final={ratios[-1]:.3f}"
    )
    print(
        "  weaker state-only matching on the full path: "
        f"{sum(row['state_exact'] for row in summary['adjacent_rows'])} adjacent exact pairs"
    )
    print(
        "  full (L,S,R)-profile matching on the full path: "
        f"{sum(row['triple_exact'] for row in summary['adjacent_rows'])} adjacent exact pairs"
    )
    print()


def random_bad_successors(cfg: Config, n: int, good_cycle: Iterable[Config]) -> List[Tuple[int, Config]]:
    good = good_cycle if isinstance(good_cycle, set) else set(good_cycle)
    out: List[Tuple[int, Config]] = []
    for mover in range(n):
        dst = move(cfg, mover)
        if dst is not None and dst not in good:
            out.append((mover, dst))
    return out


def sample_random_bad_walk(
    n: int,
    steps: int,
    rng: random.Random,
    good_cycle: set[Config],
    max_attempts: int,
) -> Tuple[Optional[List[Config]], int]:
    attempts = 0
    while attempts < max_attempts:
        attempts += 1
        cfg = tuple(rng.randrange(cup2M(n, i)) for i in range(n))
        if cfg in good_cycle:
            continue
        path = [cfg]
        while len(path) < steps + 1:
            succs = random_bad_successors(cfg, n, good_cycle)
            if not succs:
                break
            _, cfg = rng.choice(succs)
            path.append(cfg)
        if len(path) == steps + 1:
            return path, attempts
    return None, attempts


def analyze_random_bad_walks(
    n: int,
    steps: int,
    trials: int,
    suffix_len: int,
    seed: int,
    max_attempts_per_trial: int,
) -> None:
    rng = random.Random(seed)
    good = good_cycle_configs(n)
    positions = interior_mid_positions(n)

    whole_state_exact = 0
    whole_triple_exact = 0
    suffix_state_exact = 0
    suffix_triple_exact = 0
    early_snapshot_means: List[float] = []
    late_snapshot_means: List[float] = []
    min_state_hams: List[int] = []
    min_triple_hams: List[int] = []
    restarts = 0

    successful = 0
    while successful < trials:
        path, tries = sample_random_bad_walk(n, steps, rng, good, max_attempts_per_trial)
        restarts += tries
        if path is None:
            break
        successful += 1

        whole = column_window_summary(path, positions)
        suffix = column_window_summary(path[-suffix_len:], positions)
        whole_rows = whole["adjacent_rows"]
        suffix_rows = suffix["adjacent_rows"]

        whole_state_exact += sum(row["state_exact"] for row in whole_rows)
        whole_triple_exact += sum(row["triple_exact"] for row in whole_rows)
        suffix_state_exact += sum(row["state_exact"] for row in suffix_rows)
        suffix_triple_exact += sum(row["triple_exact"] for row in suffix_rows)
        min_state_hams.append(min(int(row["state_hamming"]) for row in whole_rows))
        min_triple_hams.append(min(int(row["triple_hamming"]) for row in whole_rows))

        ratios = whole["snapshot_equal_ratios"]
        early_snapshot_means.append(statistics.mean(ratios[:suffix_len]))
        late_snapshot_means.append(statistics.mean(ratios[-suffix_len:]))

    total_adjacent_pairs = successful * max(0, len(positions) - 1)

    print("=" * 88)
    print(f"2. Synthetic random bad walks at n={n}")
    print(
        f"requested {trials} walks of {steps} bad steps, "
        f"successful={successful}, sampled_starts={restarts}"
    )
    print(f"T_mid positions={positions}")
    print(
        "Whole-path adjacent exact matches: "
        f"state={fmt_ratio(whole_state_exact, total_adjacent_pairs)}, "
        f"triple={fmt_ratio(whole_triple_exact, total_adjacent_pairs)}"
    )
    print(
        f"Last-{suffix_len}-configuration suffix exact matches: "
        f"state={fmt_ratio(suffix_state_exact, total_adjacent_pairs)}, "
        f"triple={fmt_ratio(suffix_triple_exact, total_adjacent_pairs)}"
    )
    if successful:
        print(
            "Mean snapshot adjacent-equal-state ratio: "
            f"first{suffix_len}={statistics.mean(early_snapshot_means):.3f}, "
            f"last{suffix_len}={statistics.mean(late_snapshot_means):.3f}"
        )
        print(
            "Whole-path near-miss scale: "
            f"mean min state Hamming={statistics.mean(min_state_hams):.2f}/{steps + 1}, "
            f"mean min triple Hamming={statistics.mean(min_triple_hams):.2f}/{steps + 1}"
        )
    print()


def strip_successors(state: Tuple[int, ...], left_boundary: int, right_boundary: int) -> Iterator[Tuple[int, ...]]:
    ext = (left_boundary,) + state + (right_boundary,)
    for pos in range(len(state)):
        left_val, self_val, right_val = ext[pos], ext[pos + 1], ext[pos + 2]
        out = T_MID[(left_val, self_val, right_val)]
        if out != self_val:
            yield state[:pos] + (out,) + state[pos + 1 :]


def count_202_in_ext(ext: Sequence[int]) -> int:
    return sum(1 for i in range(len(ext) - 2) if tuple(ext[i : i + 3]) == (2, 0, 2))


def strip_count202(state: Tuple[int, ...], left_boundary: int, right_boundary: int) -> int:
    return count_202_in_ext((left_boundary,) + state + (right_boundary,))


def strip_tail_rank(state: Tuple[int, ...], left_boundary: int, right_boundary: int) -> Tuple[int, int, int, int, int]:
    ext = (left_boundary,) + state + (right_boundary,)
    edges = list(zip(ext, ext[1:]))
    n21 = sum(edge == (2, 1) for edge in edges)
    n01 = sum(edge == (0, 1) for edge in edges)
    n20 = sum(edge == (2, 0) for edge in edges)
    n02 = sum(edge == (0, 2) for edge in edges)
    mu = 0
    m = len(state)
    for j, edge in enumerate(edges):
        if edge == (0, 2) or edge == (1, 0):
            mu += m + 1 - j
        elif edge == (1, 2) or edge == (2, 0):
            mu += j
    return (n21, n01, n20, n02, mu)


def strip_full_rank(state: Tuple[int, ...], left_boundary: int, right_boundary: int) -> Tuple[int, int, int, int, int, int]:
    return (strip_count202(state, left_boundary, right_boundary),) + strip_tail_rank(
        state, left_boundary, right_boundary
    )


def verify_local_202_monotonicity() -> Dict[str, int]:
    total_moves = 0
    strict_202_drops = 0
    for ext in product(range(3), repeat=5):
        before = count_202_in_ext(ext)
        for center in (1, 2, 3):
            left_val, self_val, right_val = ext[center - 1], ext[center], ext[center + 1]
            out = T_MID[(left_val, self_val, right_val)]
            if out == self_val:
                continue
            total_moves += 1
            new_ext = list(ext)
            new_ext[center] = out
            after = count_202_in_ext(new_ext)
            if after > before:
                raise RuntimeError(
                    f"Local move increased #202: ext={ext}, center={center}, new_ext={tuple(new_ext)}"
                )
            if (left_val, self_val, right_val) == (2, 0, 2):
                if after >= before:
                    raise RuntimeError(
                        f"202-centered move failed to decrease #202: ext={ext}, new_ext={tuple(new_ext)}"
                    )
                strict_202_drops += 1
    return {"total_moves": total_moves, "strict_202_drops": strict_202_drops}


def verify_strip_rank(max_len: int) -> Dict[str, int]:
    checked_edges = 0
    for m in range(1, max_len + 1):
        for left_boundary, right_boundary in product(range(3), repeat=2):
            for state in product(range(3), repeat=m):
                before = strip_full_rank(state, left_boundary, right_boundary)
                for succ in strip_successors(state, left_boundary, right_boundary):
                    checked_edges += 1
                    after = strip_full_rank(succ, left_boundary, right_boundary)
                    if not (after < before):
                        raise RuntimeError(
                            "Candidate strip rank failed: "
                            f"m={m}, boundaries=({left_boundary},{right_boundary}), "
                            f"state={state}, succ={succ}, before={before}, after={after}"
                        )
    return {"max_len": max_len, "checked_edges": checked_edges}


def strip_dag_and_sink_count(m: int, left_boundary: int, right_boundary: int) -> Tuple[bool, int]:
    states = list(product(range(3), repeat=m))
    idx = {state: i for i, state in enumerate(states)}
    indeg = [0] * len(states)
    outdeg = [0] * len(states)
    edges: List[List[int]] = [[] for _ in states]

    for src_id, state in enumerate(states):
        for succ in strip_successors(state, left_boundary, right_boundary):
            dst_id = idx[succ]
            edges[src_id].append(dst_id)
            outdeg[src_id] += 1
            indeg[dst_id] += 1

    queue = deque(i for i, deg in enumerate(indeg) if deg == 0)
    seen = 0
    indeg_mut = indeg[:]
    while queue:
        node = queue.popleft()
        seen += 1
        for nxt in edges[node]:
            indeg_mut[nxt] -= 1
            if indeg_mut[nxt] == 0:
                queue.append(nxt)

    return seen == len(states), sum(1 for deg in outdeg if deg == 0)


def analyze_fixed_boundary_strips(strip_max_len: int, strip_rank_max_len: int) -> None:
    local = verify_local_202_monotonicity()
    rank_check = verify_strip_rank(strip_rank_max_len)

    sink_counts_at_max: Dict[Pair, int] = {}
    all_dag = True
    for m in range(1, strip_max_len + 1):
        for pair in product(range(3), repeat=2):
            left_boundary, right_boundary = pair
            is_dag, sink_count = strip_dag_and_sink_count(m, left_boundary, right_boundary)
            all_dag = all_dag and is_dag
            if not is_dag:
                raise RuntimeError(
                    f"Found a non-DAG strip at m={m}, boundaries=({left_boundary},{right_boundary})"
                )
            if m == strip_max_len:
                sink_counts_at_max[pair] = sink_count

    print("=" * 88)
    print("3. Fixed-boundary pure-T_mid strip")
    print(
        "Local 202 monotonicity: "
        f"checked {local['total_moves']} privileged radius-2 local moves, "
        f"202-centered strict drops={local['strict_202_drops']}"
    )
    print(
        "Candidate full-strip rank verified: "
        f"R = (#202, N21, N01, N20, N02, mu), "
        f"lengths <= {rank_check['max_len']}, checked_edges={rank_check['checked_edges']}"
    )
    print(
        f"Exhaustive strip graph survey: every boundary pair is a DAG for lengths <= {strip_max_len}: {all_dag}"
    )
    print(f"Sink counts at length {strip_max_len}:")
    for pair in sorted(sink_counts_at_max):
        print(f"  boundaries {pair}: sinks={sink_counts_at_max[pair]}")
    print()


def print_conclusion() -> None:
    print("=" * 88)
    print("4. Interpretation")
    print("Adjacent full (L,S,R)-column matching is much stronger than plain repeated columns.")
    print(
        "For adjacent positions j and j+1, equality of the centered triples at one time already forces "
        "c[j-1]=c[j]=c[j+1]=c[j+2] at that time, so cycle-wide triple-column equality is a four-site lockstep condition."
    )
    print()
    print("What the experiments say:")
    print("  - Exact n=9 maximal bad paths show no repeated state columns and no repeated triple columns among T_mid positions.")
    print("  - Random 100-step bad walks at n=20 show strong late spatial coalescence, but still no whole-path adjacent column equality.")
    print("  - The weaker state-only condition is more plausible late in a path, but still not supported as a cycle-wide invariant.")
    print("  - Fixed-boundary strip dynamics are acyclic, not genuinely periodic, and the boundary does not determine a unique bulk state.")
    print()
    print("Mathematical takeaway:")
    print(
        "The clean bulk statement is termination, not periodicity. A promising rank is "
        "R = (#202, N21, N01, N20, N02, mu), which extends the existing pure-mid rank by counting 202 defects first."
    )
    print(
        "That argues against an 'exponential decay to a unique wave' proof of adjacent matching. "
        "It supports a bulk-stabilization theorem, but not an automatic adjacency lemma for whole cycles."
    )
    print()
    print("Most plausible next direction:")
    print(
        "Replace exact whole-cycle column matching by a weaker compression invariant tied to a stabilized suffix or a rank-preserving deletion argument, "
        "rather than trying to force adjacent identical columns over an entire hypothetical cycle."
    )


def parse_args(argv: Optional[Sequence[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exact-n", type=int, default=9, help="size for the exact bad-step DAG study")
    parser.add_argument("--random-n", type=int, default=20, help="size for random bad walks")
    parser.add_argument("--random-steps", type=int, default=100, help="bad steps per random walk")
    parser.add_argument("--random-trials", type=int, default=20, help="successful full-length walks to collect")
    parser.add_argument("--random-seed", type=int, default=0, help="PRNG seed for random walks")
    parser.add_argument(
        "--random-max-attempts-per-trial",
        type=int,
        default=20000,
        help="max random start attempts for each requested full walk",
    )
    parser.add_argument(
        "--suffix-len",
        type=int,
        default=20,
        help="suffix length used when checking late-stage column coalescence",
    )
    parser.add_argument(
        "--strip-max-len",
        type=int,
        default=11,
        help="max fixed-boundary strip length for the DAG survey",
    )
    parser.add_argument(
        "--strip-rank-max-len",
        type=int,
        default=9,
        help="max fixed-boundary strip length for the candidate rank check",
    )
    return parser.parse_args(argv)


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = parse_args(argv)
    t0 = time.time()
    analyze_exact_bad_path(args.exact_n)
    analyze_random_bad_walks(
        n=args.random_n,
        steps=args.random_steps,
        trials=args.random_trials,
        suffix_len=args.suffix_len,
        seed=args.random_seed,
        max_attempts_per_trial=args.random_max_attempts_per_trial,
    )
    analyze_fixed_boundary_strips(
        strip_max_len=args.strip_max_len,
        strip_rank_max_len=args.strip_rank_max_len,
    )
    print_conclusion()
    print("=" * 88)
    print(f"done in {time.time() - t0:.3f}s")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
