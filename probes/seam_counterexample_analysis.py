#!/usr/bin/env python3
"""Search seam-lifting counterexamples for source_transport at n=9.

This script uses the CUP-2 semantics from the local Lean development:
  - good cycle from cup2CycleVal
  - TP-preserving bad steps from (Exp2Count, Int21Count, Exp2Weight)
  - fc = cup2Fc = number of adjacent frontiers
  - PhiFull(c) = max fc over TP-bad-reachable configurations

The user request's step-3 wording ("number of good-cycle configs reachable")
is inconsistent with the local `cup2Fc` / `cup2PhiFull` definitions. This
script follows the repository semantics used by `source_transport`.
"""

from __future__ import annotations

import argparse
import time
from collections import deque
from dataclasses import dataclass
from itertools import product
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple


Config = Tuple[int, ...]
TpTriple = Tuple[int, int, int]


T_BOT = {
    (0, 0, 0): 1, (0, 0, 1): 1, (0, 0, 2): 0,
    (0, 1, 0): 1, (0, 1, 1): 1, (0, 1, 2): 1,
    (1, 0, 0): 0, (1, 0, 1): 1, (1, 0, 2): 0,
    (1, 1, 0): 0, (1, 1, 1): 1, (1, 1, 2): 0,
}

T_LOW = {
    (0, 0, 0): 0, (0, 0, 1): 0, (0, 0, 2): 0,
    (0, 1, 0): 0, (0, 1, 1): 1, (0, 1, 2): 0,
    (0, 2, 0): 0, (0, 2, 1): 2, (0, 2, 2): 0,
    (1, 0, 0): 1, (1, 0, 1): 1, (1, 0, 2): 1,
    (1, 1, 0): 1, (1, 1, 1): 1, (1, 1, 2): 2,
    (1, 2, 0): 0, (1, 2, 1): 1, (1, 2, 2): 2,
}

T_MID = {
    (0, 0, 0): 0, (0, 0, 1): 0, (0, 0, 2): 0,
    (0, 1, 0): 0, (0, 1, 1): 1, (0, 1, 2): 0,
    (0, 2, 0): 0, (0, 2, 1): 2, (0, 2, 2): 0,
    (1, 0, 0): 1, (1, 0, 1): 1, (1, 0, 2): 1,
    (1, 1, 0): 1, (1, 1, 1): 1, (1, 1, 2): 2,
    (1, 2, 0): 0, (1, 2, 1): 1, (1, 2, 2): 2,
    (2, 0, 0): 0, (2, 0, 1): 0, (2, 0, 2): 2,
    (2, 1, 0): 1, (2, 1, 1): 0, (2, 1, 2): 2,
    (2, 2, 0): 0, (2, 2, 1): 2, (2, 2, 2): 2,
}

T_HIGH = {
    (0, 0, 0): 0, (0, 0, 1): 0,
    (0, 1, 0): 0, (0, 1, 1): 0,
    (0, 2, 0): 0, (0, 2, 1): 0,
    (1, 0, 0): 1, (1, 0, 1): 1,
    (1, 1, 0): 1, (1, 1, 1): 2,
    (1, 2, 0): 0, (1, 2, 1): 2,
    (2, 0, 0): 0, (2, 0, 1): 2,
    (2, 1, 0): 0, (2, 1, 1): 2,
    (2, 2, 0): 2, (2, 2, 1): 2,
}

T_TOP = {
    (0, 0, 0): 0, (0, 0, 1): 0,
    (0, 1, 0): 0, (0, 1, 1): 0,
    (1, 0, 0): 0, (1, 0, 1): 1,
    (1, 1, 0): 1, (1, 1, 1): 1,
    (2, 0, 0): 1, (2, 0, 1): 1,
    (2, 1, 0): 1, (2, 1, 1): 1,
}


def cup2M(n: int, i: int) -> int:
    return 2 if i == 0 or i == n - 1 else 3


def cup2_cycle_val(n: int, t: int, j: int) -> int:
    if t < n:
        return 1 if j < t else 0
    if t < 2 * n - 2:
        if j < 2 * n - 1 - t:
            return 1
        if j < n - 1:
            return 2
        return 1
    if t == 2 * n - 2:
        if j == 0:
            return 1
        if j < n - 1:
            return 2
        return 1
    k = t - (2 * n - 2)
    if k == 0:
        if j == 0:
            return 1
        if j < n - 1:
            return 2
        return 1
    if j < k:
        return 0
    if j < n - 1:
        return 2
    return 1


def cycle_config(n: int, t: int) -> Config:
    return tuple(cup2_cycle_val(n, t, j) for j in range(n))


def good_cycle_configs(n: int) -> Set[Config]:
    return {cycle_config(n, t) for t in range(3 * n - 2)}


def delete_config(config: Config, k: int) -> Config:
    return config[:k] + config[k + 1 :]


def insert_value(config: Config, k: int, x: int) -> Config:
    return config[:k] + (x,) + config[k:]


def move_table(n: int, mover: int) -> Dict[Tuple[int, int, int], int]:
    if mover == 0:
        return T_BOT
    if mover == 1:
        return T_LOW
    if mover == n - 2:
        return T_HIGH
    if mover == n - 1:
        return T_TOP
    return T_MID


def out_value(config: Config, mover: int) -> int:
    n = len(config)
    left = config[(mover - 1) % n]
    self_val = config[mover]
    right = config[(mover + 1) % n]
    return move_table(n, mover)[(left, self_val, right)]


def privileged(config: Config, mover: int) -> bool:
    return out_value(config, mover) != config[mover]


def move(config: Config, mover: int) -> Optional[Config]:
    out = out_value(config, mover)
    if out == config[mover]:
        return None
    updated = list(config)
    updated[mover] = out
    return tuple(updated)


def frontier_bit(a: int, b: int) -> int:
    return 0 if a == b else 1


def fc(config: Config) -> int:
    n = len(config)
    return sum(frontier_bit(config[j], config[(j + 1) % n]) for j in range(n))


def exp2_count(config: Config) -> int:
    n = len(config)
    return sum(
        1
        for j in range(2, n - 2)
        if config[j] == 2 and config[(j + 1) % n] != 2
    )


def int21_count(config: Config) -> int:
    n = len(config)
    return sum(
        1
        for j in range(2, n - 2)
        if config[j] == 2 and config[(j + 1) % n] == 1
    )


def exp2_weight(config: Config) -> int:
    n = len(config)
    return sum(
        j
        for j in range(2, n - 2)
        if config[j] == 2 and config[(j + 1) % n] != 2
    )


def tp_invariant(config: Config) -> TpTriple:
    return (exp2_count(config), int21_count(config), exp2_weight(config))


def format_cfg(config: Config) -> str:
    return "(" + ",".join(str(x) for x in config) + ")"


@dataclass(frozen=True)
class SeamCounterexample:
    k: int
    mover_prime: int
    c_prime: Config
    d_prime: Config
    inserted_value: int
    c: Config
    fc_c: int
    fc_c_prime: int
    fc_d_prime: int
    c_is_bad: bool


class TpGraph:
    def __init__(self, n: int):
        self.n = n
        self.good_cycle = good_cycle_configs(n)
        self.all_configs: List[Config] = list(
            product(*(range(cup2M(n, i)) for i in range(n)))
        )
        self.fc_all: Dict[Config, int] = {cfg: fc(cfg) for cfg in self.all_configs}
        self.bad_configs: List[Config] = [
            cfg for cfg in self.all_configs if cfg not in self.good_cycle
        ]
        self.bad_id: Dict[Config, int] = {
            cfg: idx for idx, cfg in enumerate(self.bad_configs)
        }
        self.tp_all: Dict[Config, TpTriple] = {
            cfg: tp_invariant(cfg) for cfg in self.bad_configs
        }

        self.out_edges: List[List[Tuple[int, int]]] = [[] for _ in self.bad_configs]
        self.rev_edges: List[List[int]] = [[] for _ in self.bad_configs]

        t0 = time.time()
        for src_id, cfg in enumerate(self.bad_configs):
            src_tp = self.tp_all[cfg]
            for mover in range(n):
                dst = move(cfg, mover)
                if dst is None or dst in self.good_cycle:
                    continue
                dst_id = self.bad_id.get(dst)
                if dst_id is None or self.tp_all[dst] != src_tp:
                    continue
                self.out_edges[src_id].append((dst_id, mover))
                self.rev_edges[dst_id].append(src_id)
        self.build_time = time.time() - t0

        self._scc_ready = False
        self.comp_of: List[int] = []
        self.comp_nodes: List[List[int]] = []
        self.comp_succ: List[List[int]] = []
        self.comp_rev: List[List[int]] = []
        self.phi_comp: List[int] = []
        self.phi_bad: List[int] = []
        self._reverse_comp_cache: Dict[Tuple[int, ...], Set[int]] = {}

    def ensure_scc(self) -> None:
        if self._scc_ready:
            return

        node_count = len(self.bad_configs)
        visited = [False] * node_count
        order: List[int] = []

        for start in range(node_count):
            if visited[start]:
                continue
            stack: List[Tuple[int, int]] = [(start, 0)]
            visited[start] = True
            while stack:
                node, idx = stack[-1]
                if idx < len(self.out_edges[node]):
                    nxt, _ = self.out_edges[node][idx]
                    stack[-1] = (node, idx + 1)
                    if not visited[nxt]:
                        visited[nxt] = True
                        stack.append((nxt, 0))
                else:
                    order.append(node)
                    stack.pop()

        self.comp_of = [-1] * node_count
        self.comp_nodes = []
        for start in reversed(order):
            if self.comp_of[start] != -1:
                continue
            comp_id = len(self.comp_nodes)
            self.comp_nodes.append([])
            stack = [start]
            self.comp_of[start] = comp_id
            while stack:
                node = stack.pop()
                self.comp_nodes[comp_id].append(node)
                for prv in self.rev_edges[node]:
                    if self.comp_of[prv] == -1:
                        self.comp_of[prv] = comp_id
                        stack.append(prv)

        comp_count = len(self.comp_nodes)
        succ_sets = [set() for _ in range(comp_count)]
        rev_sets = [set() for _ in range(comp_count)]
        for src in range(node_count):
            src_comp = self.comp_of[src]
            for dst, _ in self.out_edges[src]:
                dst_comp = self.comp_of[dst]
                if src_comp != dst_comp:
                    succ_sets[src_comp].add(dst_comp)
                    rev_sets[dst_comp].add(src_comp)
        self.comp_succ = [sorted(s) for s in succ_sets]
        self.comp_rev = [sorted(s) for s in rev_sets]

        indeg = [len(preds) for preds in self.comp_rev]
        topo: List[int] = []
        queue = deque([cid for cid, deg in enumerate(indeg) if deg == 0])
        while queue:
            cid = queue.popleft()
            topo.append(cid)
            for nxt in self.comp_succ[cid]:
                indeg[nxt] -= 1
                if indeg[nxt] == 0:
                    queue.append(nxt)
        if len(topo) != comp_count:
            raise RuntimeError("TP condensation graph must be acyclic")

        self.phi_comp = [
            max(self.fc_all[self.bad_configs[node]] for node in nodes)
            for nodes in self.comp_nodes
        ]
        for cid in reversed(topo):
            best = self.phi_comp[cid]
            for nxt in self.comp_succ[cid]:
                if self.phi_comp[nxt] > best:
                    best = self.phi_comp[nxt]
            self.phi_comp[cid] = best

        self.phi_bad = [
            self.phi_comp[self.comp_of[node]] for node in range(node_count)
        ]
        self._scc_ready = True

    def phi_of(self, cfg: Config) -> int:
        if cfg in self.good_cycle:
            return self.fc_all[cfg]
        self.ensure_scc()
        return self.phi_bad[self.bad_id[cfg]]

    def _reverse_reachable_comps(self, target_comps: Iterable[int]) -> Set[int]:
        self.ensure_scc()
        key = tuple(sorted(set(target_comps)))
        if key not in self._reverse_comp_cache:
            seen: Set[int] = set(key)
            stack: List[int] = list(key)
            while stack:
                cid = stack.pop()
                for prv in self.comp_rev[cid]:
                    if prv not in seen:
                        seen.add(prv)
                        stack.append(prv)
            self._reverse_comp_cache[key] = seen
        return self._reverse_comp_cache[key]

    def seam_steps(self, k: int) -> List[Tuple[Config, Config, int]]:
        steps: List[Tuple[Config, Config, int]] = []
        for src_id, cfg in enumerate(self.bad_configs):
            for dst_id, mover in self.out_edges[src_id]:
                if mover in (k - 1, k):
                    steps.append((cfg, self.bad_configs[dst_id], mover))
        return steps

    def has_admissible_lift(
        self,
        source: Config,
        deleted_target: Config,
        k: int,
        min_fc: int,
    ) -> bool:
        if source in self.good_cycle:
            for x in range(cup2M(self.n, k)):
                lifted = insert_value(deleted_target, k, x)
                if lifted == source and self.fc_all[source] >= min_fc:
                    return True
            return False

        target_comps: Set[int] = set()
        for x in range(cup2M(self.n, k)):
            lifted = insert_value(deleted_target, k, x)
            if self.fc_all[lifted] < min_fc:
                continue
            if lifted == source:
                return True
            if lifted in self.good_cycle:
                continue
            target_comps.add(self.comp_of[self.bad_id[lifted]])

        if not target_comps:
            return False

        self.ensure_scc()
        source_comp = self.comp_of[self.bad_id[source]]
        return source_comp in self._reverse_reachable_comps(target_comps)


def find_first_counterexample(
    big: TpGraph, small: TpGraph, k: int
) -> Tuple[List[Tuple[Config, Config, int]], int, Optional[SeamCounterexample]]:
    seam_steps = small.seam_steps(k)
    lifts_checked = 0

    for c_prime, d_prime, mover_prime in seam_steps:
        target_fc = small.fc_all[d_prime]
        for inserted_value in range(cup2M(big.n, k)):
            c = insert_value(c_prime, k, inserted_value)
            lifts_checked += 1
            if big.has_admissible_lift(c, d_prime, k, target_fc):
                continue
            return seam_steps, lifts_checked, SeamCounterexample(
                k=k,
                mover_prime=mover_prime,
                c_prime=c_prime,
                d_prime=d_prime,
                inserted_value=inserted_value,
                c=c,
                fc_c=big.fc_all[c],
                fc_c_prime=small.fc_all[c_prime],
                fc_d_prime=target_fc,
                c_is_bad=c not in big.good_cycle,
            )

    return seam_steps, lifts_checked, None


def global_source_transport_check(
    big: TpGraph, small: TpGraph, k: int, max_print: int = 5
) -> Tuple[int, List[Tuple[Config, int, int]]]:
    violations: List[Tuple[Config, int, int]] = []
    for cfg in big.all_configs:
        phi_big = big.phi_of(cfg)
        deleted = delete_config(cfg, k)
        phi_small = small.phi_of(deleted)
        if phi_small > phi_big:
            violations.append((cfg, phi_small, phi_big))
            if len(violations) >= max_print:
                break
    return len(big.all_configs), violations


def report_for_k(big: TpGraph, small: TpGraph, k: int) -> None:
    seam_steps, lifts_checked, counterexample = find_first_counterexample(big, small, k)

    print(f"=== n={big.n}, k={k} ===")
    print(f"size {small.n} seam TP-bad steps: {len(seam_steps)}")
    print(f"lift candidates checked: {lifts_checked}")
    if counterexample is None:
        print("per-step lifting counterexample: none found")
    else:
        print("per-step lifting counterexample: FOUND")
        print(f"  mover' = {counterexample.mover_prime}")
        print(f"  c' = {format_cfg(counterexample.c_prime)}  fc(c') = {counterexample.fc_c_prime}")
        print(f"  d' = {format_cfg(counterexample.d_prime)}  fc(d') = {counterexample.fc_d_prime}")
        print(
            f"  c  = {format_cfg(counterexample.c)}  "
            f"inserted={counterexample.inserted_value}  fc(c) = {counterexample.fc_c}  "
            f"bad={counterexample.c_is_bad}"
        )
        print("  no TP-reachable d at size 9 satisfies deleteConfig(d)=d' and fc(d)>=fc(d')")

    checked, violations = global_source_transport_check(big, small, k)
    print(f"global source_transport checks: {checked}")
    if not violations:
        print("global inequality PhiFull(delete(c)) <= PhiFull(c): HOLDS for all c")
    else:
        print(
            f"global inequality PhiFull(delete(c)) <= PhiFull(c): FAILS "
            f"({len(violations)} sample violation(s))"
        )
        for idx, (cfg, phi_small, phi_big) in enumerate(violations, start=1):
            print(
                f"  [{idx}] c={format_cfg(cfg)}  "
                f"PhiFull(delete(c))={phi_small} > PhiFull(c)={phi_big}"
            )
    print()


def parse_args(argv: Optional[Sequence[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=9, help="original ring size")
    parser.add_argument(
        "--ks",
        type=int,
        nargs="+",
        default=[4, 5],
        help="deletion sites k to check",
    )
    return parser.parse_args(argv)


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = parse_args(argv)
    if args.n < 5:
        raise SystemExit("n must be at least 5")

    t0 = time.time()
    big = TpGraph(args.n)
    small = TpGraph(args.n - 1)
    big.ensure_scc()
    small.ensure_scc()

    print(f"built n={args.n} TP graph in {big.build_time:.2f}s")
    print(f"built n={args.n - 1} TP graph in {small.build_time:.2f}s")
    print(f"good cycle counts: n={args.n} -> {len(big.good_cycle)}, n-1={args.n - 1} -> {len(small.good_cycle)}")
    print()

    for k in args.ks:
        report_for_k(big, small, k)

    print(f"elapsed: {time.time() - t0:.2f}s")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
