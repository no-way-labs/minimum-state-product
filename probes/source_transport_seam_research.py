#!/usr/bin/env python3
"""
Research script for the seam-lifting failure in LeanMn/Convergence/CPhiDelete.lean.

This script models the exact Lean semantics used by:
  - cup2System / cup2OutVal
  - badStep / cup2TpBadStepFwd / cup2TpReachable
  - cup2Fc
  - deleteConfig
  - the explicit good cycle from Cycle.lean

It supports three checks:

1. Enumerate seam TP-bad steps at size n-1 and test the claimed lifting property
   for every lift c with deleteConfig(c) = c'.
2. Summarize whether natural extra hypotheses eliminate the failures.
3. Compute PhiFull directly from the TP graph and test source_transport
   without any per-step lifting.
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


def build_system(n: int) -> Tuple[List[int], List]:
    if n < 4:
        raise ValueError("n must be at least 4")

    ms = [2] + [3] * (n - 2) + [2]

    def make_f(table):
        def f(left: int, self_val: int, right: int) -> int:
            return table[(left, self_val, right)]
        return f

    if n == 4:
        fs = [make_f(T_BOT), make_f(T_LOW), make_f(T_HIGH), make_f(T_TOP)]
    elif n == 5:
        fs = [make_f(T_BOT), make_f(T_LOW), make_f(T_MID), make_f(T_HIGH), make_f(T_TOP)]
    else:
        fs = [make_f(T_BOT), make_f(T_LOW)]
        for _ in range(2, n - 2):
            fs.append(make_f(T_MID))
        fs.append(make_f(T_HIGH))
        fs.append(make_f(T_TOP))
    return ms, fs


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


def frontier_bit(a: int, b: int) -> int:
    return 0 if a == b else 1


def fc(config: Config) -> int:
    n = len(config)
    return sum(frontier_bit(config[j], config[(j + 1) % n]) for j in range(n))


def exp2_count(config: Config) -> int:
    n = len(config)
    return sum(1 for j in range(2, n - 2) if config[j] == 2 and config[(j + 1) % n] != 2)


def int21_count(config: Config) -> int:
    n = len(config)
    return sum(1 for j in range(2, n - 2) if config[j] == 2 and config[(j + 1) % n] == 1)


def exp2_weight(config: Config) -> int:
    n = len(config)
    return sum(j for j in range(2, n - 2) if config[j] == 2 and config[(j + 1) % n] != 2)


def tp_triple(config: Config) -> TpTriple:
    return (exp2_count(config), int21_count(config), exp2_weight(config))


def delete_config(config: Config, k: int) -> Config:
    return config[:k] + config[k + 1 :]


def insert_value(config: Config, k: int, x: int) -> Config:
    return config[:k] + (x,) + config[k:]


def valid_sites(n: int) -> List[int]:
    return list(range(4, n - 3))


def no_deep_copy_pair(config: Config) -> bool:
    n = len(config)
    return all(config[k] != config[k - 1] and config[k] != config[k + 1] for k in valid_sites(n))


def format_cfg(config: Config) -> str:
    return "(" + ",".join(str(x) for x in config) + ")"


@dataclass(frozen=True)
class FailureInstance:
    n: int
    k: int
    mover_prime: int
    c_prime: Config
    d_prime: Config
    inserted_value: int
    c: Config
    c_bad: bool
    c_no_deep_copy: bool
    fc_c_prime: int
    fc_d_prime: int
    fc_c: int
    phi_c: Optional[int]
    phi_delete_c: Optional[int]
    one_step_exists: bool


class TpBadGraph:
    def __init__(self, n: int):
        self.n = n
        self.ms, self.fs = build_system(n)
        self.good_cycle = good_cycle_configs(n)
        self.all_configs: List[Config] = list(product(*(range(m) for m in self.ms)))
        self.fc_all: Dict[Config, int] = {cfg: fc(cfg) for cfg in self.all_configs}

        self.bad_configs: List[Config] = [cfg for cfg in self.all_configs if cfg not in self.good_cycle]
        self.bad_id: Dict[Config, int] = {cfg: idx for idx, cfg in enumerate(self.bad_configs)}
        self.tp_bad: Dict[Config, TpTriple] = {cfg: tp_triple(cfg) for cfg in self.bad_configs}

        self.out_edges: List[List[Tuple[int, int]]] = [[] for _ in self.bad_configs]
        self.rev_edges: List[List[int]] = [[] for _ in self.bad_configs]

        t0 = time.time()
        for src_id, cfg in enumerate(self.bad_configs):
            triple = self.tp_bad[cfg]
            for mover in range(n):
                left = cfg[(mover - 1) % n]
                self_val = cfg[mover]
                right = cfg[(mover + 1) % n]
                out = self.fs[mover](left, self_val, right)
                if out == self_val:
                    continue
                dst_list = list(cfg)
                dst_list[mover] = out
                dst = tuple(dst_list)
                dst_id = self.bad_id.get(dst)
                if dst_id is None:
                    continue
                if self.tp_bad[dst] != triple:
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

    def one_step_targets(self, cfg: Config) -> Set[Config]:
        if cfg in self.good_cycle:
            return {cfg}
        src_id = self.bad_id[cfg]
        targets = {cfg}
        for dst_id, _ in self.out_edges[src_id]:
            targets.add(self.bad_configs[dst_id])
        return targets

    def ensure_scc(self) -> None:
        if self._scc_ready:
            return

        n_bad = len(self.bad_configs)
        visited = [False] * n_bad
        order: List[int] = []

        for start in range(n_bad):
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

        self.comp_of = [-1] * n_bad
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
        for src in range(n_bad):
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
            raise RuntimeError("Condensation graph should be acyclic")

        comp_fc = [max(self.fc_all[self.bad_configs[node]] for node in nodes) for nodes in self.comp_nodes]
        self.phi_comp = comp_fc[:]
        for cid in reversed(topo):
            best = self.phi_comp[cid]
            for nxt in self.comp_succ[cid]:
                if self.phi_comp[nxt] > best:
                    best = self.phi_comp[nxt]
            self.phi_comp[cid] = best

        self.phi_bad = [self.phi_comp[self.comp_of[node]] for node in range(n_bad)]
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

    def has_admissible_lift(self, source: Config, deleted_target: Config, k: int) -> bool:
        deleted_fc = fc(deleted_target)
        if source in self.good_cycle:
            return any(insert_value(deleted_target, k, x) == source and self.fc_all[source] >= deleted_fc
                       for x in range(3))

        target_comps: Set[int] = set()
        for x in range(3):
            lifted = insert_value(deleted_target, k, x)
            if self.fc_all[lifted] < deleted_fc:
                continue
            if lifted == source:
                return True
            if lifted in self.good_cycle:
                continue
            target_comps.add(self.comp_of[self.bad_id[lifted]])

        if not target_comps:
            return False
        source_comp = self.comp_of[self.bad_id[source]]
        return source_comp in self._reverse_reachable_comps(target_comps)

    def has_one_step_admissible_lift(self, source: Config, deleted_target: Config, k: int) -> bool:
        targets = self.one_step_targets(source)
        threshold = fc(deleted_target)
        return any(delete_config(dst, k) == deleted_target and self.fc_all[dst] >= threshold for dst in targets)


def scan_seam_failures(n: int, k: int, include_phi: bool = False) -> Tuple[TpBadGraph, TpBadGraph, List[FailureInstance]]:
    if k not in valid_sites(n):
        raise ValueError(f"k={k} is not valid for n={n}")

    big = TpBadGraph(n)
    small = TpBadGraph(n - 1)
    big.ensure_scc()
    if include_phi:
        small.ensure_scc()

    failures: List[FailureInstance] = []
    c_bad_cache: Dict[Config, bool] = {}
    no_copy_cache: Dict[Config, bool] = {}

    for c_prime_id, c_prime in enumerate(small.bad_configs):
        for d_prime_id, mover_prime in small.out_edges[c_prime_id]:
            if mover_prime not in (k - 1, k):
                continue
            d_prime = small.bad_configs[d_prime_id]
            for x in range(3):
                c = insert_value(c_prime, k, x)
                if big.has_admissible_lift(c, d_prime, k):
                    continue
                c_bad = c_bad_cache.setdefault(c, c not in big.good_cycle)
                c_no_copy = no_copy_cache.setdefault(c, no_deep_copy_pair(c))
                phi_c = big.phi_of(c) if include_phi else None
                phi_delete_c = small.phi_of(c_prime) if include_phi else None
                failures.append(
                    FailureInstance(
                        n=n,
                        k=k,
                        mover_prime=mover_prime,
                        c_prime=c_prime,
                        d_prime=d_prime,
                        inserted_value=x,
                        c=c,
                        c_bad=c_bad,
                        c_no_deep_copy=c_no_copy,
                        fc_c_prime=small.fc_all[c_prime],
                        fc_d_prime=small.fc_all[d_prime],
                        fc_c=big.fc_all[c],
                        phi_c=phi_c,
                        phi_delete_c=phi_delete_c,
                        one_step_exists=big.has_one_step_admissible_lift(c, d_prime, k),
                    )
                )

    return big, small, failures


def summarize_failures(failures: Sequence[FailureInstance]) -> Dict[str, int]:
    return {
        "total_failures": len(failures),
        "failures_with_bad_c": sum(1 for f in failures if f.c_bad),
        "failures_with_good_c": sum(1 for f in failures if not f.c_bad),
        "failures_with_no_deep_copy_c": sum(1 for f in failures if f.c_no_deep_copy),
        "failures_with_fc_source_monotone": sum(1 for f in failures if f.fc_c_prime <= f.fc_c),
        "failures_with_one_step_lift": sum(1 for f in failures if f.one_step_exists),
        "failures_without_one_step_lift": sum(1 for f in failures if not f.one_step_exists),
        "failures_at_left_seam": sum(1 for f in failures if f.mover_prime == f.k - 1),
        "failures_at_right_seam": sum(1 for f in failures if f.mover_prime == f.k),
    }


def report_scan(n: int, k: int, max_print: int) -> int:
    t0 = time.time()
    big, small, failures = scan_seam_failures(n, k, include_phi=True)

    seam_step_count = 0
    for c_prime_id, _ in enumerate(small.bad_configs):
        for _, mover_prime in small.out_edges[c_prime_id]:
            if mover_prime in (k - 1, k):
                seam_step_count += 1

    print(f"=== Seam Scan n={n}, k={k} ===")
    print(f"build time n={n}: {big.build_time:.2f}s")
    print(f"build time n={n-1}: {small.build_time:.2f}s")
    print(f"seam TP-bad steps at size {n-1}: {seam_step_count}")
    print(f"failing lifted instances: {len(failures)}")

    summary = summarize_failures(failures)
    for key, value in summary.items():
        print(f"{key}: {value}")

    print()
    print("Sample failures:")
    for idx, failure in enumerate(sorted(failures, key=lambda f: (f.mover_prime, f.c_prime, f.inserted_value, f.c))[:max_print], start=1):
        print(f"[{idx}] mover'={failure.mover_prime} inserted={failure.inserted_value}")
        print(f"    c'={format_cfg(failure.c_prime)} fc={failure.fc_c_prime}")
        print(f"    d'={format_cfg(failure.d_prime)} fc={failure.fc_d_prime}")
        print(f"    c ={format_cfg(failure.c)} fc={failure.fc_c} bad={failure.c_bad} noDeepCopy={failure.c_no_deep_copy}")
        if failure.phi_c is not None and failure.phi_delete_c is not None:
            print(f"    Phi(delete(c))={failure.phi_delete_c}  Phi(c)={failure.phi_c}")
        print(f"    one-step lift exists: {failure.one_step_exists}")

    print(f"elapsed: {time.time() - t0:.2f}s")
    print()
    return 0


def report_known_counterexamples(max_print: int) -> int:
    for n, k in [(10, 4), (10, 5), (11, 5)]:
        report_scan(n, k, max_print)
    return 0


def report_scan_all_k(n: int) -> int:
    print(f"=== Seam Scan All k for n={n} ===")
    for k in valid_sites(n):
        _, _, failures = scan_seam_failures(n, k, include_phi=False)
        nocopy = sum(1 for f in failures if f.c_no_deep_copy)
        print(f"k={k}: failures={len(failures)} nocopy_failures={nocopy}")
    print()
    return 0


def direct_source_transport_check(n: int, active_only: bool = False, max_print: int = 10) -> int:
    t0 = time.time()
    big = TpBadGraph(n)
    small = TpBadGraph(n - 1)
    big.ensure_scc()
    small.ensure_scc()

    ks = valid_sites(n)
    checked = 0
    failures = []
    for cfg in big.all_configs:
        if active_only and not no_deep_copy_pair(cfg):
            continue
        phi_big = big.phi_of(cfg)
        for k in ks:
            deleted = delete_config(cfg, k)
            phi_small = small.phi_of(deleted)
            checked += 1
            if phi_small > phi_big:
                failures.append((cfg, k, phi_small, phi_big))
                if len(failures) >= max_print:
                    break
        if len(failures) >= max_print:
            break

    label = "active-only" if active_only else "all-config"
    print(f"=== Direct Phi Check n={n} ({label}) ===")
    print(f"build time n={n}: {big.build_time:.2f}s")
    print(f"build time n={n-1}: {small.build_time:.2f}s")
    print(f"checked pairs (c,k): {checked}")
    print(f"violations: {len(failures)}")
    for idx, (cfg, k, phi_small, phi_big) in enumerate(failures, start=1):
        print(f"[{idx}] k={k} cfg={format_cfg(cfg)} Phi(delete(c))={phi_small} > Phi(c)={phi_big}")
    print(f"elapsed: {time.time() - t0:.2f}s")
    print()
    return 0 if not failures else 1


def report_direct_suite(max_print: int) -> int:
    rc = 0
    for n in (10, 11):
        rc |= direct_source_transport_check(n, active_only=False, max_print=max_print)
        rc |= direct_source_transport_check(n, active_only=True, max_print=max_print)
    return rc


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)

    scan = sub.add_parser("scan", help="scan seam TP-bad steps for a fixed (n,k)")
    scan.add_argument("--n", type=int, required=True, help="original size n")
    scan.add_argument("--k", type=int, required=True, help="deleted site k")
    scan.add_argument("--max-print", type=int, default=10, help="how many failures to print")

    known = sub.add_parser("known", help="scan the known failing pairs (10,4), (10,5), (11,5)")
    known.add_argument("--max-print", type=int, default=5, help="how many failures to print per pair")

    scan_all = sub.add_parser("scan-all-k", help="scan every valid deletion site k for a fixed n")
    scan_all.add_argument("--n", type=int, required=True, help="original size n")

    direct = sub.add_parser("direct", help="check Phi(delete(c)) <= Phi(c) directly for a fixed n")
    direct.add_argument("--n", type=int, required=True, help="original size n")
    direct.add_argument("--active-only", action="store_true", help="restrict to source configs with no deep copy pair")
    direct.add_argument("--max-print", type=int, default=10, help="how many violations to print")

    suite = sub.add_parser("suite", help="run the known seam scans plus direct Phi checks for n=10,11")
    suite.add_argument("--max-print", type=int, default=5, help="how many failures to print per section")

    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = build_arg_parser()
    args = parser.parse_args(argv)

    if args.cmd == "scan":
        return report_scan(args.n, args.k, args.max_print)
    if args.cmd == "known":
        return report_known_counterexamples(args.max_print)
    if args.cmd == "scan-all-k":
        return report_scan_all_k(args.n)
    if args.cmd == "direct":
        return direct_source_transport_check(args.n, active_only=args.active_only, max_print=args.max_print)
    if args.cmd == "suite":
        rc = report_known_counterexamples(args.max_print)
        rc |= report_direct_suite(args.max_print)
        return rc
    raise AssertionError("unreachable")


if __name__ == "__main__":
    raise SystemExit(main())
