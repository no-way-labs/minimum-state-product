#!/usr/bin/env python3
"""
Recompute cup2PhiFull from the exact Lean contract:
- endpoint/interior moduli from System.lean
- boundary/interior tables from Tables.lean
- good-cycle membership from Cycle.lean
- TP invariant and TP-preserving bad reachability from TP.lean / PhiFullTP.lean

This is intentionally separate from earlier scripts whose semantics drifted.
"""

from __future__ import annotations

from collections import Counter, defaultdict, deque
from dataclasses import dataclass
from typing import Iterable


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
    (0, 0, 0): 0, (0, 0, 1): 0, (0, 1, 0): 0, (0, 1, 1): 0,
    (0, 2, 0): 0, (0, 2, 1): 0, (1, 0, 0): 1, (1, 0, 1): 1,
    (1, 1, 0): 1, (1, 1, 1): 2, (1, 2, 0): 0, (1, 2, 1): 2,
    (2, 0, 0): 0, (2, 0, 1): 2, (2, 1, 0): 0, (2, 1, 1): 2,
    (2, 2, 0): 2, (2, 2, 1): 2,
}

T_TOP = {
    (0, 0, 0): 0, (0, 0, 1): 0, (0, 1, 0): 0, (0, 1, 1): 0,
    (1, 0, 0): 0, (1, 0, 1): 1, (1, 1, 0): 1, (1, 1, 1): 1,
    (2, 0, 0): 1, (2, 0, 1): 1, (2, 1, 0): 1, (2, 1, 1): 1,
}


def moduli(n: int) -> list[int]:
    return [2] + [3] * (n - 2) + [2]


def cycle_len(n: int) -> int:
    return 3 * n - 2


def cycle_val(n: int, t: int, j: int) -> int:
    if t < n:
        return 1 if j < t else 0
    if t < 2 * n - 2:
        return 1 if j < 2 * n - 1 - t else (2 if j < n - 1 else 1)
    if t == 2 * n - 2:
        return 1 if j == 0 else (2 if j < n - 1 else 1)
    k = t - (2 * n - 2)
    if k == 0:
        return 1 if j == 0 else (2 if j < n - 1 else 1)
    return 0 if j < k else (2 if j < n - 1 else 1)


def cycle_cfg(n: int, t: int) -> tuple[int, ...]:
    return tuple(cycle_val(n, t, j) for j in range(n))


@dataclass
class Cup2Model:
    n: int

    def __post_init__(self) -> None:
        self.radices = moduli(self.n)
        self.weights = [1] * self.n
        prod = 1
        for i in range(self.n - 1, -1, -1):
            self.weights[i] = prod
            prod *= self.radices[i]
        self.num_configs = prod

    def encode(self, cfg: tuple[int, ...]) -> int:
        return sum(v * w for v, w in zip(cfg, self.weights))

    def decode(self, idx: int) -> tuple[int, ...]:
        vals = [0] * self.n
        rem = idx
        for i, base in enumerate(self.radices):
            w = self.weights[i]
            vals[i] = rem // w
            rem %= w
            assert vals[i] < base
        return tuple(vals)

    def out_val(self, cfg: tuple[int, ...], i: int) -> int:
        l = cfg[(i - 1) % self.n]
        s = cfg[i]
        r = cfg[(i + 1) % self.n]
        if i == 0:
            return T_BOT[(l, s, r)]
        if i == 1:
            return T_LOW[(l, s, r)]
        if i + 1 == self.n:
            return T_TOP[(l, s, r)]
        if i + 2 == self.n:
            return T_HIGH[(l, s, r)]
        return T_MID[(l, s, r)]

    def privileged(self, cfg: tuple[int, ...], i: int) -> bool:
        return self.out_val(cfg, i) != cfg[i]

    def fire(self, cfg: tuple[int, ...], i: int) -> tuple[int, ...]:
        out = self.out_val(cfg, i)
        if out == cfg[i]:
            return cfg
        vals = list(cfg)
        vals[i] = out
        return tuple(vals)

    def fc(self, cfg: tuple[int, ...]) -> int:
        return sum(1 for i in range(self.n) if cfg[i] != cfg[(i + 1) % self.n])

    def tp(self, cfg: tuple[int, ...]) -> tuple[int, int, int]:
        exp2 = 0
        int21 = 0
        weight = 0
        for j in range(2, self.n - 2):
            a = cfg[j]
            b = cfg[j + 1]
            if a == 2 and b != 2:
                exp2 += 1
                weight += j
                if b == 1:
                    int21 += 1
        return (exp2, int21, weight)

    def good_cycle_set(self) -> set[int]:
        return {self.encode(cycle_cfg(self.n, t)) for t in range(cycle_len(self.n))}

    def single_privileged_set(self) -> set[int]:
        out = set()
        for idx in range(self.num_configs):
            cfg = self.decode(idx)
            if sum(1 for i in range(self.n) if self.privileged(cfg, i)) == 1:
                out.add(idx)
        return out


def kosaraju_scc(adj: list[list[int]], rev: list[list[int]]) -> tuple[list[int], int]:
    n = len(adj)
    seen = [False] * n
    order: list[int] = []

    for start in range(n):
        if seen[start]:
            continue
        stack: list[tuple[int, int]] = [(start, 0)]
        seen[start] = True
        while stack:
            node, pos = stack[-1]
            if pos < len(adj[node]):
                nxt = adj[node][pos]
                stack[-1] = (node, pos + 1)
                if not seen[nxt]:
                    seen[nxt] = True
                    stack.append((nxt, 0))
            else:
                order.append(node)
                stack.pop()

    comp = [-1] * n
    comp_count = 0
    for start in reversed(order):
        if comp[start] != -1:
            continue
        stack = [start]
        comp[start] = comp_count
        while stack:
            node = stack.pop()
            for nxt in rev[node]:
                if comp[nxt] == -1:
                    comp[nxt] = comp_count
                    stack.append(nxt)
        comp_count += 1
    return comp, comp_count


def topo_order(succs: list[set[int]]) -> list[int]:
    indeg = [0] * len(succs)
    for outs in succs:
        for dst in outs:
            indeg[dst] += 1
    q = deque(i for i, d in enumerate(indeg) if d == 0)
    out: list[int] = []
    while q:
        node = q.popleft()
        out.append(node)
        for dst in succs[node]:
            indeg[dst] -= 1
            if indeg[dst] == 0:
                q.append(dst)
    assert len(out) == len(succs)
    return out


def compute_phi_full(model: Cup2Model) -> dict[str, object]:
    good = model.good_cycle_set()
    cfgs = [model.decode(idx) for idx in range(model.num_configs)]
    fc_vals = [model.fc(cfg) for cfg in cfgs]
    tp_vals = [model.tp(cfg) for cfg in cfgs]

    bad_global = [idx for idx in range(model.num_configs) if idx not in good]
    bad_to_local = {idx: j for j, idx in enumerate(bad_global)}

    adj: list[list[int]] = [[] for _ in bad_global]
    rev: list[list[int]] = [[] for _ in bad_global]

    for src_global in bad_global:
        src_local = bad_to_local[src_global]
        cfg = cfgs[src_global]
        src_tp = tp_vals[src_global]
        for i in range(model.n):
            dst_val = model.out_val(cfg, i)
            if dst_val == cfg[i]:
                continue
            dst_cfg = list(cfg)
            dst_cfg[i] = dst_val
            dst_global = model.encode(tuple(dst_cfg))
            if dst_global in good:
                continue
            if tp_vals[dst_global] != src_tp:
                continue
            dst_local = bad_to_local[dst_global]
            adj[src_local].append(dst_local)
            rev[dst_local].append(src_local)

    comp, comp_count = kosaraju_scc(adj, rev)
    comp_fc = [0] * comp_count
    comp_succs = [set() for _ in range(comp_count)]

    for node_local, node_global in enumerate(bad_global):
        c = comp[node_local]
        comp_fc[c] = max(comp_fc[c], fc_vals[node_global])
        for dst_local in adj[node_local]:
            d = comp[dst_local]
            if c != d:
                comp_succs[c].add(d)

    order = topo_order(comp_succs)
    comp_phi = comp_fc[:]
    for c in reversed(order):
        for d in comp_succs[c]:
            if comp_phi[d] > comp_phi[c]:
                comp_phi[c] = comp_phi[d]

    phi = fc_vals[:]
    for node_local, node_global in enumerate(bad_global):
        phi[node_global] = comp_phi[comp[node_local]]

    return {
        "cfgs": cfgs,
        "good": good,
        "fc": fc_vals,
        "tp": tp_vals,
        "phi": phi,
        "bad_global": bad_global,
        "adj": adj,
        "components": comp_count,
    }


def summarize_correction(model: Cup2Model, data: dict[str, object]) -> None:
    cfgs = data["cfgs"]
    good = data["good"]
    fc_vals = data["fc"]
    phi_vals = data["phi"]
    bad_global = data["bad_global"]

    deltas = [phi_vals[idx] - fc_vals[idx] for idx in bad_global]
    delta_counter = Counter(deltas)
    print(f"  bad configs: {len(bad_global)}")
    print(f"  SCCs in TP-bad graph: {data['components']}")
    print(f"  phi-fc distribution on bad configs: {dict(sorted(delta_counter.items()))}")
    max_idx = max(bad_global, key=lambda idx: phi_vals[idx] - fc_vals[idx])
    print(
        "  max correction example:",
        cfgs[max_idx],
        f"(fc={fc_vals[max_idx]}, phi={phi_vals[max_idx]}, phi-fc={phi_vals[max_idx] - fc_vals[max_idx]})",
    )

    single_priv = model.single_privileged_set()
    extra_single = sorted(single_priv - good)
    missing_single = sorted(good - single_priv)
    print(f"  good-cycle size: {len(good)}")
    print(f"  single-privileged size: {len(single_priv)}")
    print(f"  single-privileged but not on good cycle: {len(extra_single)}")
    print(f"  good-cycle but not single-privileged: {len(missing_single)}")
    if extra_single:
        print(f"    example extra-single: {cfgs[extra_single[0]]}")
    if missing_single:
        print(f"    example missing-single: {cfgs[missing_single[0]]}")

    by_boundary: dict[tuple[int, ...], set[int]] = defaultdict(set)
    for idx in bad_global:
        cfg = cfgs[idx]
        b6 = (cfg[0], cfg[1], cfg[2], cfg[model.n - 3], cfg[model.n - 2], cfg[model.n - 1])
        by_boundary[b6].add(phi_vals[idx] - fc_vals[idx])

    nonfunctional = {b6: vals for b6, vals in by_boundary.items() if len(vals) > 1}
    print(f"  boundary-6 determines phi-fc on bad configs? {not nonfunctional}")
    if nonfunctional:
        b6, vals = next(iter(nonfunctional.items()))
        print(f"    counterexample boundary-6: {b6} -> {sorted(vals)}")
        bucket_example: dict[int, tuple[int, ...]] = {}
        for idx in bad_global:
            cfg = cfgs[idx]
            cur_b6 = (cfg[0], cfg[1], cfg[2], cfg[model.n - 3], cfg[model.n - 2], cfg[model.n - 1])
            if cur_b6 == b6:
                bucket_example.setdefault(phi_vals[idx] - fc_vals[idx], cfg)
        for value in sorted(bucket_example):
            print(f"      correction {value}: {bucket_example[value]}")

    delta1 = sorted(b6 for b6, vals in by_boundary.items() if vals == {1})
    print(f"  boundary-6 classes with correction 1: {len(delta1)}")
    if delta1:
        print(f"    first five: {delta1[:5]}")
        old_delta_ok = all(b6[0] == 1 and b6[1] == 2 and b6[5] == 1 for b6 in delta1)
        with_c2_ok = all(b6[0] == 1 and b6[1] == 2 and b6[2] == 0 and b6[5] == 1 for b6 in delta1)
        print(f"  all correction-1 boundaries satisfy old delta condition? {old_delta_ok}")
        print(f"  all correction-1 boundaries satisfy c0=1,c1=2,c2=0,cN1=1? {with_c2_ok}")

    old_delta = [
        idx for idx in bad_global
        if cfgs[idx][0] == 1 and cfgs[idx][1] == 2 and cfgs[idx][model.n - 1] == 1
    ]
    old_delta_dist = Counter(phi_vals[idx] - fc_vals[idx] for idx in old_delta)
    print(f"  old-delta candidate count: {len(old_delta)}")
    print(f"  old-delta correction distribution: {dict(sorted(old_delta_dist.items()))}")


def main(ns: Iterable[int]) -> None:
    for n in ns:
        print("=" * 72)
        print(f"n = {n}")
        model = Cup2Model(n)
        data = compute_phi_full(model)
        summarize_correction(model, data)


if __name__ == "__main__":
    main([9, 10, 11])
