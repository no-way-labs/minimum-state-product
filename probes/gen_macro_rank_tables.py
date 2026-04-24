#!/usr/bin/env python3
"""
Generate small diagnostic rank tables for sampled plateau-family blocks under the
 current MVP state:

   boundary12 + first 2 omitted-core symbols + monoTag(rest)

This does not yet prove the full constant layer, but it gives us concrete data
for the next Lean step: whether we can tabulate a finite rank on the sampled
hard plateau blocks and how large those blocks are.
"""

from __future__ import annotations

from collections import Counter, defaultdict, deque
from functools import lru_cache
from itertools import product
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from probes.phifull_verify_lean_contract import Cup2Model


def mono_tag(core: tuple[int, ...]) -> int | None:
    if not core:
        return None
    return core[0] if all(x == core[0] for x in core) else None


def boundary6(cfg: tuple[int, ...]) -> tuple[int, ...]:
    n = len(cfg)
    return (cfg[0], cfg[1], cfg[2], cfg[n - 3], cfg[n - 2], cfg[n - 1])


def sig2(cfg: tuple[int, ...]) -> tuple[int | None, ...]:
    n = len(cfg)
    mid = cfg[6 : n - 6]
    extra = list(mid[:2])
    while len(extra) < 2:
        extra.append(9)
    rest = mid[2:]
    return (*cfg[:6], *cfg[n - 6 :], *extra, mono_tag(rest))


class BlockAnalyzer:
    def __init__(self, n: int, families: tuple[tuple[int, ...], ...]):
        self.n = n
        self.families = families
        self.model = Cup2Model(n)
        self.good = self.model.good_cycle_set()
        self.free = [i for i in range(n) if i not in {0, 1, 2, n - 3, n - 2, n - 1}]

    @lru_cache(None)
    def slice_data(self, b6: tuple[int, ...]):
        states = []
        for vals in product(range(3), repeat=len(self.free)):
            cfg = [None] * self.n
            cfg[0], cfg[1], cfg[2], cfg[self.n - 3], cfg[self.n - 2], cfg[self.n - 1] = b6
            for i, v in zip(self.free, vals):
                cfg[i] = v
            states.append(tuple(cfg))

        idx_of = {cfg: i for i, cfg in enumerate(states)}
        fc_vals = [self.model.fc(cfg) for cfg in states]
        tp_vals = [self.model.tp(cfg) for cfg in states]
        bad_flags = [self.model.encode(cfg) not in self.good for cfg in states]
        fixed_succ = [[] for _ in states]
        indeg = [0] * len(states)
        out_targets = [set() for _ in states]
        seg_fc = fc_vals[:]

        for i, cfg in enumerate(states):
            if not bad_flags[i]:
                continue
            for p in range(self.n):
                if not self.model.privileged(cfg, p):
                    continue
                dst = self.model.fire(cfg, p)
                if self.model.encode(dst) in self.good:
                    continue
                if self.model.tp(dst) != tp_vals[i]:
                    continue
                if boundary6(dst) == b6:
                    j = idx_of[dst]
                    fixed_succ[i].append(j)
                    indeg[j] += 1
                else:
                    seg_fc[i] = max(seg_fc[i], self.model.fc(dst))
                    out_targets[i].add(dst)

        q = deque(i for i, d in enumerate(indeg) if d == 0)
        topo: list[int] = []
        while q:
            i = q.popleft()
            topo.append(i)
            for j in fixed_succ[i]:
                indeg[j] -= 1
                if indeg[j] == 0:
                    q.append(j)

        assert len(topo) == len(states)

        for i in reversed(topo):
            for j in fixed_succ[i]:
                if seg_fc[j] > seg_fc[i]:
                    seg_fc[i] = seg_fc[j]
                out_targets[i].update(out_targets[j])

        corr = {sig2(cfg): seg_fc[i] - fc_vals[i] for i, cfg in enumerate(states)}
        return states, out_targets, corr

    def quotient_graph(self):
        nodes: set[tuple[int | None, ...]] = set()
        edges: dict[tuple[int | None, ...], set[tuple[int | None, ...]]] = defaultdict(set)
        for b6 in self.families:
            states, out_targets, corr = self.slice_data(b6)
            for cfg, targets in zip(states, out_targets):
                s = sig2(cfg)
                if corr[s] != 2:
                    continue
                nodes.add(s)
                for dst in targets:
                    dst_b6 = boundary6(dst)
                    if dst_b6 not in self.families:
                        continue
                    _, _, dst_corr = self.slice_data(dst_b6)
                    ts = sig2(dst)
                    if dst_corr[ts] == 2:
                        edges[s].add(ts)
                        nodes.add(ts)
        return nodes, edges

    def quotient_rank_stats(self):
        nodes, edges = self.quotient_graph()
        ordered = list(nodes)
        idx = {s: i for i, s in enumerate(ordered)}
        adj = [[] for _ in ordered]
        rev = [[] for _ in ordered]
        for s, ts in edges.items():
            a = idx[s]
            for t in ts:
                b = idx[t]
                if a != b:
                    adj[a].append(b)
                    rev[b].append(a)

        seen = [False] * len(ordered)
        order: list[int] = []
        for start in range(len(ordered)):
            if seen[start]:
                continue
            stack = [(start, 0)]
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

        comp = [-1] * len(ordered)
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

        sizes = sorted(Counter(comp)[c] for c in set(comp) if Counter(comp)[c] > 1)
        return len(ordered), sum(len(v) for v in edges.values()), sizes


def main() -> None:
    n = 15
    samples = {
        "2fam0": ((0, 0, 0, 0, 0, 0), (0, 0, 0, 1, 0, 0)),
        "3fam0": ((0, 0, 0, 0, 2, 0), (0, 0, 0, 1, 2, 0), (0, 0, 0, 2, 2, 0)),
    }
    for name, fams in samples.items():
        print(name)
        analyzer = BlockAnalyzer(n, fams)
        nodes, edges = analyzer.quotient_graph()
        print(f"  quotient nodes = {len(nodes)}")
        print(f"  quotient edges = {sum(len(v) for v in edges.values())}")
        print(f"  SCC sizes = {analyzer.quotient_rank_stats()[2]}")


if __name__ == "__main__":
    main()
