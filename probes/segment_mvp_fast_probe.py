#!/usr/bin/env python3
"""
Fast MVP probe on sampled hard plateau SCCs.

Instead of recomputing the slice dynamics for every k, this script:
1. builds the raw correction-2 plateau graph once for a chosen family block,
2. quotients that raw graph by summary signatures of the form
     boundary12 + first k omitted-core symbols + monoTag(rest),
3. reports SCC sizes of the quotient graph.
"""

from __future__ import annotations

from collections import defaultdict, deque, Counter
from functools import lru_cache
from itertools import product
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from probes.phifull_verify_lean_contract import Cup2Model


def boundary6(cfg: tuple[int, ...]) -> tuple[int, ...]:
    n = len(cfg)
    return (cfg[0], cfg[1], cfg[2], cfg[n - 3], cfg[n - 2], cfg[n - 1])


def mono_tag(core: tuple[int, ...]) -> int | None:
    if not core:
        return None
    return core[0] if all(x == core[0] for x in core) else None


def make_sig_plus_mono(k: int):
    def sig(cfg: tuple[int, ...]) -> tuple[int | None, ...]:
        n = len(cfg)
        mid = cfg[6 : n - 6]
        extra = list(mid[:k])
        while len(extra) < k:
            extra.append(9)
        rest = mid[k:]
        return (*cfg[:6], *cfg[n - 6 :], *extra, mono_tag(rest))

    return sig


class RawPlateauBlock:
    def __init__(self, n: int, families: tuple[tuple[int, ...], ...]):
        self.n = n
        self.families = families
        self.model = Cup2Model(n)
        self.good = self.model.good_cycle_set()
        self.free = [i for i in range(n) if i not in {0, 1, 2, n - 3, n - 2, n - 1}]

        self.nodes: list[tuple[int, ...]] = []
        self.edges: list[tuple[int, int]] = []
        self._build()

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

        corr = {cfg: seg_fc[i] - fc_vals[i] for i, cfg in enumerate(states)}
        return states, out_targets, corr

    def _build(self) -> None:
        idx_of: dict[tuple[int, ...], int] = {}
        for b6 in self.families:
            states, _, corr = self.slice_data(b6)
            for cfg in states:
                if corr[cfg] == 2:
                    idx_of[cfg] = len(self.nodes)
                    self.nodes.append(cfg)

        for b6 in self.families:
            states, out_targets, corr = self.slice_data(b6)
            for cfg, targets in zip(states, out_targets):
                if corr[cfg] != 2:
                    continue
                a = idx_of[cfg]
                for dst in targets:
                    if boundary6(dst) not in self.families:
                        continue
                    _, _, dst_corr = self.slice_data(boundary6(dst))
                    if dst_corr.get(dst) == 2:
                        b = idx_of[dst]
                        if a != b:
                            self.edges.append((a, b))

    def quotient_scc_sizes(self, k: int) -> tuple[int, int, list[int]]:
        sigf = make_sig_plus_mono(k)
        sig_to_idx: dict[tuple[int | None, ...], int] = {}
        qedges: dict[int, set[int]] = defaultdict(set)

        for cfg in self.nodes:
            sig = sigf(cfg)
            sig_to_idx.setdefault(sig, len(sig_to_idx))
        for a, b in self.edges:
            sa = sig_to_idx[sigf(self.nodes[a])]
            sb = sig_to_idx[sigf(self.nodes[b])]
            if sa != sb:
                qedges[sa].add(sb)

        n = len(sig_to_idx)
        adj = [[] for _ in range(n)]
        rev = [[] for _ in range(n)]
        for a, bs in qedges.items():
            for b in bs:
                adj[a].append(b)
                rev[b].append(a)

        seen = [False] * n
        order: list[int] = []
        for start in range(n):
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

        sizes = sorted(Counter(comp)[c] for c in set(comp) if Counter(comp)[c] > 1)
        return n, sum(len(v) for v in qedges.values()), sizes


def main() -> None:
    n = 15
    families2 = ((0, 0, 0, 0, 0, 0), (0, 0, 0, 1, 0, 0))
    families3 = ((0, 0, 0, 0, 2, 0), (0, 0, 0, 1, 2, 0), (0, 0, 0, 2, 2, 0))
    for name, fams in [("2fam", families2), ("3fam", families3)]:
        print(name)
        block = RawPlateauBlock(n, fams)
        print(f"  raw nodes = {len(block.nodes)}, raw edges = {len(block.edges)}")
        for k in [0, 1, 2, 3, 4, 5, 6]:
            print(f"  k={k}: {block.quotient_scc_sizes(k)}")


if __name__ == "__main__":
    main()
