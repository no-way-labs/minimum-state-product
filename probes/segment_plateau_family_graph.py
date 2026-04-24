#!/usr/bin/env python3
"""
Build the correction-2 boundary-family graph for the one-segment macro potential.

Nodes are boundary-6 classes (c0,c1,c2,c[n-3],c[n-2],c[n-1]).
An edge A -> B means: there exists a source config in family A with segment
correction 2 that reaches some target config in family B whose summary-state
correction is also 2.

This is the outer plateau structure we need before looking for an inner rank.
"""

from __future__ import annotations

from collections import Counter, defaultdict, deque
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


def summary_sig(cfg: tuple[int, ...]) -> tuple[int | None, ...]:
    n = len(cfg)
    return (*cfg[:6], *cfg[n - 6 :], mono_tag(cfg[6 : n - 6]))


def boundary6(cfg: tuple[int, ...]) -> tuple[int, ...]:
    n = len(cfg)
    return (cfg[0], cfg[1], cfg[2], cfg[n - 3], cfg[n - 2], cfg[n - 1])


def all_boundary6_classes() -> list[tuple[int, ...]]:
    out = []
    for c0 in [0, 1]:
        for c1 in [0, 1, 2]:
            for c2 in [0, 1, 2]:
                for cn3 in [0, 1, 2]:
                    for cn2 in [0, 1, 2]:
                        for cn1 in [0, 1]:
                            out.append((c0, c1, c2, cn3, cn2, cn1))
    return out


class FamilyGraphBuilder:
    def __init__(self, n: int):
        self.n = n
        self.model = Cup2Model(n)
        self.good = self.model.good_cycle_set()
        self.free = [i for i in range(n) if i not in {0, 1, 2, n - 3, n - 2, n - 1}]
        self.classes = all_boundary6_classes()

    def iter_slice_states(self, b6: tuple[int, ...]):
        for vals in product(range(3), repeat=len(self.free)):
            cfg = [None] * self.n
            cfg[0], cfg[1], cfg[2], cfg[self.n - 3], cfg[self.n - 2], cfg[self.n - 1] = b6
            for i, v in zip(self.free, vals):
                cfg[i] = v
            yield tuple(cfg)

    def slice_segment_data(
        self, b6: tuple[int, ...]
    ) -> tuple[list[tuple[int, ...]], list[int], list[set[tuple[int, ...]]]]:
        states = list(self.iter_slice_states(b6))
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
                    dst_fc = self.model.fc(dst)
                    if dst_fc > seg_fc[i]:
                        seg_fc[i] = dst_fc
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

        return states, seg_fc, out_targets

    def build_summary_correction(self) -> dict[tuple[int | None, ...], int]:
        summary_corr: dict[tuple[int | None, ...], int] = {}
        for idx, b6 in enumerate(self.classes, start=1):
            states, seg_fc, _ = self.slice_segment_data(b6)
            for cfg, seg in zip(states, seg_fc):
                sig = summary_sig(cfg)
                d = seg - self.model.fc(cfg)
                prev = summary_corr.get(sig)
                if prev is None:
                    summary_corr[sig] = d
                elif prev != d:
                    raise RuntimeError(("summary correction mismatch", b6, sig, prev, d))
            if idx % 50 == 0:
                print(f"pass1 processed {idx} / {len(self.classes)} slices")
        return summary_corr

    def build_family_graph(
        self, summary_corr: dict[tuple[int | None, ...], int]
    ) -> tuple[dict[tuple[int, ...], set[tuple[int, ...]]], set[tuple[int, ...]]]:
        family_edges: dict[tuple[int, ...], set[tuple[int, ...]]] = defaultdict(set)
        corr2_families: set[tuple[int, ...]] = set()

        for idx, b6 in enumerate(self.classes, start=1):
            states, seg_fc, out_targets = self.slice_segment_data(b6)
            corr_here = False
            for cfg, seg, targets in zip(states, seg_fc, out_targets):
                src_corr = seg - self.model.fc(cfg)
                if src_corr != 2:
                    continue
                corr_here = True
                for dst in targets:
                    if summary_corr[summary_sig(dst)] == 2:
                        family_edges[b6].add(boundary6(dst))
            if corr_here:
                corr2_families.add(b6)
            if idx % 50 == 0:
                print(f"pass2 processed {idx} / {len(self.classes)} slices")
        return family_edges, corr2_families


def topo_stats(graph: dict[tuple[int, ...], set[tuple[int, ...]]], nodes: set[tuple[int, ...]]):
    indeg = {node: 0 for node in nodes}
    for src in nodes:
        for dst in graph.get(src, set()):
            if dst != src:
                indeg[dst] += 1
    q = deque(node for node, d in indeg.items() if d == 0)
    seen = 0
    while q:
        node = q.popleft()
        seen += 1
        for dst in graph.get(node, set()):
            if dst == node:
                continue
            indeg[dst] -= 1
            if indeg[dst] == 0:
                q.append(dst)
    return seen == len(nodes), seen, len(nodes)


def kosaraju_scc(graph: dict[tuple[int, ...], set[tuple[int, ...]]], nodes: set[tuple[int, ...]]):
    ordered = list(nodes)
    idx = {node: i for i, node in enumerate(ordered)}
    rev = [[] for _ in ordered]
    adj = [[] for _ in ordered]
    for src in ordered:
        a = idx[src]
        for dst in graph.get(src, set()):
            if dst == src:
                continue
            b = idx[dst]
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

    members: list[list[tuple[int, ...]]] = [[] for _ in range(comp_count)]
    for node, c in enumerate(comp):
        members[c].append(ordered[node])

    cond_edges = defaultdict(set)
    for src in ordered:
        a = comp[idx[src]]
        for dst in graph.get(src, set()):
            if dst == src:
                continue
            b = comp[idx[dst]]
            if a != b:
                cond_edges[a].add(b)

    return members, cond_edges


def main() -> None:
    n = 14
    builder = FamilyGraphBuilder(n)
    summary_corr = builder.build_summary_correction()
    print(f"summary states: {len(summary_corr)}")
    print(f"summary correction distribution: {Counter(summary_corr.values())}")

    family_edges, corr2_families = builder.build_family_graph(summary_corr)
    edge_count = sum(len(v) for v in family_edges.values())
    print(f"correction-2 families: {len(corr2_families)}")
    print(f"2->2 family edges: {edge_count}")
    acyclic, seen, total = topo_stats(family_edges, corr2_families)
    print(f"acyclic: {acyclic} ({seen}/{total})")

    members, cond_edges = kosaraju_scc(family_edges, corr2_families)
    print(f"SCC count: {len(members)}")
    print("nontrivial SCCs:")
    for comp in members:
        if len(comp) > 1:
            print(f"  size {len(comp)}: {sorted(comp)}")
    print(f"condensation edges: {sum(len(v) for v in cond_edges.values())}")

    print("sample family edges:")
    shown = 0
    for src in sorted(corr2_families):
        outs = sorted(family_edges.get(src, set()))
        if not outs:
            continue
        print(f"  {src} -> {outs}")
        shown += 1
        if shown == 20:
            break


if __name__ == "__main__":
    main()
