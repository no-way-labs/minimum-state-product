#!/usr/bin/env python3
"""
Generate quotient-rank data for a chosen family block under the MVP summary
state `boundary12 + first 2 omitted-core symbols + monoTag(rest)`.

If the quotient graph is acyclic, this prints a rank table size and a few sample
ranked states. If not, it prints the nontrivial SCC sizes.
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


class BlockRank:
    def __init__(self, n: int, families: tuple[tuple[int, ...], ...]):
        self.n = n
        self.families = families
        self.model = Cup2Model(n)
        self.good = self.model.good_cycle_set()
        self.free = [i for i in range(n) if i not in {0, 1, 2, n - 3, n - 2, n - 1}]

    @lru_cache(None)
    def slice_corr(self, b6: tuple[int, ...]) -> dict[tuple[int | None, ...], int]:
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

        q = deque(i for i, d in enumerate(indeg) if d == 0)
        topo: list[int] = []
        while q:
            i = q.popleft()
            topo.append(i)
            for j in fixed_succ[i]:
                indeg[j] -= 1
                if indeg[j] == 0:
                    q.append(j)

        for i in reversed(topo):
            for j in fixed_succ[i]:
                if seg_fc[j] > seg_fc[i]:
                    seg_fc[i] = seg_fc[j]

        out: dict[tuple[int | None, ...], int] = {}
        for i, cfg in enumerate(states):
            sig = sig2(cfg)
            d = seg_fc[i] - fc_vals[i]
            prev = out.get(sig)
            if prev is None:
                out[sig] = d
            elif prev != d:
                raise RuntimeError(("correction mismatch", b6, sig, prev, d))
        return out

    def build(self):
        nodes: set[tuple[int | None, ...]] = set()
        edges: dict[tuple[int | None, ...], set[tuple[int | None, ...]]] = defaultdict(set)

        for idx_b6, b6 in enumerate(self.families, start=1):
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

            for i in reversed(topo):
                for j in fixed_succ[i]:
                    if seg_fc[j] > seg_fc[i]:
                        seg_fc[i] = seg_fc[j]
                    out_targets[i].update(out_targets[j])

            for cfg, seg, targets in zip(states, seg_fc, out_targets):
                sig = sig2(cfg)
                if self.slice_corr(b6)[sig] != 2:
                    continue
                nodes.add(sig)
                for dst in targets:
                    dst_b6 = boundary6(dst)
                    if dst_b6 not in self.families:
                        continue
                    ts = sig2(dst)
                    if self.slice_corr(dst_b6)[ts] == 2:
                        edges[sig].add(ts)
                        nodes.add(ts)
            print(f"    processed family {idx_b6}/{len(self.families)} for block {self.families}", flush=True)

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

        nontrivial = sorted(Counter(comp)[c] for c in set(comp) if Counter(comp)[c] > 1)
        if nontrivial:
            return {"nodes": ordered, "edges": edges, "nontrivial_scc_sizes": nontrivial}

        topo_nodes = []
        indeg = [0] * len(ordered)
        for vs in adj:
            for j in vs:
                indeg[j] += 1
        q = deque(i for i, d in enumerate(indeg) if d == 0)
        while q:
            i = q.popleft()
            topo_nodes.append(i)
            for j in adj[i]:
                indeg[j] -= 1
                if indeg[j] == 0:
                    q.append(j)
        rank = [0] * len(ordered)
        for i in reversed(topo_nodes):
            if adj[i]:
                rank[i] = 1 + max(rank[j] for j in adj[i])
        return {"nodes": ordered, "edges": edges, "rank": rank, "nontrivial_scc_sizes": []}


def main() -> None:
    n = 15
    for name, fams in [
        ("2fam0", ((0, 0, 0, 0, 0, 0), (0, 0, 0, 1, 0, 0))),
        ("3fam0", ((0, 0, 0, 0, 2, 0), (0, 0, 0, 1, 2, 0), (0, 0, 0, 2, 2, 0))),
    ]:
        print(f"building {name}", flush=True)
        block = BlockRank(n, fams)
        result = block.build()
        print(name)
        print(f"  nodes = {len(result['nodes'])}")
        print(f"  edges = {sum(len(v) for v in result['edges'].values())}")
        print(f"  nontrivial_scc_sizes = {result['nontrivial_scc_sizes']}")
        if "rank" in result:
            rank = result["rank"]
            print(f"  rank range = ({min(rank)}, {max(rank)})")
            for pair in list(zip(result['nodes'], rank))[:10]:
                print(f"    {pair}")


if __name__ == "__main__":
    main()
