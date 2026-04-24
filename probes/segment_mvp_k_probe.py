#!/usr/bin/env python3
"""
Probe fat summary states of the form

  boundary12 + first k omitted-core symbols + monoTag(rest)

on the hardest sampled plateau-family SCCs.

This is an MVP-oriented search: we do not optimize for minimality, only for
finding a fixed-width state that destroys the sample SCCs.
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


def scc_sizes(n: int, families: tuple[tuple[int, ...], ...], k: int):
    sigf = make_sig_plus_mono(k)
    model = Cup2Model(n)
    good = model.good_cycle_set()
    free = [i for i in range(n) if i not in {0, 1, 2, n - 3, n - 2, n - 1}]

    @lru_cache(None)
    def slice_corr(b6: tuple[int, ...]):
        states = []
        for vals in product(range(3), repeat=len(free)):
            cfg = [None] * n
            cfg[0], cfg[1], cfg[2], cfg[n - 3], cfg[n - 2], cfg[n - 1] = b6
            for i, v in zip(free, vals):
                cfg[i] = v
            states.append(tuple(cfg))

        idx_of = {cfg: i for i, cfg in enumerate(states)}
        fc_vals = [model.fc(cfg) for cfg in states]
        tp_vals = [model.tp(cfg) for cfg in states]
        bad_flags = [model.encode(cfg) not in good for cfg in states]
        fixed_succ = [[] for _ in states]
        indeg = [0] * len(states)
        seg_fc = fc_vals[:]

        for i, cfg in enumerate(states):
            if not bad_flags[i]:
                continue
            for p in range(n):
                if not model.privileged(cfg, p):
                    continue
                dst = model.fire(cfg, p)
                if model.encode(dst) in good:
                    continue
                if model.tp(dst) != tp_vals[i]:
                    continue
                if boundary6(dst) == b6:
                    j = idx_of[dst]
                    fixed_succ[i].append(j)
                    indeg[j] += 1
                else:
                    seg_fc[i] = max(seg_fc[i], model.fc(dst))

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
            sig = sigf(cfg)
            d = seg_fc[i] - model.fc(cfg)
            prev = out.get(sig)
            if prev is None:
                out[sig] = d
            elif prev != d:
                raise RuntimeError(("summary mismatch", n, b6, k, sig, prev, d))
        return out

    nodes: set[tuple[int | None, ...]] = set()
    edges: dict[tuple[int | None, ...], set[tuple[int | None, ...]]] = defaultdict(set)

    for b6 in families:
        states = []
        for vals in product(range(3), repeat=len(free)):
            cfg = [None] * n
            cfg[0], cfg[1], cfg[2], cfg[n - 3], cfg[n - 2], cfg[n - 1] = b6
            for i, v in zip(free, vals):
                cfg[i] = v
            states.append(tuple(cfg))

        idx_of = {cfg: i for i, cfg in enumerate(states)}
        fc_vals = [model.fc(cfg) for cfg in states]
        tp_vals = [model.tp(cfg) for cfg in states]
        bad_flags = [model.encode(cfg) not in good for cfg in states]
        fixed_succ = [[] for _ in states]
        indeg = [0] * len(states)
        out_targets = [set() for _ in states]
        seg_fc = fc_vals[:]

        for i, cfg in enumerate(states):
            if not bad_flags[i]:
                continue
            for p in range(n):
                if not model.privileged(cfg, p):
                    continue
                dst = model.fire(cfg, p)
                if model.encode(dst) in good:
                    continue
                if model.tp(dst) != tp_vals[i]:
                    continue
                if boundary6(dst) == b6:
                    j = idx_of[dst]
                    fixed_succ[i].append(j)
                    indeg[j] += 1
                else:
                    seg_fc[i] = max(seg_fc[i], model.fc(dst))
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
            sig = sigf(cfg)
            sc = slice_corr(b6)[sig]
            if sc != 2:
                continue
            nodes.add(sig)
            for dst in targets:
                dst_b6 = boundary6(dst)
                if dst_b6 not in families:
                    continue
                dst_sig = sigf(dst)
                dst_corr = slice_corr(dst_b6)[dst_sig]
                if dst_corr == 2:
                    edges[sig].add(dst_sig)
                    nodes.add(dst_sig)

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
    families2 = ((0, 0, 0, 0, 0, 0), (0, 0, 0, 1, 0, 0))
    families3 = ((0, 0, 0, 0, 2, 0), (0, 0, 0, 1, 2, 0), (0, 0, 0, 2, 2, 0))
    for name, fams in [("2fam", families2), ("3fam", families3)]:
        print(name)
        for k in [0, 1, 2, 3, 4, 5, 6]:
            print(f"  k={k}: {scc_sizes(n, fams, k)}")


if __name__ == "__main__":
    main()
