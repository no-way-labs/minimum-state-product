#!/usr/bin/env python3
"""One-shot extractor for the n=5 SK walkthrough doc.

Pulls a candidate sweep cycle, its det dict, the non-good set, and the
SK iteration trace at n=5 ms=(2,2,2,3,3), plus an explicit witness for
each of the 4 canonical pole edges. Output goes to stdout in a form
suitable for direct inclusion in the markdown walkthrough.
"""
from itertools import product as iproduct
from collections import defaultdict
import time


def enumerate_sweep_cycles(ms, n, max_found=1, time_budget=30.0):
    mover_seq = list(range(n)) * 2
    L = len(mover_seq)
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []
    seen = set()
    t0 = time.time()

    def dfs(step, config, det, path):
        if len(found) >= max_found or time.time() - t0 > time_budget:
            return
        if step == L:
            if config == path[0]:
                ct = tuple(path)
                if ct not in seen:
                    seen.add(ct)
                    found.append((list(path), list(mover_seq), dict(det)))
            return
        p = mover_seq[step]
        Lp = config[(p-1)%n]; Sp = config[p]; Rp = config[(p+1)%n]
        km = (p, Lp, Sp, Rp)
        forced_out = det.get(km)
        for new_val in range(ms[p]):
            if new_val == Sp: continue
            if forced_out is not None and forced_out != new_val: continue
            new_det = dict(det)
            new_det[km] = new_val
            ok = True
            for i in range(n):
                if i == p: continue
                Li = config[(i-1)%n]; Si = config[i]; Ri = config[(i+1)%n]
                ki = (i, Li, Si, Ri)
                if ki in new_det and new_det[ki] != Si:
                    ok = False; break
                new_det[ki] = Si
            if not ok: continue
            nc = list(config); nc[p] = new_val; nc = tuple(nc)
            if step + 1 < L and nc in set(path):
                continue
            dfs(step+1, nc, new_det, path + [nc])

    for start in all_starts:
        if len(found) >= max_found or time.time() - t0 > time_budget:
            break
        dfs(0, start, {}, [start])
    return found


def build_forced_graph(ms, n, det, good_set):
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
    ng_set = set(non_good)
    adj = defaultdict(list)
    for c in non_good:
        for p in range(n):
            Lp = c[(p-1)%n]; Sp = c[p]; Rp = c[(p+1)%n]
            key = (p, Lp, Sp, Rp)
            if key in det and det[key] != Sp:
                nc = list(c); nc[p] = det[key]; nc = tuple(nc)
                if nc in ng_set:
                    adj[c].append((nc, p))
    return non_good, ng_set, adj


def sink_kernel_with_trace(non_good, adj):
    remaining = set(non_good)
    rounds_log = []
    rounds = 0
    while True:
        sinks = set()
        for c in remaining:
            has_out = False
            for tgt, _ in adj.get(c, []):
                if tgt in remaining:
                    has_out = True
                    break
            if not has_out:
                sinks.add(c)
        if not sinks:
            break
        rounds_log.append((len(sinks), len(remaining) - len(sinks)))
        remaining -= sinks
        rounds += 1
    return remaining, rounds, rounds_log


def main():
    ms = (2, 2, 2, 3, 3)
    n = 5
    print(f"=== n={n} ms={ms} (product={1*2*2*2*3*3}) ===\n")

    cycles = enumerate_sweep_cycles(ms, n, max_found=1, time_budget=60.0)
    cycle, movers, det = cycles[0]
    print(f"CYCLE (length {len(cycle)}):")
    for t, c in enumerate(cycle):
        mv = movers[t] if t < len(movers) else None
        print(f"  t={t:2d}: {c}  →  mover next: {mv}")
    print()

    print(f"DET dict ({len(det)} entries):")
    for k in sorted(det.keys()):
        print(f"  ({k[0]}, L={k[1]}, S={k[2]}, R={k[3]}) → {det[k]}")
    print()

    good_set = set(cycle)
    ng, _, adj = build_forced_graph(ms, n, det, good_set)
    sk, rounds, rounds_log = sink_kernel_with_trace(ng, adj)
    print(f"NON-GOOD: {len(ng)} configs (= {1*2*2*2*3*3} - {len(cycle)} = {1*2*2*2*3*3 - len(cycle)})")
    print(f"FORCED EDGES (within non-good): {sum(len(adj[c]) for c in ng)}")
    print()

    print(f"SK ITERATION ({rounds} rounds):")
    print(f"  start: {len(ng)} configs")
    cumulative = len(ng)
    for r, (removed, after) in enumerate(rounds_log):
        cumulative -= removed
        print(f"  round {r+1}: remove {removed:3d} sinks, {cumulative:3d} remaining")
    print(f"SK final: {len(sk)} configs")
    print()

    bpos = [0, 1, 2]
    nbpos = [3, 4]

    # SK content by binary projection
    print("SK by binary projection:")
    by_proj = defaultdict(list)
    for c in sk:
        bp = tuple(c[i] for i in bpos)
        by_proj[bp].append(c)
    for bp in sorted(by_proj):
        print(f"  {bp}: {len(by_proj[bp])} configs")
        for c in sorted(by_proj[bp]):
            print(f"    {c}")
    print()

    # Forced edges in projection: only count moves at binary positions
    print("FORCED EDGES IN BINARY PROJECTION (mover ∈ binary positions):")
    proj_edges = defaultdict(list)
    for c in sk:
        for cprime, p in adj[c]:
            if cprime not in sk: continue
            if p not in bpos: continue
            bp_c = tuple(c[i] for i in bpos)
            bp_cprime = tuple(cprime[i] for i in bpos)
            if bp_c != bp_cprime:
                proj_edges[(bp_c, bp_cprime)].append((c, cprime, p))
    for edge in sorted(proj_edges):
        wits = proj_edges[edge]
        print(f"  {edge[0]} → {edge[1]}: {len(wits)} witnesses")
        for c, cprime, p in wits:
            print(f"    {c} →[mover={p}] {cprime}")
    print()

    # The 4 canonical pole edges
    POLE = [
        ((0,0,1),(0,0,0)),
        ((0,0,0),(1,0,0)),
        ((1,1,0),(1,1,1)),
        ((1,1,1),(0,1,1)),
    ]
    print("POLE EDGES (load-bearing for T2):")
    for edge in POLE:
        wits = proj_edges.get(edge, [])
        print(f"  pole {edge[0]} → {edge[1]}: {len(wits)} witness(es)")
        for c, cprime, p in wits:
            Lp = c[(p-1)%n]; Sp = c[p]; Rp = c[(p+1)%n]
            print(f"    c={c}  c'={cprime}  mover p={p}  context (L={Lp},S={Sp},R={Rp})  det→{cprime[p]}")


if __name__ == "__main__":
    main()
