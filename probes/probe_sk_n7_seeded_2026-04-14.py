#!/usr/bin/env python3
"""Seeded enumerator for length-2n uniform-sweep cycles at n=7 tail.

Instead of free DFS, we fix the mover sequence to [0,1,...,n-1,0,...,n-1]
and only search over the value choices at each step. This is a much
smaller search space (at most 2^k leaves per start, where k = number of
ternary firings) and terminates quickly.

Goal: enumerate the canonical base-layer cycles at n=7 tail and verify
the 10-edge binary-cube skeleton predicted from n=5, n=6.
"""

from itertools import product as iproduct
from collections import defaultdict, Counter
import time


def enumerate_sweep_cycles(ms, n, max_found=30, time_budget=120.0):
    """Length-2n cycles with mover sequence [0..n-1]*2."""
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
                cycle_tup = tuple(path)
                if cycle_tup not in seen:
                    seen.add(cycle_tup)
                    found.append((list(path), list(mover_seq), dict(det)))
            return
        p = mover_seq[step]
        Lp = config[(p-1)%n]; Sp = config[p]; Rp = config[(p+1)%n]
        key_m = (p, Lp, Sp, Rp)
        forced_out = det.get(key_m)
        for new_val in range(ms[p]):
            if new_val == Sp: continue
            if forced_out is not None and forced_out != new_val: continue
            # Consistent new_det.
            new_det = dict(det)
            new_det[key_m] = new_val
            # Non-mover entries: every other proc's context must be
            # consistent with its current value.
            consistent = True
            for i in range(n):
                if i == p: continue
                Li = config[(i-1)%n]; Si = config[i]; Ri = config[(i+1)%n]
                ki = (i, Li, Si, Ri)
                if ki in new_det and new_det[ki] != Si:
                    consistent = False; break
                new_det[ki] = Si
            if not consistent: continue
            nc = list(config); nc[p] = new_val; nc = tuple(nc)
            # Avoid revisiting a config before closing (except closure).
            if step + 1 < L and nc in set(path):
                continue
            dfs(step+1, nc, new_det, path + [nc])

    for start_idx, start in enumerate(all_starts):
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


def sink_kernel(non_good, adj):
    remaining = set(non_good)
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
        remaining -= sinks
        rounds += 1
    return remaining, rounds


def binary_pos(ms):
    return [i for i, m in enumerate(ms) if m == 2]


def analyze(kernel, adj, ms, n):
    bpos = binary_pos(ms)
    by_bin = defaultdict(int)
    for c in kernel:
        bp = tuple(c[i] for i in bpos)
        by_bin[bp] += 1
    edge_count_by_mover = Counter()
    bin_proj_edges = Counter()
    kset = set(kernel)
    for u in kernel:
        for v, p in adj.get(u, ()):
            if v not in kset: continue
            edge_count_by_mover[p] += 1
            if p in bpos:
                bu = tuple(u[i] for i in bpos)
                bv = tuple(v[i] for i in bpos)
                bin_proj_edges[(bu, bv)] += 1
    return {
        "sk_size": len(kernel),
        "bin_histogram": dict(by_bin),
        "edge_count_by_mover": dict(edge_count_by_mover),
        "bin_proj_edges": dict(bin_proj_edges),
    }


def run(ms, label):
    n = len(ms)
    P = 1
    for m in ms: P *= m
    print(f"\n{'='*60}")
    print(f"{label}  ms={ms}  n={n}  product={P}  threshold={4*3**(n-2)}")
    print(f"{'='*60}")

    t0 = time.time()
    cycles = enumerate_sweep_cycles(ms, n, max_found=20, time_budget=120.0)
    print(f"sweep cycles found: {len(cycles)} in {time.time()-t0:.1f}s")
    if not cycles:
        return

    infos = []
    for cycle, movers, det in cycles:
        good_set = set(cycle)
        ng, _, adj = build_forced_graph(ms, n, det, good_set)
        sk, rounds = sink_kernel(ng, adj)
        info = analyze(sk, adj, ms, n)
        info["cycle_len"] = len(cycle)
        info["rounds"] = rounds
        infos.append(info)

    # Detail on first cycle.
    if infos:
        info = infos[0]
        print(f"\nfirst cycle: L={info['cycle_len']}  |SK|={info['sk_size']}  rounds={info['rounds']}")
        print(f"  binary histogram:")
        for bp in sorted(info["bin_histogram"].keys()):
            print(f"    {bp}: {info['bin_histogram'][bp]}")
        print(f"  edges by mover proc: {info['edge_count_by_mover']}")
        print(f"  binary-proj edges ({len(info['bin_proj_edges'])}):")
        for (bu, bv), cnt in sorted(info["bin_proj_edges"].items()):
            print(f"    {bu} -> {bv}  x{cnt}")

    # Rigidity.
    print(f"\nRIGIDITY across {len(infos)} cycles:")
    sk_sizes = [info["sk_size"] for info in infos]
    print(f"  |SK|: {Counter(sk_sizes)}")
    hist_fps = [tuple(sorted(info["bin_histogram"].items())) for info in infos]
    print(f"  distinct histograms: {len(set(hist_fps))}")
    edge_fps = [tuple(sorted(info["edge_count_by_mover"].items())) for info in infos]
    print(f"  distinct edge-by-mover: {len(set(edge_fps))}")
    bp_skeletons = [frozenset(info["bin_proj_edges"].keys()) for info in infos]
    print(f"  distinct bin-proj skeletons: {len(set(bp_skeletons))}")

    # Canonical skeleton.
    six_cycle_rev = [
        ((0,1,1),(0,0,1)), ((0,1,0),(0,1,1)), ((1,1,0),(0,1,0)),
        ((1,0,0),(1,1,0)), ((1,0,1),(1,0,0)), ((0,0,1),(1,0,1)),
    ]
    uniform_attach = [
        ((0,0,1),(0,0,0)), ((0,0,0),(1,0,0)),
        ((1,1,0),(1,1,1)), ((1,1,1),(0,1,1)),
    ]
    print(f"\n  canonical skeleton match per cycle:")
    for idx, info in enumerate(infos[:10]):
        bp = info["bin_proj_edges"]
        rev6 = sum(1 for e in six_cycle_rev if e in bp)
        ua = sum(1 for e in uniform_attach if e in bp)
        other = sum(1 for e in bp if e not in six_cycle_rev
                    and e not in uniform_attach)
        print(f"    cycle {idx}: rev6={rev6}/6 ua={ua}/4 other={other}")


def main():
    # Sanity: n=5 and n=6 should reproduce the previous results.
    run((2,2,2,3,3), "n=5 tail (sanity)")
    run((2,2,2,3,3,3), "n=6 tail (sanity)")
    # New: n=7 tail.
    run((2,2,2,3,3,3,3), "n=7 tail")


if __name__ == "__main__":
    main()
