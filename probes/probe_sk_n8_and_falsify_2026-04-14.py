#!/usr/bin/env python3
"""Two experiments on the 3CB SK structural theorem:

(1) n=8 prediction check on ms=(2,2,2,3,3,3,3,3).
    Closed-form predictions:
       |SK|          = 240
       edges/proc    = 62
       heavy mult    = 31 (two of six 6-cycle edges)
       light mult    = 16 (four of six 6-cycle edges)
       uniform attach mult = 15
       uniform state count = 26

(2) Falsification: non-consecutive binary at n=6. Run the same probe
    on ms=(2,3,2,2,3,3) — binary positions are now 0, 2, 3 (not all
    adjacent on the ring; P1 is a ternary sandwiched between binaries).
    Prediction: the canonical 10-edge reverse-6-cycle skeleton on
    the 3-binary-position projection does NOT appear (or appears with
    different structure), confirming 3CB is the specific source of the
    invariant.
"""

from itertools import product as iproduct
from collections import defaultdict, Counter
import time


def enumerate_sweep_cycles(ms, n, max_found=30, time_budget=120.0):
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
            new_det = dict(det)
            new_det[key_m] = new_val
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


def sink_kernel(non_good, adj):
    remaining = set(non_good)
    rounds = 0
    while True:
        sinks = set()
        for c in remaining:
            has_out = False
            for tgt, _ in adj.get(c, []):
                if tgt in remaining:
                    has_out = True; break
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


# Canonical 3CB skeleton (works when #binary == 3).
CANON_6CYC_REV = [
    ((0,1,1),(0,0,1)), ((0,1,0),(0,1,1)), ((1,1,0),(0,1,0)),
    ((1,0,0),(1,1,0)), ((1,0,1),(1,0,0)), ((0,0,1),(1,0,1)),
]
CANON_UA = [
    ((0,0,1),(0,0,0)), ((0,0,0),(1,0,0)),
    ((1,1,0),(1,1,1)), ((1,1,1),(0,1,1)),
]


def canon_match(bp_edges):
    rev6 = sum(1 for e in CANON_6CYC_REV if e in bp_edges)
    ua = sum(1 for e in CANON_UA if e in bp_edges)
    other = sum(1 for e in bp_edges if e not in CANON_6CYC_REV
                and e not in CANON_UA)
    return rev6, ua, other


def run(ms, label, predict=None):
    n = len(ms)
    P = 1
    for m in ms: P *= m
    bpos = binary_pos(ms)
    print(f"\n{'='*66}")
    print(f"{label}  ms={ms}  n={n}  product={P}  "
          f"threshold=4*3^{n-2}={4*3**(n-2)}")
    print(f"binary positions: {bpos}")
    print(f"{'='*66}")

    t0 = time.time()
    cycles = enumerate_sweep_cycles(ms, n, max_found=30, time_budget=300.0)
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

    # First-cycle details.
    if infos:
        info = infos[0]
        print(f"\nfirst cycle: L={info['cycle_len']}  "
              f"|SK|={info['sk_size']}  rounds={info['rounds']}")
        print(f"  binary histogram ({len(info['bin_histogram'])} states hit):")
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

    # Canonical skeleton match (only meaningful when #binary == 3).
    if len(bpos) == 3:
        print(f"\n  canonical 3CB skeleton match per cycle:")
        for idx, info in enumerate(infos[:6]):
            rev6, ua, other = canon_match(info["bin_proj_edges"])
            print(f"    cycle {idx}: rev6={rev6}/6 ua={ua}/4 other={other}  "
                  f"total_edges={len(info['bin_proj_edges'])}")

    # Check prediction.
    if predict and infos:
        print(f"\n  PREDICTION CHECK:")
        info = infos[0]
        for key, expected in predict.items():
            actual = info.get(key)
            if key == "edges_per_proc":
                actual = set(info["edge_count_by_mover"].values())
                actual = next(iter(actual)) if len(actual) == 1 else actual
            match = "✓" if actual == expected else "✗"
            print(f"    {key}: predicted={expected}  actual={actual}  {match}")


def main():
    # Experiment 1: n=8 prediction check.
    run(
        (2, 2, 2, 3, 3, 3, 3, 3),
        "EXP 1  n=8 tail",
        predict={
            "sk_size": 240,
            "edges_per_proc": 62,
        },
    )

    # Experiment 2: falsification — non-consecutive binary at n=6.
    run(
        (2, 3, 2, 2, 3, 3),
        "EXP 2  n=6 non-consecutive binary (FALSIFICATION)",
    )


if __name__ == "__main__":
    main()
