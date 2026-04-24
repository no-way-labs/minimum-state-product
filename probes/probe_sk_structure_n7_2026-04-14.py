#!/usr/bin/env python3
"""SK structural analysis at n=7 tail  ms=(2,2,2,3,3,3,3).

Prediction: same 10-edge binary-cube skeleton (reverse 6-cycle plus 4
uniform attachments), per-proc edge count rigid across cycles, SK size
constant across length-2n candidates.
"""

from itertools import product as iproduct
from collections import defaultdict, Counter
import time


def check_cycle_consistency(cycle_configs, n, ms):
    required = {}
    L = len(cycle_configs)
    for idx in range(L):
        c = cycle_configs[idx]
        c_next = cycle_configs[(idx+1) % L]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return False, {}
        mv = diffs[0]
        Li = c[(mv-1)%n]; Si = c[mv]; Ri = c[(mv+1)%n]
        km = (mv, Li, Si, Ri)
        if km in required and required[km] != c_next[mv]:
            return False, {}
        required[km] = c_next[mv]
        for i in range(n):
            if i == mv: continue
            Li2 = c[(i-1)%n]; Si2 = c[i]; Ri2 = c[(i+1)%n]
            ki = (i, Li2, Si2, Ri2)
            if ki in required and required[ki] != Si2:
                return False, {}
            required[ki] = Si2
    return True, required


def find_short_cycles(start, ms, max_length, max_found=500, time_budget=30.0):
    n = len(ms)
    found = []
    t0 = time.time()
    def dfs(path, movers_used):
        if len(found) >= max_found or time.time() - t0 > time_budget:
            return
        config = path[-1]
        if len(path) >= n * 2 and len(movers_used) == n:
            for proc in range(n):
                for new_val in range(ms[proc]):
                    if new_val == config[proc]: continue
                    nc = list(config); nc[proc] = new_val
                    if tuple(nc) == start:
                        ok, _ = check_cycle_consistency(list(path), n, ms)
                        if ok:
                            found.append(list(path))
        if len(path) >= max_length:
            return
        visited = set(path)
        for proc in range(n):
            for new_val in range(ms[proc]):
                if new_val == config[proc]: continue
                nc = list(config); nc[proc] = new_val
                nc_t = tuple(nc)
                if nc_t in visited: continue
                dfs(path + [nc_t], movers_used | {proc})
    dfs([start], set())
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


def non_binary_pos(ms):
    return [i for i, m in enumerate(ms) if m != 2]


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
            if v not in kset:
                continue
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


def main():
    ms = (2, 2, 2, 3, 3, 3, 3)
    n = 7
    P = 1
    for m in ms: P *= m
    print(f"n=7 tail  ms={ms}  product={P}  threshold=4*3^(n-2)={4*3**(n-2)}")

    # Enumerate length-2n cycles from first few starts.
    all_configs = list(iproduct(*[range(m) for m in ms]))
    cycles = []
    seen = set()
    t_total_start = time.time()
    for start_idx in range(4):
        if time.time() - t_total_start > 300:
            break
        start = all_configs[start_idx]
        print(f"  trying start {start_idx} = {start} ...")
        budget = 100.0
        t0 = time.time()
        new_cycles = find_short_cycles(start, ms, max_length=14,
                                        max_found=12, time_budget=budget)
        print(f"    found {len(new_cycles)} cycles in {time.time()-t0:.1f}s")
        for c in new_cycles:
            key = tuple(c)
            if key not in seen:
                seen.add(key)
                cycles.append(c)
        if len(cycles) >= 8:
            break
    print(f"\n  total distinct cycles: {len(cycles)}")

    if not cycles:
        print("  NO CYCLES FOUND — enumeration failed at this budget")
        return

    infos = []
    for c in cycles[:8]:
        ok, det = check_cycle_consistency(c, n, ms)
        if not ok: continue
        good_set = set(c)
        ng, _, adj = build_forced_graph(ms, n, det, good_set)
        sk, rounds = sink_kernel(ng, adj)
        info = analyze(sk, adj, ms, n)
        info["cycle_len"] = len(c)
        info["rounds"] = rounds
        infos.append(info)

    # Detail print.
    for idx, info in enumerate(infos[:3]):
        print(f"\n--- cycle {idx}  L={info['cycle_len']}  |SK|={info['sk_size']}  rounds={info['rounds']} ---")
        print(f"  binary histogram:")
        for bp in sorted(info["bin_histogram"].keys()):
            print(f"    {bp}: {info['bin_histogram'][bp]} configs")
        print(f"  edges by mover proc: {info['edge_count_by_mover']}")
        print(f"  binary-proj edges ({len(info['bin_proj_edges'])} distinct):")
        for (bu, bv), cnt in sorted(info["bin_proj_edges"].items()):
            print(f"    {bu} -> {bv}  x{cnt}")

    # Rigidity checks.
    print("\n" + "=" * 60)
    print(f"RIGIDITY CHECK across {len(infos)} cycles:")
    print("=" * 60)

    sk_sizes = [info["sk_size"] for info in infos]
    print(f"  |SK| values: {Counter(sk_sizes)}")

    hist_fps = [tuple(sorted(info["bin_histogram"].items())) for info in infos]
    print(f"  distinct binary-histogram fingerprints: {len(set(hist_fps))}")

    edge_fps = [tuple(sorted(info["edge_count_by_mover"].items())) for info in infos]
    print(f"  distinct edge-by-mover fingerprints: {len(set(edge_fps))}")
    if len(set(edge_fps)) == 1:
        print(f"    uniform: {dict(edge_fps[0])}")

    bp_skeleton = [frozenset(info["bin_proj_edges"].keys()) for info in infos]
    print(f"  distinct binary-projection skeletons: {len(set(bp_skeleton))}")

    # Check canonical skeleton.
    six_cycle_fwd = [
        ((0,0,1),(0,1,1)), ((0,1,1),(0,1,0)), ((0,1,0),(1,1,0)),
        ((1,1,0),(1,0,0)), ((1,0,0),(1,0,1)), ((1,0,1),(0,0,1)),
    ]
    six_cycle_rev = [(b, a) for (a, b) in six_cycle_fwd]
    uniform_attach = [
        ((0,0,1),(0,0,0)), ((0,0,0),(1,0,0)),
        ((1,1,0),(1,1,1)), ((1,1,1),(0,1,1)),
    ]
    print(f"\n  canonical skeleton match per cycle:")
    for idx, info in enumerate(infos):
        bp = info["bin_proj_edges"]
        fwd6 = sum(1 for e in six_cycle_fwd if e in bp)
        rev6 = sum(1 for e in six_cycle_rev if e in bp)
        ua = sum(1 for e in uniform_attach if e in bp)
        other = sum(1 for e in bp if e not in six_cycle_fwd
                    and e not in six_cycle_rev
                    and e not in uniform_attach)
        print(f"    cycle {idx}: rev6={rev6}/6 ua={ua}/4 other={other}")


if __name__ == "__main__":
    main()
