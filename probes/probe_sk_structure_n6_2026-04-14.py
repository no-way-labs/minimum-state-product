#!/usr/bin/env python3
"""SK structural analysis at n=6 tail  ms=(2,2,2,3,3,3).

The question: does the rigid structural pattern observed at n=5 tail
(universal binary histogram (1,3,3,3,3,3,3,1), reverse 6-cycle + 4
uniform attachments, 6 edges per proc) extend to n=6? At n=6 the
ternary fiber space expands from 3^2=9 to 3^3=27, so raw |SK| cannot
be constant. But the binary-projection skeleton should still be rigid
if the 3CB structural magic generalizes.

Experiments:
  (1) binary histogram per cycle — is a fixed pattern (k uniform, m
      non-uniform) invariant across cycles, or does it vary?
  (2) binary-projection edge set — 10-edge skeleton (6-cycle reverse +
      4 uniform attachments) preserved?
  (3) edge count by mover — constant per proc?
  (4) raw |SK| and round count — range across cycles.
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
    tpos = non_binary_pos(ms)
    by_bin = defaultdict(set)
    for c in kernel:
        bp = tuple(c[i] for i in bpos)
        fiber = tuple(c[i] for i in tpos)
        by_bin[bp].add(fiber)

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
        "bin_histogram": {bp: len(fs) for bp, fs in by_bin.items()},
        "edge_count_by_mover": dict(edge_count_by_mover),
        "bin_proj_edges": dict(bin_proj_edges),
        "bin_states_hit": set(by_bin.keys()),
    }


N6_TAIL = (2, 2, 2, 3, 3, 3)


def main():
    ms = N6_TAIL
    n = len(ms)
    print(f"n=6 tail  ms={ms}  product={2*2*2*3*3*3}")

    all_configs = list(iproduct(*[range(m) for m in ms]))
    cycles = find_short_cycles(all_configs[0], ms, max_length=12,
                                max_found=12, time_budget=60.0)
    print(f"cycles found: {len(cycles)}\n")

    infos = []
    for idx, c in enumerate(cycles):
        ok, det = check_cycle_consistency(c, n, ms)
        if not ok: continue
        good_set = set(c)
        ng, _, adj = build_forced_graph(ms, n, det, good_set)
        sk, rounds = sink_kernel(ng, adj)
        info = analyze(sk, adj, ms, n)
        info["cycle_len"] = len(c)
        info["rounds"] = rounds
        infos.append(info)

    for idx, info in enumerate(infos[:4]):
        print(f"--- cycle {idx}  L={info['cycle_len']}  "
              f"|SK|={info['sk_size']}  rounds={info['rounds']} ---")
        print(f"  binary histogram:")
        for bp in sorted(info["bin_histogram"].keys()):
            print(f"    {bp}: {info['bin_histogram'][bp]} configs")
        print(f"  edges by mover proc: {info['edge_count_by_mover']}")
        print(f"  binary-proj edges ({len(info['bin_proj_edges'])} distinct):")
        for (bu, bv), cnt in sorted(info["bin_proj_edges"].items()):
            print(f"    {bu} -> {bv}  x{cnt}")
        print()

    # Rigidity checks.
    print("=" * 60)
    print(f"RIGIDITY CHECK across {len(infos)} cycles:")
    print("=" * 60)

    sk_sizes = [info["sk_size"] for info in infos]
    print(f"  |SK| values: {Counter(sk_sizes)}")

    bin_states_hit_all = set.union(*(info["bin_states_hit"] for info in infos))
    print(f"  binary states ever hit: {len(bin_states_hit_all)}/8")
    always_hit = set.intersection(*(info["bin_states_hit"] for info in infos))
    print(f"  binary states hit by ALL cycles: {len(always_hit)}/8")

    # Histogram fingerprints.
    hist_fps = [tuple(sorted(info["bin_histogram"].items())) for info in infos]
    print(f"  distinct binary-histogram fingerprints: {len(set(hist_fps))}")

    # Uniform vs non-uniform counts.
    uniform_states = [(0,0,0), (1,1,1)]
    nonuniform_states = [(0,0,1),(0,1,1),(0,1,0),(1,1,0),(1,0,0),(1,0,1)]
    uniform_counts = []
    nonuniform_counts = []
    for info in infos:
        h = info["bin_histogram"]
        uniform_counts.append(tuple(sorted(h.get(s, 0) for s in uniform_states)))
        nonuniform_counts.append(tuple(sorted(h.get(s, 0) for s in nonuniform_states)))
    print(f"  uniform-state fiber-counts multiset across cycles:")
    for v in sorted(set(uniform_counts)):
        print(f"    {v}  (x{uniform_counts.count(v)})")
    print(f"  non-uniform state fiber-counts multiset across cycles:")
    for v in sorted(set(nonuniform_counts)):
        print(f"    {v}  (x{nonuniform_counts.count(v)})")

    # Edge count by mover.
    edge_fps = [tuple(sorted(info["edge_count_by_mover"].items())) for info in infos]
    print(f"  distinct edge-by-mover fingerprints: {len(set(edge_fps))}")
    if len(set(edge_fps)) <= 3:
        for v in sorted(set(edge_fps)):
            print(f"    {dict(v)}  (x{edge_fps.count(v)})")

    # Binary projection edge set (ignore multiplicities first).
    bp_skeleton = [frozenset(info["bin_proj_edges"].keys()) for info in infos]
    print(f"  distinct binary-projection SKELETONS (unique edge sets): "
          f"{len(set(bp_skeleton))}")
    if len(set(bp_skeleton)) <= 3:
        common = set.intersection(*(set(s) for s in bp_skeleton))
        print(f"  edges present in ALL cycles: {len(common)}")
        for e in sorted(common):
            print(f"    {e[0]} -> {e[1]}")

    # Check reverse 6-cycle + uniform attachments.
    six_cycle_fwd = [
        ((0,0,1),(0,1,1)), ((0,1,1),(0,1,0)), ((0,1,0),(1,1,0)),
        ((1,1,0),(1,0,0)), ((1,0,0),(1,0,1)), ((1,0,1),(0,0,1)),
    ]
    six_cycle_rev = [(b, a) for (a, b) in six_cycle_fwd]
    uniform_attach = [
        ((0,0,1),(0,0,0)), ((0,0,0),(1,0,0)),
        ((1,1,0),(1,1,1)), ((1,1,1),(0,1,1)),
    ]
    uniform_attach_rev = [(b, a) for (a, b) in uniform_attach]
    print(f"\n  skeleton match per cycle:")
    for idx, info in enumerate(infos[:8]):
        bp = info["bin_proj_edges"]
        fwd6 = sum(1 for e in six_cycle_fwd if e in bp)
        rev6 = sum(1 for e in six_cycle_rev if e in bp)
        ua = sum(1 for e in uniform_attach if e in bp)
        ua_r = sum(1 for e in uniform_attach_rev if e in bp)
        other_count = sum(1 for e in bp if e not in six_cycle_fwd
                          and e not in six_cycle_rev
                          and e not in uniform_attach
                          and e not in uniform_attach_rev)
        print(f"    cycle {idx}: fwd6={fwd6}/6 rev6={rev6}/6 "
              f"ua={ua}/4 ua_rev={ua_r}/4 other={other_count}")


if __name__ == "__main__":
    main()
