#!/usr/bin/env python3
"""SK structural analysis at n=5 tail multisets.

For each tail ms at n=5, take several candidate good cycles, extract
SK(C) from each, and dump the internal structure:

  * kernel config list grouped by binary projection (positions 0,1,2)
  * per-binary-state: which ternary fibers (c[3], c[4]) appear
  * forced-edge classification in kernel:
      - P0/P1/P2 binary move  (changes a binary coord)
      - P3/P4 ternary move    (changes a ternary coord, fiber-switch)
  * binary-cube projection graph: V = 8 binary states, E = edges
    induced by binary moves in the kernel

We check whether:
  (i)  SK(C) is structurally identical across different cycles C at the
       same ms (same binary histogram, same fiber histogram, same
       binary-cube projection edges),
  (ii) the binary-cube projection is the canonical 6-cycle +
       uniform-states structure from memory.
"""

from itertools import product as iproduct
from collections import defaultdict, Counter
import time
import sys


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


def analyze_kernel(kernel, adj, ms, n):
    bpos = binary_pos(ms)
    tpos = non_binary_pos(ms)

    # Group by binary projection.
    by_bin = defaultdict(list)
    for c in kernel:
        bp = tuple(c[i] for i in bpos)
        by_bin[bp].append(c)

    # Fiber histogram per binary state.
    fiber_hist = {}
    for bp, cfgs in by_bin.items():
        fibers = sorted(tuple(c[i] for i in tpos) for c in cfgs)
        fiber_hist[bp] = fibers

    # Edge classification in kernel.
    kset = set(kernel)
    binary_edges = []    # (from_bp, to_bp, mover)
    ternary_loops = []   # (bp, from_fiber, to_fiber, mover)
    edge_count_by_mover = Counter()
    for u in kernel:
        for v, p in adj.get(u, ()):
            if v not in kset:
                continue
            edge_count_by_mover[p] += 1
            bu = tuple(u[i] for i in bpos)
            bv = tuple(v[i] for i in bpos)
            if p in bpos:
                binary_edges.append((bu, bv, p))
            else:
                fu = tuple(u[i] for i in tpos)
                fv = tuple(v[i] for i in tpos)
                ternary_loops.append((bu, fu, fv, p))

    # Binary cube projection: unique (bu -> bv) edges.
    bin_proj_edges = Counter()
    for bu, bv, p in binary_edges:
        bin_proj_edges[(bu, bv)] += 1

    return {
        "by_bin": dict(by_bin),
        "fiber_hist": fiber_hist,
        "edge_count_by_mover": dict(edge_count_by_mover),
        "bin_proj_edges": dict(bin_proj_edges),
        "binary_edges": binary_edges,
        "ternary_loops": ternary_loops,
    }


def print_structure(label, info, ms):
    bpos = binary_pos(ms)
    tpos = non_binary_pos(ms)
    print(f"\n  --- {label} ---")

    # Binary histogram
    print(f"  binary state histogram (8 possible):")
    for bp in sorted(info["by_bin"].keys()):
        fibers = info["fiber_hist"][bp]
        print(f"    {bp}: {len(fibers)} configs  fibers={fibers}")

    # Edge count by mover
    print(f"  edges by mover proc: {info['edge_count_by_mover']}")

    # Binary projection edges
    print(f"  binary-cube projection edges (dedup):")
    for (bu, bv), cnt in sorted(info["bin_proj_edges"].items()):
        print(f"    {bu} -> {bv}  x{cnt}")


def main():
    # Tail multisets at n=5.
    tails = [
        ("n5_tail_223a",  (2, 2, 2, 3, 3)),  # canonical sub-threshold
        # optional: other sub-thresholds for contrast
    ]

    for label, ms in tails:
        n = len(ms)
        print("=" * 70)
        print(f"TAIL {label}  ms={ms}  product={1 if not ms else eval('*'.join(map(str,ms)))}")
        print("=" * 70)

        # Enumerate a few candidate cycles and analyze SK of each.
        all_configs = list(iproduct(*[range(m) for m in ms]))
        cycles = find_short_cycles(all_configs[0], ms, max_length=10,
                                    max_found=8, time_budget=10.0)
        print(f"  cycles found: {len(cycles)}")

        infos = []
        for idx, c in enumerate(cycles):
            ok, det = check_cycle_consistency(c, n, ms)
            if not ok:
                continue
            good_set = set(c)
            ng, _, adj = build_forced_graph(ms, n, det, good_set)
            sk, rounds = sink_kernel(ng, adj)
            info = analyze_kernel(sk, adj, ms, n)
            info["cycle_len"] = len(c)
            info["sk_size"] = len(sk)
            info["rounds"] = rounds
            info["cycle"] = c
            infos.append(info)
            if idx < 3:
                print_structure(f"cycle {idx}  L={len(c)}  |SK|={len(sk)}",
                                info, ms)

        # Universality check: are the SK structures identical across cycles?
        print("\n  UNIVERSALITY CHECK across", len(infos), "cycles:")
        sk_sizes = [info["sk_size"] for info in infos]
        print(f"    SK sizes       : {Counter(sk_sizes)}")

        # Binary histograms: canonicalize to a sorted fingerprint.
        def bin_fingerprint(info):
            return tuple(sorted(
                (bp, tuple(info["fiber_hist"][bp]))
                for bp in info["by_bin"]
            ))

        fps = [bin_fingerprint(info) for info in infos]
        print(f"    distinct binary-histogram fingerprints: "
              f"{len(set(fps))}")

        # Edge-count by mover fingerprint.
        edge_fps = [tuple(sorted(info["edge_count_by_mover"].items()))
                    for info in infos]
        print(f"    distinct mover-edge fingerprints: "
              f"{len(set(edge_fps))}")

        # Binary projection edges (as directed multi-edge set).
        bp_fps = [tuple(sorted(info["bin_proj_edges"].items()))
                  for info in infos]
        print(f"    distinct binary-projection edge fingerprints: "
              f"{len(set(bp_fps))}")

        if len(set(fps)) == 1:
            print("    *** binary histograms IDENTICAL across all cycles ***")
        if len(set(bp_fps)) == 1:
            print("    *** binary projection edges IDENTICAL across all cycles ***")

        # Check: does the union of binary-projection edges form the classic
        # 6-cycle (001-011-010-110-100-101) plus uniform-state links?
        if infos:
            bp = infos[0]["bin_proj_edges"]
            six_cycle = [
                ((0,0,1),(0,1,1)), ((0,1,1),(0,1,0)), ((0,1,0),(1,1,0)),
                ((1,1,0),(1,0,0)), ((1,0,0),(1,0,1)), ((1,0,1),(0,0,1)),
            ]
            six_cycle_reversed = [(b, a) for (a, b) in six_cycle]
            on_6cycle = sum(1 for e in six_cycle if e in bp)
            on_6cycle_rev = sum(1 for e in six_cycle_reversed if e in bp)
            other = [e for e in bp if e not in six_cycle and e not in six_cycle_reversed]
            print(f"    6-cycle forward edges present: {on_6cycle}/6")
            print(f"    6-cycle reverse edges present: {on_6cycle_rev}/6")
            print(f"    other binary edges: {len(other)}")
            for e in other[:8]:
                print(f"      {e} x{bp[e]}")


if __name__ == "__main__":
    main()
