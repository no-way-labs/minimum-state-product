#!/usr/bin/env python3
"""Phase 0 follow-up: shadow-of-C in forced graph on NG(C).

Prior finding (probe_sk_shortest_cycle): k = L(C) in all 5 dumps; shortest
cycle in forced graph on NG(C) has the same length as C and uses every
processor. Keston: is shadow(C) canonical?

For each of 5 dumps:
  (a) Record firing sequence `pseq` of the shortest cycle.
      Compare to C's firing sequence `movers`:
        * identical
        * cyclic shift (and by how much)
        * reverse
        * reverse-shift
        * neither
  (b) Enumerate ALL length-L(C) simple cycles in forced graph on NG(C)
      up to rotation. Report count.
  (c) For each vertex of the shortest cycle, report min-Hamming distance
      to C. Start-vertex: Hamming-1 neighbor of some C[i]? Which coord p?
      Can we state start = flip(C[i0], p) for specific i0, p determined
      by C?
"""
from __future__ import annotations
from collections import Counter, defaultdict, deque
from itertools import product as iproduct
import importlib.util, json, os, sys, time

sys.setrecursionlimit(100000)
_HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location(
    "probe_c", os.path.join(_HERE, "probe_sk_hamming1_chain_closure_2026-04-17.py"))
probe_c = importlib.util.module_from_spec(spec); spec.loader.exec_module(probe_c)

enumerate_cycles_multistart = probe_c.enumerate_cycles_multistart
forced_successors = probe_c.forced_successors


def build_forced_graph(ms, n, cycle, det):
    cycle_set = set(cycle)
    NG = set()
    for tup in iproduct(*[range(m) for m in ms]):
        if tup not in cycle_set:
            NG.add(tup)
    fwd = defaultdict(list)
    for c in NG:
        for (kind, p, nc) in forced_successors(c, det, n, cycle_set):
            if kind == 'ng':
                fwd[c].append((p, nc))
    return NG, fwd, cycle_set


def shortest_cycle(NG, fwd, cap=80):
    best = None
    for s in NG:
        parent = {s: (None, None)}
        dist = {s: 0}
        q = deque([s])
        found_here = None
        while q:
            v = q.popleft()
            if best is not None and dist[v] + 1 >= best[0]:
                continue
            for (p, nc) in fwd.get(v, []):
                if nc == s:
                    length = dist[v] + 1
                    path, positions = [], []
                    u = v
                    while u is not None:
                        path.append(u)
                        prev, pos = parent[u]
                        if prev is not None:
                            positions.append(pos)
                        u = prev
                    path.reverse(); positions.reverse()
                    positions.append(p)
                    if best is None or length < best[0]:
                        best = (length, path, positions)
                    found_here = length
                    break
                if nc in dist:
                    continue
                dist[nc] = dist[v] + 1
                parent[nc] = (v, p)
                if dist[nc] < cap:
                    q.append(nc)
            if found_here is not None:
                break
    return best


def compare_firing(pseq, movers):
    """Classify pseq vs movers (both length L).
    Returns (mode, shift_or_None)."""
    L = len(movers)
    if len(pseq) != L:
        return ("length_mismatch", None)
    m = tuple(movers); p = tuple(pseq)
    # identical
    for s in range(L):
        if p == m[s:] + m[:s]:
            return ("cyclic_shift" if s != 0 else "identical", s)
    # reverse
    mr = tuple(reversed(m))
    for s in range(L):
        if p == mr[s:] + mr[:s]:
            return ("reverse_shift" if s != 0 else "reverse", s)
    return ("unrelated", None)


def hamming(a, b):
    return sum(1 for x, y in zip(a, b) if x != y)


def find_all_cycles_of_length(NG, fwd, k, cap=2000, time_budget=120):
    """Enumerate up to `cap` distinct simple cycles of length exactly k
    (counting each rotation class once). Returns list of (vseq, pseq).
    time_budget in seconds."""
    out = []
    seen_norm = set()
    t0 = time.time()
    for s in sorted(NG):
        if len(out) >= cap:
            break
        if time.time() - t0 > time_budget:
            break
        # DFS depth up to k
        stack = [(s, (s,), ())]
        while stack:
            if len(out) >= cap or time.time() - t0 > time_budget:
                break
            v, vpath, ppath = stack.pop()
            if len(ppath) >= k:
                continue
            for (p, nc) in fwd.get(v, []):
                if nc == s:
                    if len(ppath) + 1 == k:
                        vp = vpath
                        norm = min(tuple(vp[j:] + vp[:j]) for j in range(k))
                        if norm not in seen_norm:
                            seen_norm.add(norm)
                            out.append((list(vp), list(ppath) + [p]))
                elif nc in vpath:
                    continue
                else:
                    if len(ppath) + 1 < k:
                        stack.append((nc, vpath + (nc,), ppath + (p,)))
    return out, (time.time() - t0)


def describe_start(vseq, cycle):
    """Report Hamming distances from vseq[0] (and from each vertex in vseq)
    to all C configs, plus a succinct start-vertex description."""
    L = len(vseq)
    Lc = len(cycle)
    start = vseq[0]
    dists_to_C = [hamming(start, c) for c in cycle]
    min_d = min(dists_to_C)
    argmin = [i for i, d in enumerate(dists_to_C) if d == min_d]
    # Which coordinates differ for each argmin?
    diffs_by_argmin = {}
    for i in argmin:
        diffs = [p for p in range(len(start)) if start[p] != cycle[i][p]]
        diffs_by_argmin[i] = diffs
    # Hamming distance profile across full shortest-cycle vertex sequence
    all_dists = []
    for v in vseq:
        dv = min(hamming(v, c) for c in cycle)
        all_dists.append(dv)
    dist_hist = Counter(all_dists)
    return {
        "start": list(start),
        "start_min_hamming_to_C": min_d,
        "start_argmin_C_indices": argmin,
        "start_diff_coords_per_argmin": {str(k): v for k, v in diffs_by_argmin.items()},
        "vertex_hamming_distances_to_C": all_dists,
        "hamming_histogram": {str(d): c for d, c in dist_hist.items()},
    }


def do_case(label, n, ms, L_min, L_max, enum_budget=180):
    prod = 1
    for m in ms: prod *= m
    print(f"\n=== {label}: n={n} ms={ms} product={prod} ===", flush=True)
    cycles = enumerate_cycles_multistart(ms, n, L_min=L_min, L_max=L_max,
                                          time_budget=30, max_cycles=3)
    if not cycles:
        print("  NO CYCLES FOUND"); return None
    cycle, movers, det = cycles[0]
    L = len(movers)
    print(f"  picked 1 cycle with L={L}; |Config|={prod}")
    NG, fwd, cycle_set = build_forced_graph(ms, n, cycle, det)
    print(f"  |NG|={len(NG)}  |edges|={sum(len(v) for v in fwd.values())}")
    sc = shortest_cycle(NG, fwd, cap=80)
    if sc is None:
        print("  NO CYCLE FOUND"); return None
    k, vseq, pseq = sc
    print(f"  shortest k={k}  (L(C)={L})  k==L: {k == L}")

    # (a) firing sequence comparison
    mode, shift = compare_firing(pseq, movers)
    print(f"  firing mode: {mode}  shift={shift}")
    print(f"  C movers:   {list(movers)}")
    print(f"  sc pseq:    {list(pseq)}")

    # (c) start description
    start_desc = describe_start(vseq, cycle)
    print(f"  start={start_desc['start']}  min_H_to_C={start_desc['start_min_hamming_to_C']}  "
          f"argmin_C_idx={start_desc['start_argmin_C_indices']}  "
          f"diffs={start_desc['start_diff_coords_per_argmin']}")
    print(f"  hamming histogram along shortest cycle: {start_desc['hamming_histogram']}")

    # (b) uniqueness — enumerate all length-k cycles
    print(f"  enumerating all length-{k} cycles in NG (budget={enum_budget}s)...", flush=True)
    all_cycles, elapsed = find_all_cycles_of_length(NG, fwd, k,
                                                     cap=5000, time_budget=enum_budget)
    print(f"  found {len(all_cycles)} length-{k} cycles (rotation-normalized) in {elapsed:.1f}s")
    # If none found via DFS but sc exists, enumerate timed out before reaching
    # we at least have the sc as a known one.
    firing_modes = Counter()
    shifts_cyclic = []
    shifts_reverse = []
    start_min_hamming_hist = Counter()
    for (vs, ps) in all_cycles:
        m, sh = compare_firing(ps, movers)
        firing_modes[m] += 1
        if m in ("identical", "cyclic_shift"):
            shifts_cyclic.append(sh)
        elif m in ("reverse", "reverse_shift"):
            shifts_reverse.append(sh)
        d0 = min(hamming(vs[0], cc) for cc in cycle)
        start_min_hamming_hist[d0] += 1
    print(f"  firing mode histogram across all length-{k} cycles: {dict(firing_modes)}")
    if shifts_cyclic:
        print(f"    cyclic shifts seen: {sorted(set(shifts_cyclic))} "
              f"(counts: {Counter(shifts_cyclic)})")
    if shifts_reverse:
        print(f"    reverse shifts seen: {sorted(set(shifts_reverse))} "
              f"(counts: {Counter(shifts_reverse)})")
    print(f"  start-vertex min-Hamming-to-C histogram: {dict(start_min_hamming_hist)}")

    return {
        "label": label, "n": n, "ms": list(ms), "L": L, "k": k,
        "k_equals_L": k == L,
        "firing_mode_primary": mode,
        "firing_shift_primary": shift,
        "C_movers": list(movers),
        "sc_pseq": list(pseq),
        "start_desc": start_desc,
        "num_length_L_cycles_found": len(all_cycles),
        "enum_elapsed_s": elapsed,
        "firing_mode_hist_all_L_cycles": dict(firing_modes),
        "cyclic_shifts_seen": sorted(set(shifts_cyclic)),
        "reverse_shifts_seen": sorted(set(shifts_reverse)),
        "start_min_H_hist_all_L_cycles": dict(start_min_hamming_hist),
    }


CASES = [
    ("A_n5",      5, (2, 2, 2, 2, 3),           10, 14, 60),
    ("E_n6_3bin", 6, (2, 2, 2, 3, 3, 3),        14, 18, 120),
    ("B_n7_3bin", 7, (2, 2, 2, 3, 3, 3, 3),     16, 19, 180),
    ("C_n8_3bin", 8, (2, 2, 2, 3, 3, 3, 3, 3),  18, 24, 300),
    ("D_n9_3bin", 9, (2, 2, 2, 3, 3, 3, 3, 3, 3), 20, 26, 420),
]


def main():
    out = []
    t0 = time.time()
    for (label, n, ms, L_min, L_max, enum_budget) in CASES:
        if time.time() - t0 > 28 * 60:
            print(f"\nTIME BUDGET — stopping at {label}"); break
        r = do_case(label, n, ms, L_min, L_max, enum_budget=enum_budget)
        if r is not None: out.append(r)

    print("\n" + "=" * 60)
    print("SHADOW UNIFORMITY REPORT")
    print("=" * 60)
    for r in out:
        print(f"\n  {r['label']}: n={r['n']} L={r['L']} k={r['k']} "
              f"k==L: {r['k_equals_L']}")
        print(f"    firing_mode (primary found cycle): {r['firing_mode_primary']}  "
              f"shift={r['firing_shift_primary']}")
        print(f"    total length-L cycles enumerated: {r['num_length_L_cycles_found']}")
        print(f"    firing-mode histogram across all: {r['firing_mode_hist_all_L_cycles']}")
        print(f"    start min-H to C (primary): "
              f"{r['start_desc']['start_min_hamming_to_C']}  "
              f"argmin_C_idx: {r['start_desc']['start_argmin_C_indices']}")
        print(f"    start min-H histogram across all: {r['start_min_H_hist_all_L_cycles']}")

    all_cyclic = all(r['firing_mode_primary'] in ('identical', 'cyclic_shift')
                     for r in out)
    all_reverse = all(r['firing_mode_primary'] in ('reverse', 'reverse_shift')
                      for r in out)
    print(f"\n  all primary cycles are cyclic shift of C: {all_cyclic}")
    print(f"  all primary cycles are reverse of C:      {all_reverse}")
    any_unrelated = any(r['firing_mode_primary'] == 'unrelated' for r in out)
    print(f"  any primary is unrelated (no shift/reverse match): {any_unrelated}")

    outdir = os.path.join(_HERE, "sk_phase0_out")
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "shadow_cycle.json"), "w") as f:
        json.dump(out, f, indent=2)
    print(f"\n  wrote sk_phase0_out/shadow_cycle.json")


if __name__ == "__main__":
    main()
