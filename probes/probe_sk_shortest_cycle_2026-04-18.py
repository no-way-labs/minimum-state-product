#!/usr/bin/env python3
"""Phase 0 addendum — characterize the shortest cycle in forced graph on NG(C).

Phase 0 ruled out 2-cycles and 3-cycles. This probe asks: what IS the
shortest cycle, and does it have a uniform shape across dumps?

For each of 5 dumps (one per case + an extra), pick ONE enumerated cycle C.
Build forced graph on NG(C). Run multi-source BFS to find the globally
shortest cycle. Record:

  * length k
  * firing positions (p_0, ..., p_{k-1})
  * multiset of (p_i, pre_value, post_value) — the det edges traversed
  * positional pattern normalized mod rotation

GO iff all 5 dumps yield the same shape (same k, same positional pattern
up to rotation/relabelling).
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
    # Edges with (position, from, to) — target must be in NG for SK structure.
    fwd = defaultdict(list)
    for c in NG:
        for (kind, p, nc) in forced_successors(c, det, n, cycle_set):
            if kind == 'ng':
                fwd[c].append((p, nc))
    return NG, fwd, cycle_set


def shortest_cycle(NG, fwd, cap=60):
    """Return (length, vertex_sequence, position_sequence) of the shortest
    directed cycle in fwd restricted to NG. BFS from each vertex, keep
    parent info so we can reconstruct the cycle."""
    best = None  # (k, vseq, pseq)
    for s in NG:
        # BFS — track parent and position used.
        parent = {s: (None, None)}  # vertex -> (prev_vertex, position_used)
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
                    # reconstruct vertex path s -> ... -> v -> s
                    path = []
                    positions = []
                    u = v
                    while u is not None:
                        path.append(u)
                        prev, pos = parent[u]
                        if prev is not None:
                            positions.append(pos)
                        u = prev
                    path.reverse()
                    positions.reverse()
                    positions.append(p)  # final edge v -> s
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
        if best is not None and best[0] == 2:
            return best  # can't do better
    return best


def characterize_cycle(vseq, pseq, n):
    """Given a found cycle vertex sequence v_0 -> v_1 -> ... -> v_0
    and positions (edge i uses p_i), describe the shape."""
    k = len(pseq)
    # Flip pattern: for each edge i, (position, pre, post)
    flips = []
    for i in range(k):
        u = vseq[i]
        v = vseq[(i + 1) % k]
        p = pseq[i]
        flips.append((p, u[p], v[p]))
    # Coord-flip pattern: sequence of positions
    pos_seq = tuple(pseq)
    # Normalize by rotation: take lex-min rotation of pos_seq
    rotations = [tuple(pos_seq[j:] + pos_seq[:j]) for j in range(k)]
    norm_positions = min(rotations)
    # Distinct positions used
    distinct_pos = sorted(set(pseq))
    # Position count multiset
    pos_hist = Counter(pseq)
    return {
        "k": k,
        "positions_raw": list(pseq),
        "positions_norm_rot": list(norm_positions),
        "distinct_positions": distinct_pos,
        "num_distinct_positions": len(distinct_pos),
        "pos_histogram": {str(p): c for p, c in pos_hist.items()},
        "flips": [[p, int(a), int(b)] for (p, a, b) in flips],
    }


def find_all_short_cycles_of_length(NG, fwd, k, cap=5):
    """Enumerate up to `cap` cycles of length exactly k starting from different
    vertices. Returns list of (vseq, pseq)."""
    out = []
    seen_norm = set()
    NG_list = sorted(NG)
    for s in NG_list:
        if len(out) >= cap:
            break
        # DFS depth k
        stack = [(s, [s], [])]
        while stack and len(out) < cap:
            v, vpath, ppath = stack.pop()
            if len(vpath) > k:
                continue
            for (p, nc) in fwd.get(v, []):
                if nc == s and len(ppath) + 1 == k:
                    # found cycle
                    norm = min(tuple(vpath[j:] + vpath[:j]) for j in range(k))
                    if norm in seen_norm:
                        continue
                    seen_norm.add(norm)
                    out.append((list(vpath), list(ppath) + [p]))
                    if len(out) >= cap:
                        break
                elif nc not in vpath and len(ppath) + 1 < k:
                    stack.append((nc, vpath + [list(nc) and tuple(nc)], ppath + [p]))
        if len(out) >= cap:
            break
    return out


def do_case(label, n, ms, L_min, L_max):
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
    t0 = time.time()
    NG, fwd, cycle_set = build_forced_graph(ms, n, cycle, det)
    t1 = time.time()
    print(f"  |NG|={len(NG)}  |edges|={sum(len(v) for v in fwd.values())}  "
          f"(forced_graph built in {t1-t0:.1f}s)")
    sc = shortest_cycle(NG, fwd, cap=80)
    t2 = time.time()
    if sc is None:
        print("  NO CYCLE FOUND in forced graph on NG — SK should be empty!")
        return None
    k, vseq, pseq = sc
    print(f"  shortest cycle length k={k}  (BFS in {t2-t1:.1f}s)")
    char = characterize_cycle(vseq, pseq, n)
    print(f"  positions (normalized rot): {char['positions_norm_rot']}")
    print(f"  distinct positions: {char['distinct_positions']} "
          f"(count={char['num_distinct_positions']})")
    print(f"  pos histogram: {char['pos_histogram']}")
    print(f"  flips: {char['flips']}")
    print(f"  vertex sample: {[list(v) for v in vseq[:min(6, k)]]}")
    # Also enumerate a few OTHER shortest cycles (same k) to check uniformity of shape within this dump
    others = find_all_short_cycles_of_length(NG, fwd, k, cap=5)
    other_shapes = []
    for (vs, ps) in others:
        ch = characterize_cycle(vs, ps, n)
        other_shapes.append((tuple(ch['positions_norm_rot']),
                              ch['num_distinct_positions']))
    shape_counter = Counter(other_shapes)
    print(f"  other k={k}-cycles sampled: {len(others)}  shape_histogram: "
          f"{[(list(s[0]), s[1], c) for s, c in shape_counter.most_common(5)]}")
    return {
        "label": label, "n": n, "ms": list(ms), "prod": prod, "L": L,
        "|NG|": len(NG),
        "shortest_cycle": {
            "k": k,
            "positions_norm_rot": char['positions_norm_rot'],
            "distinct_positions": char['distinct_positions'],
            "num_distinct_positions": char['num_distinct_positions'],
            "pos_histogram": char['pos_histogram'],
            "flips": char['flips'],
        },
        "other_k_shapes_sample": [
            {"positions_norm_rot": list(s[0]), "num_distinct": s[1], "count": c}
            for s, c in shape_counter.most_common(10)
        ],
    }


CASES = [
    ("A_n5", 5, (2, 2, 2, 2, 3), 10, 14),
    ("B_n7_3bin", 7, (2, 2, 2, 3, 3, 3, 3), 16, 19),
    ("C_n8_3bin", 8, (2, 2, 2, 3, 3, 3, 3, 3), 18, 24),
    ("D_n9_3bin", 9, (2, 2, 2, 3, 3, 3, 3, 3, 3), 20, 26),
    ("E_n6_3bin", 6, (2, 2, 2, 3, 3, 3), 14, 18),
]


def main():
    all_res = []
    t0 = time.time()
    for (label, n, ms, L_min, L_max) in CASES:
        if time.time() - t0 > 28 * 60:
            print(f"\nTIME BUDGET EXCEEDED (30min) — stopping at {label}")
            break
        res = do_case(label, n, ms, L_min, L_max)
        if res is not None:
            all_res.append(res)

    print("\n" + "=" * 60)
    print("UNIFORMITY REPORT")
    print("=" * 60)
    ks = [r["shortest_cycle"]["k"] for r in all_res]
    print(f"  ks per dump: {ks}")
    pos_shapes = [tuple(r["shortest_cycle"]["positions_norm_rot"]) for r in all_res]
    num_distinct_per_dump = [r["shortest_cycle"]["num_distinct_positions"] for r in all_res]
    print(f"  num_distinct_positions per dump: {num_distinct_per_dump}")
    print(f"  positions_norm_rot per dump:")
    for r in all_res:
        sc = r["shortest_cycle"]
        print(f"    {r['label']}: k={sc['k']}  positions={sc['positions_norm_rot']}  "
              f"distinct={sc['distinct_positions']}  hist={sc['pos_histogram']}")
    all_k_same = len(set(ks)) == 1
    all_shape_same = len(set(pos_shapes)) == 1
    print(f"\n  all same k: {all_k_same}  (ks: {set(ks)})")
    print(f"  all same normalized position sequence: {all_shape_same}")
    print(f"  all same num_distinct: {len(set(num_distinct_per_dump)) == 1}")

    with open(os.path.join(_HERE, "sk_phase0_out", "shortest_cycles.json"), "w") as f:
        json.dump(all_res, f, indent=2)
    print(f"\n  wrote sk_phase0_out/shortest_cycles.json")


if __name__ == "__main__":
    main()
