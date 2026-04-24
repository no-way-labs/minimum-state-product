#!/usr/bin/env python3
"""Phase 0 paper check — sk_plan_a18.md.

Hard-stop 2 hours. For each of three tight cases:

  * n=5, ms=(2,2,2,2,3)           product 48    (sub-96)
  * n=8, ms=(2,2,2,3,3,3,3,3)     product 1944  (sub-2592)
  * n=9, ms=(2,2,3,3,3,3,3,3,3)   product 4374  (sub-8748)

...enumerate fair simple closed cycles C, build det(C), compute forced
graph on NG(C), dump SK and look for compact structural witnesses:

  (1) Short cycles in the forced graph on NG(C) — 2-cycles, 3-cycles.
  (2) Shadow-cycle: uniform φ : Config → Config with φ(C) a forced cycle
      inside NG(C). Tries: bit-flip at each coordinate (binary coords),
      constant-add at each coordinate (all coords).
  (3) Closed-form rule for peel(N_1(C) ∩ VC-NG) — signature via (q, v, i).

Reuses machinery from probe_sk_hamming1_chain_closure_2026-04-17.py.

Output: stdout report + ./sk_phase0_out/<case>.json dumps.
"""
from __future__ import annotations

from collections import Counter, defaultdict, deque
from itertools import product as iproduct
import importlib.util
import json
import os
import sys
import time

sys.setrecursionlimit(100000)

_HERE = os.path.dirname(os.path.abspath(__file__))


def _load(name, relpath):
    path = os.path.join(_HERE, relpath)
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


probe_c = _load("probe_c", "probe_sk_hamming1_chain_closure_2026-04-17.py")
enumerate_cycles_multistart = probe_c.enumerate_cycles_multistart
build_N1_and_peel = probe_c.build_N1_and_peel
forced_successors = probe_c.forced_successors


# --- forced graph on full NG(C) ---

def build_forced_graph_on_NG(ms, n, cycle, det):
    """Return (NG_set, forward_adj, reverse_adj) on NG(C).

    Edges are forced moves (det entry with val ≠ S) whose target is in NG.
    Forced moves targeting the cycle are omitted (they leave NG).
    """
    cycle_set = set(cycle)
    domains = [range(m) for m in ms]
    NG = set()
    for tup in iproduct(*domains):
        if tup not in cycle_set:
            NG.add(tup)

    fwd = defaultdict(list)
    rev = defaultdict(list)
    for c in NG:
        for (kind, p, nc) in forced_successors(c, det, n, cycle_set):
            if kind == 'ng':
                fwd[c].append((p, nc))
                rev[nc].append((p, c))
    return NG, fwd, rev, cycle_set


def peel_to_fixpoint(NG, fwd):
    """Standard sink-peel: iteratively remove vertices with no outgoing edge in the set."""
    cur = set(NG)
    while True:
        drop = {c for c in cur if not any(nc in cur for (_, nc) in fwd.get(c, []))}
        if not drop:
            return cur
        cur -= drop


def find_2cycles(NG, fwd):
    """Pairs (c,c') in NG×NG, c<c', with c↔c' in forced graph."""
    out = []
    fset = {c: {nc for (_, nc) in fwd.get(c, [])} for c in NG}
    for c in NG:
        for nc in fset[c]:
            if nc <= c:
                continue
            if c in fset.get(nc, set()):
                out.append((c, nc))
    return out


def find_3cycles(NG, fwd, cap=200):
    """c→c'→c''→c in forced graph. Canonicalize by rotating to min."""
    seen = set()
    out = []
    fset = {c: {nc for (_, nc) in fwd.get(c, [])} for c in NG}
    for c in NG:
        for d in fset[c]:
            for e in fset.get(d, set()):
                if c in fset.get(e, set()):
                    tri = tuple(sorted([c, d, e]))
                    if tri in seen:
                        continue
                    seen.add(tri)
                    # only count true 3-cycles (not 2+self, etc.)
                    if len({c, d, e}) == 3:
                        out.append((c, d, e))
                        if len(out) >= cap:
                            return out
    return out


def sk_girth(SK, fwd, cap=8):
    """Shortest cycle length in SK. Iterates BFS from each vertex in SK up
    to depth cap. Returns ∞ if no cycle found ≤ cap; 0 if SK empty."""
    if not SK:
        return 0
    SK_set = set(SK)
    fset = {c: {nc for (_, nc) in fwd.get(c, []) if nc in SK_set} for c in SK}
    best = None
    for s in SK:
        # BFS for shortest cycle back to s
        dist = {s: 0}
        q = deque([s])
        while q:
            v = q.popleft()
            if dist[v] >= cap:
                continue
            for w in fset.get(v, set()):
                if w == s:
                    cand = dist[v] + 1
                    if best is None or cand < best:
                        best = cand
                    break
                if w not in dist:
                    dist[w] = dist[v] + 1
                    q.append(w)
            if best == 2:
                return 2
        if best is not None and best <= 3:
            return best
    return best if best is not None else float('inf')


def count_cycles_of_length_L(SK, fwd, L, cap=1):
    """Existence check: does SK contain a cycle of length exactly L? Returns
    count up to cap (cap=1 is enough for existence)."""
    if not SK:
        return 0
    SK_set = set(SK)
    fset = {c: [nc for (_, nc) in fwd.get(c, []) if nc in SK_set] for c in SK}
    cnt = 0
    # DFS from each vertex, depth exactly L, find return to start
    nodes = sorted(SK)
    for s in nodes:
        # iterative DFS
        stack = [(s, [s])]
        while stack:
            v, path = stack.pop()
            if len(path) == L:
                if s in fset.get(v, []):
                    cnt += 1
                    if cnt >= cap:
                        return cnt
                continue
            for w in fset.get(v, []):
                if w == s and len(path) >= 2:
                    if len(path) == L:
                        cnt += 1
                        if cnt >= cap:
                            return cnt
                elif w not in path:
                    stack.append((w, path + [w]))
    return cnt


# --- shadow-cycle candidates ---

def shadow_by_flip(cycle, coord, ms):
    """φ(c) = flip c[coord] (only for binary coord)."""
    if ms[coord] != 2:
        return None
    return [tuple((c[j] ^ 1) if j == coord else c[j] for j in range(len(c))) for c in cycle]


def shadow_by_add(cycle, coord, delta, ms):
    """φ(c) = c with c[coord] += delta mod ms[coord]."""
    if delta == 0:
        return None
    return [tuple(((c[j] + delta) % ms[j]) if j == coord else c[j]
                  for j in range(len(c))) for c in cycle]


def shadow_is_forced_cycle(shadow, cycle_set, fwd):
    """Check: shadow[i] ∈ NG (not cycle); shadow[i]→shadow[i+1] is a forced
    edge in fwd adjacency on NG."""
    shadow_set = set(shadow)
    L = len(shadow)
    if len(shadow_set) != L:
        return False, "not_distinct"
    for s in shadow:
        if s in cycle_set:
            return False, "overlaps_cycle"
    for i in range(L):
        s = shadow[i]
        t = shadow[(i + 1) % L]
        if t not in {nc for (_, nc) in fwd.get(s, [])}:
            return False, f"missing_edge_{i}"
    return True, "ok"


def try_all_shadows(cycle, ms, n, cycle_set, fwd):
    """Return list of (kind, coord, delta, length_ok) for shadows that work."""
    hits = []
    for coord in range(n):
        sh = shadow_by_flip(cycle, coord, ms)
        if sh is not None:
            ok, why = shadow_is_forced_cycle(sh, cycle_set, fwd)
            if ok:
                hits.append(("flip", coord, 1))
        for delta in range(1, ms[coord]):
            sh = shadow_by_add(cycle, coord, delta, ms)
            if sh is None:
                continue
            ok, why = shadow_is_forced_cycle(sh, cycle_set, fwd)
            if ok:
                hits.append(("add", coord, delta))
    return hits


# --- peel bit-pattern fingerprint (for closed-form hypothesis) ---

def peel_fingerprint(ms, n, cycle, det):
    """Return N_1-peel set + provenance digest for closed-form attempt."""
    N1, adj, peel_set, provenance, V, move_entries, cycle_set = build_N1_and_peel(
        ms, n, cycle, det)
    fp = []
    for c in sorted(peel_set):
        qs = sorted({q for (q, v, i) in provenance[c]})
        vs = sorted({(q, v) for (q, v, i) in provenance[c]})
        idxs = sorted({i for (q, v, i) in provenance[c]})
        fp.append({
            "config": list(c),
            "q_set": list(qs),
            "qv_set": [[q, v] for (q, v) in vs],
            "i_set": list(idxs),
            "provenance": [[q, v, i] for (q, v, i) in sorted(provenance[c])],
        })
    return peel_set, N1, fp


def bijection_diagnostics(peel_set, cycle, ms, n):
    """For the bijection hunt: encode each peel survivor as a bit vector
    relative to its nearest cycle config. Look for uniqueness.

    For each c ∈ peel:
      * nearest cycle config c_ref (min Hamming distance)
      * diff_positions = {i : c[i] ≠ c_ref[i]}
      * bit_at_position = tuple(0 if c[i]==c_ref[i] else 1, for i in 0..n-1)

    Return (bit_vectors, counts).
    """
    cycle_set = set(cycle)
    bits_map = {}
    diff_lens = Counter()
    for c in peel_set:
        # nearest cycle config
        best = None
        for cc in cycle:
            d = sum(1 for i in range(n) if c[i] != cc[i])
            if best is None or d < best[0]:
                best = (d, cc)
        d_min, c_ref = best
        bits = tuple(0 if c[i] == c_ref[i] else 1 for i in range(n))
        bits_map[c] = (bits, d_min, c_ref)
        diff_lens[d_min] += 1
    return bits_map, diff_lens


def run_case(n, ms, L_min, L_max, time_budget_cycles, max_cycles, outdir):
    print(f"\n=== case n={n} ms={ms} (product={1}) ===".replace(
        "product=1", f"product={1}"))
    prod = 1
    for m in ms:
        prod *= m
    print(f"  product = {prod}")

    t0 = time.time()
    cycles = enumerate_cycles_multistart(ms, n, L_min=L_min, L_max=L_max,
                                          time_budget=time_budget_cycles,
                                          max_cycles=max_cycles)
    t_enum = time.time() - t0
    print(f"  enumerated {len(cycles)} cycles in {t_enum:.1f}s")

    if not cycles:
        print("  NO CYCLES FOUND — try wider L_max / more time")
        return {
            "n": n, "ms": list(ms), "product": prod,
            "num_cycles": 0,
        }

    per_cycle = []
    sk_sizes = []
    two_cycle_counts = []
    three_cycle_counts = []
    shadow_hits_counter = Counter()
    peel_sizes = []
    peel_bit_uniqueness = []   # fraction of cycles where bit-vector mapping is injective
    peel_bit_surjective_half = []  # fraction where bit-vector image = ≥ 2^(n-1)

    for idx, (cycle, movers, det) in enumerate(cycles):
        L = len(movers)
        NG, fwd, rev, cycle_set = build_forced_graph_on_NG(ms, n, cycle, det)
        SK = peel_to_fixpoint(NG, fwd)
        twos = find_2cycles(NG, fwd)
        threes = find_3cycles(NG, fwd, cap=20) if not twos else []
        shadows = try_all_shadows(cycle, ms, n, cycle_set, fwd)
        peel_set, N1, peel_fp = peel_fingerprint(ms, n, cycle, det)

        # Bijection diagnostics on peel
        bits_map, diff_lens = bijection_diagnostics(peel_set, cycle, ms, n)
        distinct_bits = len({b for (b, _, _) in bits_map.values()})
        bits_inj = (distinct_bits == len(peel_set)) if peel_set else True

        sk_sizes.append(len(SK))
        two_cycle_counts.append(len(twos))
        three_cycle_counts.append(len(threes))
        peel_sizes.append(len(peel_set))
        peel_bit_uniqueness.append(1 if bits_inj else 0)
        peel_bit_surjective_half.append(1 if distinct_bits >= 2 ** (n - 1) else 0)
        for h in shadows:
            shadow_hits_counter[(h[0], h[2])] += 1

        per_cycle.append({
            "idx": idx, "L": L,
            "NG_size": len(NG), "SK_size": len(SK),
            "num_2cycles": len(twos),
            "num_3cycles": len(threes),
            "num_shadows": len(shadows),
            "shadow_examples": [list(h) for h in shadows[:5]],
            "N1_size": len(N1), "peel_size": len(peel_set),
            "sample_2cycle": [list(twos[0][0]), list(twos[0][1])] if twos else None,
            "sample_3cycle": [list(threes[0][0]), list(threes[0][1]), list(threes[0][2])] if threes else None,
            "peel_distinct_bits": distinct_bits,
            "peel_bits_injective": bits_inj,
            "peel_diff_lens_histogram": dict(diff_lens),
            # For first 3 cycles, dump the full peel details for bijection analysis:
            "peel_detail": peel_fp if idx < 3 else None,
            "peel_bits_sample": (
                [[list(c), list(b), int(d), list(cref)]
                 for c, (b, d, cref) in sorted(bits_map.items())][:20]
                if idx < 3 else None
            ),
        })

        if idx < 5:
            print(f"    cycle[{idx}] L={L} NG={len(NG)} SK={len(SK)} "
                  f"|N1peel|={len(peel_set)} "
                  f"2cyc={len(twos)} 3cyc={len(threes)} shadows={len(shadows)}")
        elif idx == 5:
            print("    ...")

    # Uniform-rule verdict
    all_have_2cyc = all(c > 0 for c in two_cycle_counts)
    all_have_3cyc = all(c > 0 for c in three_cycle_counts) if not all_have_2cyc else None
    all_have_shadow = all(len(r["shadow_examples"]) > 0 for r in per_cycle) if per_cycle else False

    print(f"  SK size range: {min(sk_sizes)}..{max(sk_sizes)} (over {len(cycles)} cycles)")
    print(f"  |N1_peel| range: {min(peel_sizes)}..{max(peel_sizes)}")
    print(f"  |N1_peel|=2^(n-1) ({2**(n-1)}) exact: "
          f"{sum(1 for p in peel_sizes if p == 2**(n-1))}/{len(cycles)}")
    print(f"  2-cycle present on ALL cycles: {all_have_2cyc}")
    if not all_have_2cyc:
        print(f"    (2-cycles on {sum(1 for c in two_cycle_counts if c>0)}/{len(cycles)})")
    if all_have_3cyc is not None:
        print(f"  3-cycle present on ALL cycles: {all_have_3cyc}")
        if not all_have_3cyc:
            print(f"    (3-cycles on {sum(1 for c in three_cycle_counts if c>0)}/{len(cycles)})")
    print(f"  shadow works on ALL cycles: {all_have_shadow}")
    print(f"  shadow hit kinds: {dict(shadow_hits_counter)}")
    print(f"  peel bits-injective on ALL cycles: "
          f"{sum(peel_bit_uniqueness)}/{len(cycles)}")
    print(f"  peel bit-image ≥ 2^(n-1) on ALL cycles: "
          f"{sum(peel_bit_surjective_half)}/{len(cycles)}")

    os.makedirs(outdir, exist_ok=True)
    out = {
        "n": n, "ms": list(ms), "product": prod,
        "num_cycles": len(cycles),
        "sk_sizes_histogram": dict(Counter(sk_sizes)),
        "peel_sizes_histogram": dict(Counter(peel_sizes)),
        "two_cycle_counts_histogram": dict(Counter(two_cycle_counts)),
        "three_cycle_counts_histogram": dict(Counter(three_cycle_counts)),
        "shadow_hit_kinds": {str(k): v for k, v in shadow_hits_counter.items()},
        "verdict": {
            "all_have_2cyc": all_have_2cyc,
            "all_have_3cyc": all_have_3cyc,
            "all_have_shadow": all_have_shadow,
        },
        "per_cycle_first_20": per_cycle[:20],
    }
    fname = f"case_n{n}_ms{'_'.join(str(m) for m in ms)}.json"
    with open(os.path.join(outdir, fname), "w") as f:
        json.dump(out, f, indent=2)
    print(f"  wrote {os.path.join(outdir, fname)}")
    return out


CASES = [
    # (n, ms, L_min, L_max, time_budget_enum, max_cycles, label)
    (5, (2, 2, 2, 2, 3), 5, 20, 30, 200, "small_n_tight"),
    # n=7 ADDED for bijection hunt (|peel|=2^(n-1) exact per prior work)
    (7, (2, 2, 2, 2, 3, 3, 3), 2 * 7 + 2, 2 * 7 + 8, 90, 40, "n7_bijection"),
    (8, (2, 2, 2, 3, 3, 3, 3, 3), 2 * 8 + 2, 2 * 8 + 8, 120, 30, "small_n_tight"),
    # Plan typo: ms=(2,2,3,...,3)^9 has product 8748, not 4374.
    # Use sub-M_9 ms=(2,2,2,3,3,3,3,3,3) product 5832.
    (9, (2, 2, 2, 3, 3, 3, 3, 3, 3), 2 * 9 + 2, 2 * 9 + 8, 180, 20, "large_n_tight"),
]


def main():
    outdir = os.path.join(_HERE, "sk_phase0_out")
    os.makedirs(outdir, exist_ok=True)
    all_results = []
    t_start = time.time()
    for (n, ms, L_min, L_max, tb, mc, label) in CASES:
        res = run_case(n, ms, L_min, L_max, tb, mc, outdir)
        res["label"] = label
        all_results.append(res)
    with open(os.path.join(outdir, "summary.json"), "w") as f:
        json.dump(all_results, f, indent=2)
    dt = time.time() - t_start
    print(f"\n=== Phase 0 sweep done in {dt:.1f}s ===")
    # Verdict line
    all_have_2cyc = all(r.get("verdict", {}).get("all_have_2cyc") for r in all_results if r.get("num_cycles"))
    all_have_shadow = all(r.get("verdict", {}).get("all_have_shadow") for r in all_results if r.get("num_cycles"))
    print(f"  UNIFORM 2-cycle across all three cases: {all_have_2cyc}")
    print(f"  UNIFORM shadow across all three cases: {all_have_shadow}")


if __name__ == "__main__":
    main()
