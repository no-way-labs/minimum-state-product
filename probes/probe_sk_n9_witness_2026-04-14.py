#!/usr/bin/env python3
"""n=9 witness SK analysis + ternary-strip fiber structure.

Goals:
  (A) Extract the n=9 CLB witness cycle from clb_witness_8748 and
      compute SK(det(C_w9)) directly. Predict SK = 0.
  (B) Verify monotonicity: SK(det(C)) ⊆ SK(full_completion). Both
      should be 0 for the valid witness.
  (C) Binary projection at k=2: just a 2-cube (4 vertices). See if
      the binary-cube projection is empty, degenerate, or whatever.
  (D) Ternary-strip fiber analysis. With k=2 and 7 ternary positions,
      the "action" is in the ternary strip. Project SK and good cycle
      onto the 7 ternary coords. Look at:
        - how the 7-ternary fiber space (3^7 = 2187 cells) is used
        - binary-state-conditional fiber coverage
        - whether there's a rigid structural pattern analogous to
          the binary-cube skeleton at k≥3
"""

import os
import sys
from itertools import product as iproduct
from collections import defaultdict, Counter

sys.path.insert(0, os.path.dirname(__file__))
from clb_witness_8748 import build_system


def extract_cycle_via_single_priv(ms, fs, n):
    all_configs = list(iproduct(*[range(m) for m in ms]))

    def priv(cfg):
        out = []
        for i in range(n):
            L = cfg[(i - 1) % n]; S = cfg[i]; R = cfg[(i + 1) % n]
            if fs[i](L, S, R) != S:
                out.append(i)
        return out

    def move(cfg, p):
        L = cfg[(p - 1) % n]; S = cfg[p]; R = cfg[(p + 1) % n]
        lst = list(cfg); lst[p] = fs[p](L, S, R)
        return tuple(lst)

    single = {}
    for cfg in all_configs:
        pv = priv(cfg)
        if len(pv) == 1:
            single[cfg] = (move(cfg, pv[0]), pv[0])

    # Walk to find cycle.
    visited_global = set()
    for start in single:
        if start in visited_global:
            continue
        path = [start]; movers = []; visited = {start}; cur = start
        while cur in single:
            nxt, mv = single[cur]
            movers.append(mv)
            if nxt == start:
                return path, movers
            if nxt in visited:
                break
            visited.add(nxt); visited_global.add(nxt); path.append(nxt)
            cur = nxt
    return None, None


def extract_det_from_cycle(cycle, ms, n):
    det = {}
    L = len(cycle)
    for idx in range(L):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % L]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return None
        mover = diffs[0]
        Lm = c[(mover - 1) % n]; Sm = c[mover]; Rm = c[(mover + 1) % n]
        km = (mover, Lm, Sm, Rm)
        if km in det and det[km] != c_next[mover]:
            return None
        det[km] = c_next[mover]
        for i in range(n):
            if i == mover: continue
            Li = c[(i - 1) % n]; Si = c[i]; Ri = c[(i + 1) % n]
            ki = (i, Li, Si, Ri)
            if ki in det and det[ki] != Si:
                return None
            det[ki] = Si
    return det


def build_forced_graph(ms, n, det, good_set):
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
    ng_set = set(non_good)
    adj = defaultdict(list)
    for c in non_good:
        for p in range(n):
            Lp = c[(p - 1) % n]; Sp = c[p]; Rp = c[(p + 1) % n]
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


def main():
    print("Building n=9 witness system ...")
    ms, fs, comp = build_system()
    n = len(ms)
    print(f"  ms = {tuple(ms)}")
    print(f"  |comp| = {len(comp)}  (full transition table entries)")

    # Extract good cycle.
    print("\nExtracting good cycle via single-privileged walk ...")
    cycle, movers = extract_cycle_via_single_priv(ms, fs, n)
    if cycle is None:
        print("  FAILED")
        return
    print(f"  cycle length: {len(cycle)}")
    print(f"  mover sequence: {movers}")
    good_set = set(cycle)

    # Extract det(C) from the cycle alone (not the full comp).
    print("\nExtracting det(C_w9) from cycle alone (ignoring completion) ...")
    det_cycle = extract_det_from_cycle(cycle, ms, n)
    if det_cycle is None:
        print("  FAILED — cycle inconsistent")
        return
    print(f"  |det(C)| = {len(det_cycle)}")

    # Convert comp (dict of (p,L,S,R)->out) into det_full format.
    det_full = dict(comp)
    print(f"  |det_full| = {len(det_full)}")

    # Build forced graphs and compute SKs.
    print("\n(A) SK(det(C_w9)) — cycle-only forcing:")
    ng_c, _, adj_c = build_forced_graph(ms, n, det_cycle, good_set)
    sk_c, rounds_c = sink_kernel(ng_c, adj_c)
    print(f"  |non-good| = {len(ng_c)}")
    print(f"  |bad edges| = {sum(len(adj_c[c]) for c in ng_c)}")
    print(f"  |SK| = {len(sk_c)}  (rounds = {rounds_c})")

    print("\n(B) SK(det_full) — full completion:")
    ng_f, _, adj_f = build_forced_graph(ms, n, det_full, good_set)
    sk_f, rounds_f = sink_kernel(ng_f, adj_f)
    print(f"  |non-good| = {len(ng_f)}")
    print(f"  |bad edges| = {sum(len(adj_f[c]) for c in ng_f)}")
    print(f"  |SK| = {len(sk_f)}  (rounds = {rounds_f})")

    subset_ok = set(sk_c).issubset(set(sk_f))
    print(f"  monotonicity SK(det) ⊆ SK(full): {subset_ok}")

    # Now structural analysis.
    bpos = [i for i, m in enumerate(ms) if m == 2]
    tpos = [i for i, m in enumerate(ms) if m != 2]
    print(f"\n  binary positions: {bpos}  (k={len(bpos)})")
    print(f"  ternary positions: {tpos}")

    # (C) Binary projection (k=2, so 4 vertices).
    print("\n(C) Binary projection of entire non-good set:")
    bproj_count = defaultdict(int)
    for c in ng_c:
        bp = tuple(c[i] for i in bpos)
        bproj_count[bp] += 1
    print(f"  non-good binary distribution ({len(bproj_count)}/4 binary states):")
    for bp in sorted(bproj_count):
        print(f"    {bp}: {bproj_count[bp]} configs")
    print(f"  good cycle binary distribution:")
    good_bproj_count = defaultdict(int)
    for c in cycle:
        bp = tuple(c[i] for i in bpos)
        good_bproj_count[bp] += 1
    for bp in sorted(good_bproj_count):
        print(f"    {bp}: {good_bproj_count[bp]} configs")

    # (D) Ternary-strip fiber analysis.
    print("\n(D) Ternary-strip fiber analysis:")
    print(f"  ternary strip: positions {tpos}  (length {len(tpos)}, "
          f"3^{len(tpos)} = {3**len(tpos)} cells)")

    # For each binary state, count how many ternary fibers the good
    # cycle vs non-good occupy.
    fibers_by_binary = defaultdict(lambda: {"good": set(), "ng": set()})
    for c in cycle:
        bp = tuple(c[i] for i in bpos)
        fib = tuple(c[i] for i in tpos)
        fibers_by_binary[bp]["good"].add(fib)
    for c in ng_c:
        bp = tuple(c[i] for i in bpos)
        fib = tuple(c[i] for i in tpos)
        fibers_by_binary[bp]["ng"].add(fib)
    total_fibers = 3 ** len(tpos)
    print(f"  coverage of 3^{len(tpos)} fiber space per binary state:")
    for bp in sorted(fibers_by_binary):
        gcnt = len(fibers_by_binary[bp]["good"])
        ncnt = len(fibers_by_binary[bp]["ng"])
        print(f"    {bp}: good={gcnt}, non-good={ncnt}, "
              f"total={gcnt+ncnt}/{total_fibers}")

    # Ternary fiber weight histogram (Hamming weight on the ternary strip,
    # meaning how many positions are at 0 vs 1 vs 2).
    print("\n  ternary fiber value distribution (good cycle):")
    val_counts = [Counter() for _ in tpos]
    for c in cycle:
        for idx, tp in enumerate(tpos):
            val_counts[idx][c[tp]] += 1
    for idx, tp in enumerate(tpos):
        counts = val_counts[idx]
        print(f"    position {tp}: {dict(counts)}")

    # Structural: is there a pattern in which ternary values are
    # visited at each binary state?
    print("\n  ternary fiber value signature per binary state (good cycle):")
    for bp in sorted(fibers_by_binary):
        fibers = sorted(fibers_by_binary[bp]["good"])
        if len(fibers) <= 5:
            print(f"    {bp}: {fibers}")
        else:
            print(f"    {bp}: {len(fibers)} fibers, first 5: {fibers[:5]}")

    # For sink kernel (empty or not), dump what little is left.
    print("\n(E) Sink-kernel structural dump:")
    if len(sk_c) == 0:
        print("  SK(det(C_w9)) is EMPTY — witness confirmed via cycle-only "
              "forcing alone.")
    else:
        print(f"  SK(det(C_w9)) has {len(sk_c)} configs. Binary distribution:")
        sk_bproj = defaultdict(int)
        for c in sk_c:
            bp = tuple(c[i] for i in bpos)
            sk_bproj[bp] += 1
        for bp in sorted(sk_bproj):
            print(f"    {bp}: {sk_bproj[bp]}")
    if len(sk_f) == 0:
        print("  SK(det_full) is EMPTY — full completion is valid.")
    else:
        print(f"  SK(det_full) has {len(sk_f)} configs.")

    print("\nDone.")


if __name__ == "__main__":
    main()
