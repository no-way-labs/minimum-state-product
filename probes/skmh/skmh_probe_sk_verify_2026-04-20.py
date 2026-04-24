#!/usr/bin/env python3
"""SKMH E12 — direct SK (sink kernel) computation + (n, L) invariance.

Final probe to sanity-check the E1 Strategy Register claim that |SK|
is constant per (n, L). Compute SK via iterative sink-removal on the
forced graph. Tabulate across cycles. Look for:
  (a) |SK| invariant at fixed (n, L) — confirms E1 building block
  (b) Whether |SK| has any threshold-discriminating signal
  (c) Whether the LARGEST SK-component size has signal

If |SK| is purely (n, L)-driven, the LB factors through (n, L). That's
the correct framing: ms enters only via cycle-length constraints, and
the topological content of SK is about (n, L) pairs, not ms itself.
"""
from __future__ import annotations
import importlib.util
import itertools
import os
import sys
import time
from collections import defaultdict


sys.setrecursionlimit(100000)

_HERE = os.path.dirname(os.path.abspath(__file__))
_CLAUDE = os.path.normpath(
    os.path.join(_HERE, "..", "..", "..", "claude"))
spec = importlib.util.spec_from_file_location(
    "probe_a",
    os.path.join(
        _CLAUDE,
        "probe_sk_hamming1_empty_discriminator_2026-04-17.py"))
probe_a = importlib.util.module_from_spec(spec)
spec.loader.exec_module(probe_a)
enumerate_cycles_multistart = probe_a.enumerate_cycles_multistart


def M_n_sharp(n):
    if 5 <= n <= 8:
        return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


def build_forced_graph(ms, cycle, det):
    n = len(ms)
    cycle_set = set(tuple(c) for c in cycle)
    ng = [tuple(c) for c in itertools.product(*[range(m) for m in ms])
          if tuple(c) not in cycle_set]
    idx = {c: k for k, c in enumerate(ng)}
    # forced edges c -> nc where nc in NG
    adj_out = defaultdict(list)
    adj_in = defaultdict(list)
    for c in ng:
        for p in range(n):
            key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if key in det:
                v = det[key]
                if v == c[p]:
                    continue
                nc = list(c)
                nc[p] = v
                nc = tuple(nc)
                if nc in idx:
                    adj_out[idx[c]].append(idx[nc])
                    adj_in[idx[nc]].append(idx[c])
    return ng, idx, adj_out, adj_in


def compute_sk(ng, idx, adj_out):
    """Iteratively remove configs with no outgoing edge inside the set."""
    alive = set(range(len(ng)))
    out_count = {v: len(adj_out[v]) for v in alive}
    # actually out_count should be over alive-only neighbors. recompute
    # by counting how many of adj_out[v] are alive.

    def recompute_out_counts():
        return {v: sum(1 for w in adj_out[v] if w in alive)
                for v in alive}

    changed = True
    iters = 0
    while changed:
        oc = recompute_out_counts()
        to_remove = {v for v in alive if oc[v] == 0}
        if not to_remove:
            changed = False
        else:
            alive -= to_remove
            iters += 1
    return alive, iters


def run_multiset(n, ms, prod, max_cycles=2):
    threshold = M_n_sharp(n)
    tag = ("sub" if prod < threshold
           else "at" if prod == threshold else "super")
    L_max = 3 * n + 6
    cycles = enumerate_cycles_multistart(
        ms, n, L_min=6, L_max=L_max,
        time_budget=30.0, max_cycles=max_cycles)
    results = []
    for i, (cyc, movers, det) in enumerate(cycles):
        ng, idx, adj_out, adj_in = build_forced_graph(ms, cyc, det)
        t0 = time.time()
        sk_alive, iters = compute_sk(ng, idx, adj_out)
        dt = time.time() - t0
        print(f"[E12] ms={ms} tag={tag} L={len(cyc)} cyc{i}: "
              f"V={len(ng)} |SK|={len(sk_alive)} iters={iters} "
              f"({dt:.2f}s)")
        results.append({
            "n": n, "ms": ms, "prod": prod, "tag": tag,
            "cyc": i, "L": len(cyc), "V_ng": len(ng),
            "SK_size": len(sk_alive),
            "SK_iters": iters,
        })
    return results


def main():
    prod_ms = [
        (5, (2, 2, 2, 2, 2), 32),
        (5, (2, 2, 2, 2, 3), 48),
        (5, (2, 2, 2, 3, 3), 72),
        (5, (2, 2, 3, 3, 3), 108),
        (5, (2, 2, 2, 3, 4), 96),
        (5, (3, 3, 3, 3, 3), 243),
        (6, (2, 2, 2, 2, 3, 3), 144),
        (6, (2, 2, 2, 3, 3, 3), 216),
        (6, (2, 2, 2, 3, 3, 4), 288),
    ]
    all_results = []
    for n, ms, prod in prod_ms:
        print(f"\n[E12] === ms={ms} n={n} ∏={prod} "
              f"(M*={M_n_sharp(n)}) ===")
        res = run_multiset(n, ms, prod)
        all_results.extend(res)

    print("\n===== E12 SK SIZE SUMMARY =====")
    print(f"{'n':>3} {'L':>3} {'ms':<18} {'tag':<5} "
          f"{'V_ng':>6} {'|SK|':>6} {'iters':>6}")
    for r in sorted(all_results, key=lambda r: (r['n'], r['L'], r['ms'])):
        print(f"{r['n']:>3} {r['L']:>3} {str(r['ms']):<18} "
              f"{r['tag']:<5} {r['V_ng']:>6} {r['SK_size']:>6} "
              f"{r['SK_iters']:>6}")

    # Group by (n, L) — does |SK| match within group?
    print("\n===== (n, L) INVARIANCE CHECK =====")
    by_nl = defaultdict(list)
    for r in all_results:
        by_nl[(r['n'], r['L'])].append(r)
    for (n, L), group in sorted(by_nl.items()):
        sk_sizes = sorted(set(r["SK_size"] for r in group))
        ms_tags = [(r['ms'], r['tag'], r['SK_size']) for r in group]
        print(f"  (n={n}, L={L}): |SK| values = {sk_sizes}  "
              f"across {len(group)} cycles")
        if len(sk_sizes) > 1:
            print(f"    (multi-valued — not (n,L)-invariant) "
                  f"details: {ms_tags}")

    # Threshold discriminator?
    print("\n===== SK BY THRESHOLD =====")
    for tag in ["sub", "at", "super"]:
        entries = [r for r in all_results if r['tag'] == tag]
        if entries:
            vals = [r["SK_size"] for r in entries]
            print(f"  {tag}: |SK| = {sorted(set(vals))}  "
                  f"avg={sum(vals)/len(vals):.1f}  n={len(entries)}")


if __name__ == "__main__":
    main()
