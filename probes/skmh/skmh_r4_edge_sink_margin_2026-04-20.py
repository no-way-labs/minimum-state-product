#!/usr/bin/env python3
"""R4 pre-commit probe — edge-sink margin on N_1(C) ∩ VC-NG.

From sk_peel_direct_scope_2026-04-19.md §12:
  T_N1     = N_1(C) ∩ VC-NG
  E_N1     = forced-NG edges (c→c') where c, c' ∈ T_N1
  sinks_N1 = configs in T_N1 with no forced NG-successor in T_N1
  margin   = |E_N1| - (|T_N1| - |sinks_N1|)

If margin ≥ 1 uniformly (with closed-form lower bound or robust
empirical shape), R4 peel-direct ships two SK sorries.

Prior empirical datum: margin ≥ 6 across 656/656 n=5..8 records.

This probe:
  1. Computes margin across many multisets and many cycles per ms,
     including sub / at / super threshold and n=5..8.
  2. Tests whether margin has a clean closed-form in (n, L, ms).
  3. Flags any cycle with margin < 6 or margin = 0.

Exit gates:
  PASS — margin ≥ 1 uniformly, ideally ≥ k for some fixed k.
  FAIL — some cycle has margin < 1, or margin's lower bound is
         cycle-structure-dependent.
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


def value_sets(cycle, n):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n):
            V[i].add(c[i])
    return V


def build_N1_VCNG(ms, cycle, n):
    """T_N1 = N_1(C) ∩ VC-NG.

    For each cycle config c_k and each position q, for each
    v ∈ V[q] \\ {c_k[q]}, generate c with c[q] = v, rest from c_k.
    Accept if c ∉ cycle.
    """
    V = value_sets(cycle, n)
    cycle_set = set(tuple(c) for c in cycle)
    T = set()
    for c in cycle:
        for q in range(n):
            for v in V[q]:
                if v == c[q]:
                    continue
                nc = list(c)
                nc[q] = v
                nc = tuple(nc)
                if nc not in cycle_set:
                    T.add(nc)
    return T


def forced_successors_in(c, det, n, T):
    """List of forced successors of c that land inside T."""
    out = []
    for p in range(n):
        key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
        if key not in det:
            continue
        v = det[key]
        if v == c[p]:
            continue
        nc = list(c)
        nc[p] = v
        nc = tuple(nc)
        if nc in T:
            out.append(nc)
    return out


def margin_data(ms, cycle, det):
    n = len(ms)
    T = build_N1_VCNG(ms, cycle, n)
    out_deg = {c: len(forced_successors_in(c, det, n, T)) for c in T}
    sinks = {c for c, d in out_deg.items() if d == 0}
    non_sinks = {c for c, d in out_deg.items() if d > 0}
    E = sum(out_deg.values())
    margin = E - len(non_sinks)
    # Also: multi-out configs = non-sinks with out-deg >= 2
    multi_out = sum(1 for c in non_sinks if out_deg[c] >= 2)
    max_out = max(out_deg.values()) if out_deg else 0
    return {
        "T": len(T),
        "E": E,
        "sinks": len(sinks),
        "non_sinks": len(non_sinks),
        "margin": margin,
        "multi_out_configs": multi_out,
        "max_out_deg": max_out,
    }


def run_multiset(n, ms, prod, max_cycles=10, time_budget=45.0):
    threshold = M_n_sharp(n)
    tag = ("sub" if prod < threshold
           else "at" if prod == threshold else "super")
    L_max = 3 * n + 6
    cycles = enumerate_cycles_multistart(
        ms, n, L_min=max(6, 2 * n),
        L_max=L_max,
        time_budget=time_budget, max_cycles=max_cycles)
    results = []
    for i, (cyc, movers, det) in enumerate(cycles):
        m = margin_data(ms, cyc, det)
        results.append({
            "n": n, "ms": ms, "prod": prod, "tag": tag,
            "cyc_idx": i, "L": len(cyc),
            **m,
        })
    return results


def main():
    # Broad sweep: many multisets, many cycles each.
    prod_ms = [
        # n=5: sub through super-threshold, including all-binary
        (5, (2, 2, 2, 2, 2), 32),
        (5, (2, 2, 2, 2, 3), 48),
        (5, (2, 2, 2, 3, 3), 72),
        (5, (2, 2, 2, 3, 4), 96),   # at-threshold
        (5, (2, 2, 3, 3, 3), 108),  # super
        (5, (3, 3, 3, 3, 3), 243),  # super symmetric
        (5, (2, 2, 2, 2, 4), 64),
        (5, (2, 2, 2, 4, 4), 128),  # super
        # n=6:
        (6, (2, 2, 2, 2, 3, 3), 144),
        (6, (2, 2, 2, 3, 3, 3), 216),
        (6, (2, 2, 2, 3, 3, 4), 288),  # at
        (6, (2, 2, 3, 3, 3, 3), 324),  # super
        (6, (2, 3, 3, 3, 3, 3), 486),  # super
        # n=7:
        (7, (2, 2, 2, 2, 3, 3, 3), 432),
        (7, (2, 2, 2, 3, 3, 3, 3), 648),
        (7, (2, 2, 2, 3, 3, 3, 4), 864),  # at
        # n=8 (smaller sample to control time):
        (8, (2, 2, 2, 2, 3, 3, 3, 3), 1296),
        (8, (2, 2, 2, 3, 3, 3, 3, 4), 2592),  # at
    ]
    all_results = []
    for n, ms, prod in prod_ms:
        t0 = time.time()
        tag_threshold = M_n_sharp(n)
        tag = ("sub" if prod < tag_threshold
               else "at" if prod == tag_threshold else "super")
        print(f"\n[R4] === ms={ms} n={n} ∏={prod} (M*={tag_threshold}, "
              f"{tag}) ===")
        max_cycles = 10 if n <= 7 else 4
        res = run_multiset(n, ms, prod, max_cycles=max_cycles)
        all_results.extend(res)
        for r in res:
            print(f"    L={r['L']} T={r['T']} E={r['E']} "
                  f"sinks={r['sinks']} non_sinks={r['non_sinks']} "
                  f"margin={r['margin']} "
                  f"(multi_out={r['multi_out_configs']}, "
                  f"max_out={r['max_out_deg']})")
        print(f"    [{time.time()-t0:.1f}s total on this ms]")

    print("\n[R4] ===== SUMMARY =====")
    print(f"{'ms':<25} {'tag':<5} {'L':>3} {'T':>5} {'E':>5} "
          f"{'sinks':>6} {'nonsink':>7} {'margin':>6} {'multi':>5}")
    for r in all_results:
        print(f"{str(r['ms']):<25} {r['tag']:<5} {r['L']:>3} "
              f"{r['T']:>5} {r['E']:>5} {r['sinks']:>6} "
              f"{r['non_sinks']:>7} {r['margin']:>6} "
              f"{r['multi_out_configs']:>5}")

    # Margin direction check
    margins = [r['margin'] for r in all_results]
    print(f"\n[R4] margin across {len(margins)} cycles:")
    print(f"  min = {min(margins)}")
    print(f"  max = {max(margins)}")
    print(f"  avg = {sum(margins)/len(margins):.2f}")
    print(f"  below 1: {sum(1 for m in margins if m < 1)}")
    print(f"  below 6: {sum(1 for m in margins if m < 6)}")
    # violations
    violations = [r for r in all_results if r['margin'] < 1]
    if violations:
        print(f"\n[R4] !!! VIOLATIONS (margin < 1): {len(violations)}")
        for r in violations:
            print(f"    ms={r['ms']} L={r['L']} margin={r['margin']}")
    else:
        print("\n[R4] No violations (margin ≥ 1 uniform).")

    # By threshold tag
    print("\n[R4] ===== BY THRESHOLD =====")
    for tag in ["sub", "at", "super"]:
        entries = [r for r in all_results if r['tag'] == tag]
        if entries:
            mvals = sorted(set(r['margin'] for r in entries))
            print(f"  {tag}: margin range = {mvals}, n={len(entries)} cycles")

    # Closed-form attempt: margin vs L, T
    print("\n[R4] ===== CLOSED-FORM FIT ATTEMPT =====")
    print("  Testing if margin is a function of (n, L) alone...")
    by_nl = defaultdict(list)
    for r in all_results:
        by_nl[(r['n'], r['L'])].append(r['margin'])
    constant_count = 0
    varying_count = 0
    for (n, L), margins_at_nL in sorted(by_nl.items()):
        s = sorted(set(margins_at_nL))
        status = "CONST" if len(s) == 1 else "VARIES"
        if status == "CONST":
            constant_count += 1
        else:
            varying_count += 1
        print(f"    (n={n}, L={L}): margins={s} across "
              f"{len(margins_at_nL)} cycles — {status}")
    print(f"\n  (n,L)-constant margins: {constant_count}")
    print(f"  (n,L)-varying margins: {varying_count}")

    # Also test: T, E, sinks, non_sinks by (n, L)
    print("\n[R4] ===== T, E, non_sinks by (n, L) =====")
    by_nl2 = defaultdict(list)
    for r in all_results:
        by_nl2[(r['n'], r['L'])].append(r)
    for (n, L), entries in sorted(by_nl2.items()):
        Ts = sorted(set(r['T'] for r in entries))
        Es = sorted(set(r['E'] for r in entries))
        NSs = sorted(set(r['non_sinks'] for r in entries))
        print(f"    (n={n}, L={L}) × {len(entries)} cycles: "
              f"T={Ts} E={Es} non_sinks={NSs}")

    return all_results


if __name__ == "__main__":
    main()
