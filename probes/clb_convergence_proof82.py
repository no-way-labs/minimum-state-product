#!/usr/bin/env python3
"""
CONVERGENCE PROOF 82: Per-step monotonicity verification
=========================================================
KEY CONJECTURE (from analytical case analysis):
  Δ(int_20 + int_21) ≤ 0 on EVERY SINGLE STEP in the bad-config graph.

This is a PER-STEP result, not just excursion-level. If true:
- Proves Layer 0 analytically for ALL n
- The proof is: enumerate all (L,S,R)→out triples, show Δ ≤ 0 for each

Also checks:
- Δint_21 per-step (known to fail: (2,0,1)→{1,2} gives +1)
- Δ(intj20+intj21) per-step (does it also hold per-step?)
- Characterize the "zero residual" (edges where int_20+int_21 preserved)
"""
import sys
import os
import time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter


def int_21(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)


def int_20(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)


def int_j_20(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)


def int_j_21(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)


def exposed_2_count(c, n):
    """int_20 + int_21: count of interior j where c[j]=2, c[j+1] in {0,1}."""
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] in (0, 1))


def exposed_2_weight(c, n):
    """intj20 + intj21: position-weighted exposed interior 2's."""
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] in (0, 1))


def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])


def delta_fc_val(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))


def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in range(5, 13):
        t0 = time.time()
        ms, fs = build_system(n_val)
        result = verify_system(ms, fs)
        assert result['valid']
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_list = [c for c in all_configs if c not in good_set]
        bad_set = set(bad_list)
        n = n_val

        # === 1. Per-step verification ===
        # For EVERY edge (c → c') in bad-to-bad graph, check quantities
        d_exp2_cnt = Counter()  # Δ(int_20+int_21) distribution
        d_int21 = Counter()     # Δint_21 distribution
        d_exp2_wt = Counter()   # Δ(intj20+intj21) distribution
        d_fc_vs_exp2 = Counter()  # joint (Δfc, Δexp2_cnt sign)

        exp2_violations = 0
        int21_violations = 0
        wt_violations = 0
        total_edges = 0

        # Track per-Δfc class
        dfc_classes = defaultdict(lambda: Counter())  # dfc -> {quantity: Counter}

        for c in bad_list:
            e2_c = exposed_2_count(c, n)
            i21_c = int_21(c, n)
            ew_c = exposed_2_weight(c, n)

            for i in range(n):
                L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
                out = fs[i](L, S, R)
                if out != S:
                    lst = list(c); lst[i] = out; succ = tuple(lst)
                    if succ in bad_set:
                        total_edges += 1
                        dfc = delta_fc_val(L, S, R, out)

                        e2_s = exposed_2_count(succ, n)
                        i21_s = int_21(succ, n)
                        ew_s = exposed_2_weight(succ, n)

                        de2 = e2_s - e2_c
                        di21 = i21_s - i21_c
                        dew = ew_s - ew_c

                        d_exp2_cnt[de2] += 1
                        d_int21[di21] += 1
                        d_exp2_wt[dew] += 1

                        if de2 > 0:
                            exp2_violations += 1
                        if di21 > 0:
                            int21_violations += 1
                        if dew > 0:
                            wt_violations += 1

                        # Joint
                        d_fc_vs_exp2[(dfc, de2)] += 1

                        # Per Δfc class
                        dfc_classes[dfc]['de2:' + str(de2)] += 1
                        dfc_classes[dfc]['di21:' + str(di21)] += 1

        elapsed = time.time() - t0
        print(f"\n{'='*70}")
        print(f"n={n}: {total_edges} bad→bad edges ({elapsed:.1f}s)")

        print(f"\n  Per-step Δ(int_20+int_21): {dict(sorted(d_exp2_cnt.items()))}")
        print(f"  VIOLATIONS (>0): {exp2_violations} / {total_edges}"
              f" {'*** ALL ≤ 0 ***' if exp2_violations == 0 else '!!! FAILS !!!'}")

        print(f"\n  Per-step Δint_21: {dict(sorted(d_int21.items()))}")
        print(f"  VIOLATIONS (>0): {int21_violations} / {total_edges}"
              f" {'*** ALL ≤ 0 ***' if int21_violations == 0 else '(expected violations)'}")

        print(f"\n  Per-step Δ(intj20+intj21): min={min(d_exp2_wt.keys())}, "
              f"max={max(d_exp2_wt.keys())}")
        print(f"  VIOLATIONS (>0): {wt_violations} / {total_edges}"
              f" {'*** ALL ≤ 0 ***' if wt_violations == 0 else '(violations exist)'}")

        # Joint (Δfc, Δexp2_count)
        print(f"\n  Joint (Δfc, Δ(int20+int21)):")
        for (dfc, de2), cnt in sorted(d_fc_vs_exp2.items()):
            marker = " !!!" if de2 > 0 else ""
            print(f"    Δfc={dfc:+d}, Δexp2={de2:+d}: {cnt}{marker}")

        # Per Δfc class: int_21 range
        print(f"\n  Per Δfc class details:")
        for dfc in sorted(dfc_classes.keys()):
            items = dfc_classes[dfc]
            di21_vals = {k: v for k, v in items.items() if k.startswith('di21:')}
            de2_vals = {k: v for k, v in items.items() if k.startswith('de2:')}
            di21_range = sorted(int(k.split(':')[1]) for k in di21_vals)
            de2_range = sorted(int(k.split(':')[1]) for k in de2_vals)
            total = sum(di21_vals.values())
            print(f"    Δfc={dfc:+d}: {total} edges, "
                  f"Δint_21 ∈ [{di21_range[0]},{di21_range[-1]}], "
                  f"Δexp2 ∈ [{de2_range[0]},{de2_range[-1]}]")

        # === 2. Zero-residual analysis ===
        # Edges where int_20+int_21 is preserved
        zero_exp2_edges = 0
        zero_exp2_dfc = Counter()
        zero_exp2_di21 = Counter()
        zero_both = 0  # Also int_21 preserved

        for c in bad_list:
            e2_c = exposed_2_count(c, n)
            i21_c = int_21(c, n)
            for i in range(n):
                L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
                out = fs[i](L, S, R)
                if out != S:
                    lst = list(c); lst[i] = out; succ = tuple(lst)
                    if succ in bad_set:
                        e2_s = exposed_2_count(succ, n)
                        i21_s = int_21(succ, n)
                        if e2_s == e2_c:
                            zero_exp2_edges += 1
                            dfc = delta_fc_val(L, S, R, out)
                            zero_exp2_dfc[dfc] += 1
                            di21 = i21_s - i21_c
                            zero_exp2_di21[di21] += 1
                            if i21_s == i21_c:
                                zero_both += 1

        print(f"\n  Zero-exp2 residual: {zero_exp2_edges} / {total_edges} "
              f"({100*zero_exp2_edges/total_edges:.1f}%)")
        print(f"    Δfc distribution: {dict(sorted(zero_exp2_dfc.items()))}")
        print(f"    Δint_21 distribution: {dict(sorted(zero_exp2_di21.items()))}")
        print(f"    Both preserved: {zero_both} "
              f"({100*zero_both/total_edges:.1f}% of total)")

    print(f"\n{'='*70}")
    print("DONE")


if __name__ == '__main__':
    main()
