#!/usr/bin/env python3
"""Option (ii): T UB tightening — tripwire T1' + α floor (2026-04-19).

Reuses existing 340-record gates JSON. Two checks:

  T1' variance: spread of T/(L·Σμ) at fixed (n, L, ms). If any key has
  max/min > 2×, T UB is cycle-dependent — T1 regression, abort.

  α floor: α_worst(n) = max over records of T/(L·Σμ) per n. Project to
  n=9 binary-dominated regime. Need α ≤ 0.5 for ansatz closure at
  n=9 binary-dom. If projected α_worst > 0.7, declare R4 failed.

Ansatz closure pressure-test at projected worst n=9 binary-dom:
  need  L·(n−3)/n·Σμ − ε·L·Σμ + λ·cross_cand + sinks − T ≥ 1
  with T = α·L·Σμ:
    L·Σμ·((n−3)/n − ε − α) + λ·cross_cand + sinks ≥ 1
  n=9, ε≈0.03, λ≈0.15:
    L·Σμ·(0.667 − 0.03 − α) + 0.15·cross_cand + sinks ≥ 1
  Need α < 0.637 for the Σμ term to even be positive.
"""

import json
import os
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
DATA_PATH = os.path.normpath(
    os.path.join(HERE, '..', 'lean', 'docs', 'sk', 'sk_phase0_out',
                 'r4_read2_session2_gates_2026-04-19.json')
)

with open(DATA_PATH) as f:
    records = json.load(f)
print(f"Loaded {len(records)} records from {DATA_PATH}\n")

# Compute T/(L·Σμ) per record
for r in records:
    lsm = r['L'] * r['Sigma_mu']
    r['T_over_LSm'] = r['T_size'] / lsm if lsm > 0 else 0.0

# --- Tripwire T1': variance at fixed (n, L, ms) ---
print("=" * 72)
print("Tripwire T1': spread of T/(L·Σμ) at fixed (n, L, ms)")
print("=" * 72)

by_key = defaultdict(list)
for r in records:
    by_key[(r['n'], r['L'], tuple(r['ms']))].append(r['T_over_LSm'])

multi_keys = {k: xs for k, xs in by_key.items() if len(xs) >= 2}
print(f"  {len(multi_keys)} multi-cycle keys")

spreads = []
for key, xs in multi_keys.items():
    lo, hi = min(xs), max(xs)
    rr = hi / lo if lo > 0 else float('inf')
    spreads.append((rr, key, xs))

spreads.sort(key=lambda t: -t[0])
print(f"\n  Top 5 spreads:")
for rr, key, xs in spreads[:5]:
    print(f"    spread={rr:.3f}x  key={key}  T/LSm range=[{min(xs):.4f}, {max(xs):.4f}]")

max_spread = spreads[0][0] if spreads else 0.0
print(f"\n  Max spread: {max_spread:.3f}x")
if max_spread > 2.0:
    print(f"  *** TRIPWIRE T1' FIRES: T/(L·Σμ) varies > 2× at fixed (n, L, ms). ***")
    print(f"  T UB is cycle-dependent. T1 regression. ABORT option (ii).")
    abort = True
else:
    print(f"  Tripwire T1' clean (spread ≤ 2×). T UB is cycle-shape-free on this axis.")
    abort = False

# --- α floor per n ---
print("\n" + "=" * 72)
print("α floor: α_worst(n) = max T/(L·Σμ) per n")
print("=" * 72)

by_n = defaultdict(list)
for r in records:
    by_n[r['n']].append(r)

print(f"\n  {'n':>3} | {'recs':>5} | α_worst | α_mean  | α_min   | "
      f"α at binary-dom")
for n in sorted(by_n):
    rs = by_n[n]
    alphas = [r['T_over_LSm'] for r in rs]
    amin = min(alphas); amax = max(alphas); amean = sum(alphas) / len(alphas)
    # binary-dominated slice: ms with at least ceil(2n/3) binary positions
    bin_thresh = (2 * n + 2) // 3
    bin_dom = [r['T_over_LSm'] for r in rs
               if sum(1 for m in r['ms'] if m == 2) >= bin_thresh]
    if bin_dom:
        adm = f"{max(bin_dom):.3f} (N={len(bin_dom)})"
    else:
        adm = "no records"
    print(f"  {n:>3} | {len(rs):>5} | {amax:.3f}   | {amean:.3f}   | "
          f"{amin:.3f}   | {adm}")

# --- Worst-record inspection ---
print("\n" + "=" * 72)
print("Worst records by T/(L·Σμ)")
print("=" * 72)

records_sorted = sorted(records, key=lambda r: -r['T_over_LSm'])
print(f"\n  Top 10 records by T/(L·Σμ):")
for r in records_sorted[:10]:
    bin_n = sum(1 for m in r['ms'] if m == 2)
    print(f"    T/LSm={r['T_over_LSm']:.3f}  n={r['n']}  ms={r['ms']}  "
          f"L={r['L']}  Σμ={r['Sigma_mu']}  T={r['T_size']}  bin={bin_n}")

# --- Projection to n=9 binary-dominated ---
print("\n" + "=" * 72)
print("Projection: α needed at n=9 binary-dominated")
print("=" * 72)

# The ansatz at n=9:  L·Σμ·((n-3)/n − ε − α) + λ·cross_cand + sinks ≥ 1
# For bound to hold with zero cross+sinks cushion, need α < (n-3)/n − ε
# n=9, ε = 0.03: threshold α* = 6/9 − 0.03 = 0.637
# To have cushion of 10%, need α ≤ 0.57
# Keston's tripwire: need α ≤ 0.5 for closure, if projection > 0.7 declare failed.

# Extrapolate α trend in n
ns = sorted(by_n.keys())
alpha_worst_by_n = {n: max(r['T_over_LSm'] for r in by_n[n]) for n in ns}
alpha_worst_bindom = {}
for n in ns:
    bin_thresh = (2 * n + 2) // 3
    slice_r = [r['T_over_LSm'] for r in by_n[n]
               if sum(1 for m in r['ms'] if m == 2) >= bin_thresh]
    if slice_r:
        alpha_worst_bindom[n] = max(slice_r)

print(f"\n  α_worst by n (all): {alpha_worst_by_n}")
print(f"  α_worst by n (binary-dom): {alpha_worst_bindom}")

# Simple linear extrapolation to n=9
if len(ns) >= 2 and 9 not in ns:
    # use last two points
    n1, n2 = ns[-2], ns[-1]
    a1, a2 = alpha_worst_by_n[n1], alpha_worst_by_n[n2]
    slope = (a2 - a1) / (n2 - n1)
    proj_9 = a2 + slope * (9 - n2)
    print(f"\n  Linear extrapolation to n=9: α ≈ {proj_9:.3f}")
    print(f"    (slope {slope:+.4f} per n from n={n1}→{n2}: {a1:.3f}→{a2:.3f})")
    if alpha_worst_bindom:
        n1b, n2b = sorted(alpha_worst_bindom.keys())[-2:] if len(alpha_worst_bindom) >= 2 else (None, None)
        if n1b is not None:
            a1b, a2b = alpha_worst_bindom[n1b], alpha_worst_bindom[n2b]
            slope_b = (a2b - a1b) / (n2b - n1b) if n2b != n1b else 0.0
            proj_9b = a2b + slope_b * (9 - n2b)
            print(f"  Linear extrapolation to n=9 (binary-dom): α ≈ {proj_9b:.3f}")

elif 9 in ns:
    print(f"\n  n=9 observed: α_worst = {alpha_worst_by_n[9]:.3f}")
else:
    proj_9 = max(alpha_worst_by_n.values())
    print(f"\n  Single n; using max α across records: {proj_9:.3f}")

# Ansatz closure thresholds
print(f"\n  Closure thresholds at n=9, ε=0.03:")
print(f"    α < 0.637 → Σμ term positive")
print(f"    α ≤ 0.50  → 13% cushion (Keston's closure condition)")
print(f"    α > 0.70  → R4 declared failed")

# Verdict
print("\n" + "=" * 72)
print("Verdict")
print("=" * 72)

if abort:
    print("  T1' fires → option (ii) ABORT. R4 dead. Stop at sorry count 4.")
else:
    # compute best projected α
    if 9 in ns:
        proj = alpha_worst_bindom.get(9, alpha_worst_by_n[9])
    else:
        proj = proj_9b if 'proj_9b' in dir() else proj_9 if 'proj_9' in dir() else max(alpha_worst_by_n.values())
    print(f"\n  Best-case projected α at n=9 binary-dom: {proj:.3f}")
    if proj <= 0.50:
        print(f"  GREEN: α ≤ 0.5 — analytical derivation of T ≤ α·L·Σμ is worth a session.")
    elif proj <= 0.70:
        print(f"  YELLOW: α in (0.5, 0.7] — marginal. Analytical tightening may be needed.")
    else:
        print(f"  *** RED: α > 0.7 → declare R4 FAILED per Keston's tripwire. ***")

# Output
out = {
    'T1_prime_max_spread': max_spread,
    'T1_prime_fires': abort,
    'alpha_worst_by_n': alpha_worst_by_n,
    'alpha_worst_bindom_by_n': alpha_worst_bindom,
}
out_path = os.path.join(
    os.path.dirname(DATA_PATH), 'r4_T_upper_bound_2026-04-19.json'
)
with open(out_path, 'w') as f:
    json.dump(out, f, indent=2)
print(f"\n  Wrote {out_path}")
