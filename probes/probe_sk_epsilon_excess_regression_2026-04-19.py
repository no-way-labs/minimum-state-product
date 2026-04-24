#!/usr/bin/env python3
"""ε sub-session step 1+2: variance check + excess regression (2026-04-19).

Step 1: variance of `excess = |Ham-1 pairs in C| − L` at fixed (n, L, ms).
If spread > 2× at any multi-cycle key, shape 4d fires — cycle-shape-
dependent, abort.

Step 2: if variance clean, regress excess against:
  (4a) L · c/n
  (4b) c · Σ(m−1)
  (4c) c · bin_count + c' · ternary_count (joint)

Pick best fit by worst-case (max excess / predictor) ratio — the ansatz
needs the floor, not the mean.
"""

import json
import os
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
DATA_PATH = os.path.normpath(
    os.path.join(HERE, '..', 'lean', 'docs', 'sk', 'sk_phase0_out',
                 'r4_epsilon_separation_2026-04-19.json')
)

with open(DATA_PATH) as f:
    records = json.load(f)
print(f"Loaded {len(records)} records from {DATA_PATH}\n")

for r in records:
    r['excess'] = r['ham1_count'] - r['L']

# --- Step 1: variance at fixed (n, L, ms) ---
print("=" * 72)
print("Step 1: variance check at fixed (n, L, ms)")
print("=" * 72)

by_key = defaultdict(list)
for r in records:
    key = (r['n'], r['L'], tuple(r['ms']))
    by_key[key].append(r['excess'])

multi_keys = {k: xs for k, xs in by_key.items() if len(xs) >= 2}
print(f"  {len(multi_keys)} (n, L, ms) keys with ≥ 2 cycles")

max_spread = 0.0
worst_key = None
spreads = []
for key, xs in multi_keys.items():
    lo, hi = min(xs), max(xs)
    if lo > 0:
        r = hi / lo
    elif hi > 0:
        r = float('inf')
    else:
        r = 1.0
    spreads.append((r, key, xs))
    if r > max_spread:
        max_spread = r
        worst_key = key

spreads.sort(reverse=True)
print(f"\n  Top 5 spreads (max/min excess at fixed key):")
for r, key, xs in spreads[:5]:
    print(f"    spread={r:.2f}x at key={key}, excess values={sorted(set(xs))}")

print(f"\n  Max spread: {max_spread:.2f}x at {worst_key}")
if max_spread > 2.0:
    # Check if it's dominated by small-excess noise (excess 0 vs 1 etc.)
    close_but_small = [(r, k, xs) for r, k, xs in spreads
                       if r > 2.0 and max(xs) <= 3]
    if close_but_small and not any(r > 2.0 and max(xs) > 3
                                    for r, k, xs in spreads):
        print(f"  NOTE: all >2× spreads are at low absolute excess "
              f"(max excess ≤ 3). Absolute spread small.")
    else:
        print(f"  *** SHAPE 4d FIRES: excess varies > 2× at fixed (n, L, ms). ***")
        print(f"  Abort session: cycle-shape-dependent.")

# Also print absolute spread (max - min) per key — that's what matters
# for the ansatz, not ratio
abs_spreads = [(max(xs) - min(xs), key, xs) for key, xs in multi_keys.items()]
abs_spreads.sort(reverse=True)
print(f"\n  Top 5 ABSOLUTE excess ranges at fixed (n,L,ms):")
for d, key, xs in abs_spreads[:5]:
    print(f"    Δexcess={d}, key={key}, "
          f"excess values={sorted(set(xs))}")

# --- Step 2: regression ---
print("\n" + "=" * 72)
print("Step 2: regression of excess against candidate bounds")
print("=" * 72)

# For each candidate, compute the minimum c such that excess ≤ c · predictor
# holds across all records (i.e., c = max over records of excess/predictor).

def fit_min_c(get_predictor, records):
    """Return min c such that excess ≤ c · predictor(r) for all r."""
    ratios = []
    for r in records:
        p = get_predictor(r)
        if p <= 0:
            continue
        if r['excess'] > 0:
            ratios.append((r['excess'] / p, r))
        else:
            ratios.append((0.0, r))
    if not ratios:
        return None, None
    max_ratio, worst_r = max(ratios, key=lambda x: x[0])
    mean_ratio = sum(x[0] for x in ratios) / len(ratios)
    return {
        'c_worst': max_ratio,
        'c_mean': mean_ratio,
        'worst_record': {
            'n': worst_r['n'], 'ms': worst_r['ms'],
            'L': worst_r['L'], 'excess': worst_r['excess'],
        },
    }, ratios

# 4a: excess ≤ c · L / n
fit_4a, _ = fit_min_c(lambda r: r['L'] / r['n'], records)
print(f"\n  4a: excess ≤ c · L/n")
print(f"    c_worst (tight analytical target) = {fit_4a['c_worst']:.3f}")
print(f"    c_mean                            = {fit_4a['c_mean']:.3f}")
print(f"    Worst record: n={fit_4a['worst_record']['n']} "
      f"ms={fit_4a['worst_record']['ms']} "
      f"L={fit_4a['worst_record']['L']} "
      f"excess={fit_4a['worst_record']['excess']}")

# 4b: excess ≤ c · Σ(m-1)
fit_4b, _ = fit_min_c(
    lambda r: sum(m - 1 for m in r['ms']), records
)
print(f"\n  4b: excess ≤ c · Σ(m-1)")
print(f"    c_worst = {fit_4b['c_worst']:.3f}")
print(f"    c_mean  = {fit_4b['c_mean']:.3f}")

# 4c: excess ≤ c · bin_count + c' · ternary_count
# joint fit — minimize worst-case ratio with some structure.
# Simplest: compute c1 such that excess ≤ c1 · bin_count + c2 · ternary_count
# We'll just try a grid for (c1, c2).
def bin_count(r): return sum(1 for m in r['ms'] if m == 2)
def tern_count(r): return sum(1 for m in r['ms'] if m == 3)

def c4c_worst(c1, c2):
    max_diff = 0
    for r in records:
        bound = c1 * bin_count(r) + c2 * tern_count(r)
        if bound > 0:
            max_diff = max(max_diff, r['excess'] / bound)
    return max_diff

# Find the min over a grid where both terms could be useful
best_c1c2 = (None, None, float('inf'))
for c1 in [0, 0.5, 1, 1.5, 2, 3, 4]:
    for c2 in [0, 0.5, 1, 2, 3]:
        if c1 == 0 and c2 == 0:
            continue
        # for each record, need c1*bin + c2*tern ≥ excess
        # find max over records of excess - (c1*bin + c2*tern); want it ≤ 0
        max_excess_overshoot = max(
            r['excess'] - (c1 * bin_count(r) + c2 * tern_count(r))
            for r in records
        )
        if max_excess_overshoot < best_c1c2[2]:
            best_c1c2 = (c1, c2, max_excess_overshoot)
print(f"\n  4c: excess ≤ c1 · bin + c2 · tern (grid search)")
print(f"    best (c1, c2) = ({best_c1c2[0]}, {best_c1c2[1]}), "
      f"worst-case overshoot = {best_c1c2[2]}")

# Also try excess vs L alone and vs L·Σμ
fit_L, _ = fit_min_c(lambda r: r['L'], records)
print(f"\n  Reference: excess ≤ c · L")
print(f"    c_worst = {fit_L['c_worst']:.4f}, c_mean = {fit_L['c_mean']:.4f}")

# Per-n worst-case c for 4a to see if it stabilizes
print(f"\n  4a per-n: worst-case c = excess · n / L")
by_n = defaultdict(list)
for r in records:
    by_n[r['n']].append(r['excess'] * r['n'] / r['L'])
for n in sorted(by_n):
    xs = by_n[n]
    print(f"    n={n}: max c = {max(xs):.2f}, mean c = {sum(xs)/len(xs):.2f}, "
          f"records = {len(xs)}")

# --- Ansatz closure with pinned ε ---
print("\n" + "=" * 72)
print("Step 3: does the pinned ε close E − T + sinks ≥ 1?")
print("=" * 72)

# Using 4a: excess ≤ c · L/n, so collision_pairs ≤ excess · (n-3)/n per ...
# Actually let's plug in more carefully.
# ε = (Case-A collision pairs) / (L · Σμ · (n-3)/n)
# where Case-A collision pairs ≤ excess · (n-3)/n (each non-adjacent Ham-1
# pair can contribute to multiple (k, q) but q-direction is bounded by (n-3))
# Actually each non-adj Ham-1 pair (c_i, c_j) where they differ at coord q:
#   contributes 1 (k, q) collision pair for k=i if q ∉ N[p_i]
#   contributes 1 (k, q) collision pair for k=j if q ∉ N[p_j]
# So each Ham-1 pair contributes AT MOST 2 collision pairs.
# |collision_pairs| ≤ 2 · |non-adj Ham-1| ≤ 2 · excess.

c_4a = fit_4a['c_worst']
print(f"\n  Using 4a: excess ≤ {c_4a:.2f} · L/n  ⇒  "
      f"|collision| ≤ {2*c_4a:.2f}·L/n")
print(f"  ε ≤ 2·excess / (L·Σμ·(n-3)/n) ≤ 2·({c_4a:.2f}·L/n) / (L·Σμ·(n-3)/n)")
print(f"     = 2·{c_4a:.2f} / (n·Σμ·(n-3)/n) = {2*c_4a:.2f}·n / (n·Σμ·(n-3))")
print(f"     = {2*c_4a:.2f} / (Σμ · (n-3))")
print()

# Test ansatz closure per record: E ≥ L(n-3)/n·Σμ·(1 - ε) + λ·cross_cand
# with ε = 2·c_4a / (Σμ·(n-3)), λ = 0.83/(n-2.5)
# Actually we don't have cross_cand/shadow/etc. in THESE records — they were
# stored in a different JSON. Skip ansatz eval for now; report pinned c.

# Write pinned constants
out = {
    'step1_max_spread': max_spread,
    'step1_worst_key': list(worst_key) if worst_key else None,
    'step2': {
        '4a': {'c_worst': fit_4a['c_worst'], 'c_mean': fit_4a['c_mean']},
        '4b': {'c_worst': fit_4b['c_worst'], 'c_mean': fit_4b['c_mean']},
        '4c_best': {'c1': best_c1c2[0], 'c2': best_c1c2[1],
                    'overshoot': best_c1c2[2]},
    },
    'epsilon_pinned_c': c_4a,
}
out_path = os.path.join(
    os.path.dirname(DATA_PATH), 'r4_epsilon_excess_regression_2026-04-19.json'
)
with open(out_path, 'w') as f:
    json.dump(out, f, indent=2)
print(f"\n  Wrote {out_path}")
