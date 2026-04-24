#!/usr/bin/env python3
"""Session-2 pre-commit checks (2026-04-19).

Three checks before writing the ansatz:

  (1) Landing-ratio trend fit. Is λ ∝ 1/n, 1/(n−k), geometric, or else?
      Pick best fit on mean λ at n=5..8; also check per-record min.

  (2) ε collision-correction settle. Does the ansatz close with trivial
      ε ≤ 1/Σμ, or does it require empirical 0.03?
      For each record, compute:
          margin_bound_trivial = L·(n−3)/n·Σμ − L + λ·cross_cand − T + sinks
          margin_bound_tight   = L·(n−3)/n·Σμ − 0.03·L·Σμ + λ·cross_cand − T + sinks
      Check whether trivial bound ≥ 1 uniformly.

  (3) cross_cand floor shape. Compute cross_cand / L per record; fit to:
       (a) constant
       (b) f(n, ms) explicit (e.g. Σ(m−1))
       (c) cycle-shape-dependent (variance at fixed (n, L, ms) > 2×)
      If (c), T1 regression — report back.

Also report cross_cand absolute floor and landing ratio floor.
"""

import importlib.util
import json
import math
import os
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))

DATA_PATH = os.path.normpath(
    os.path.join(HERE, '..', 'lean', 'docs', 'sk', 'sk_phase0_out',
                 'r4_read2_session2_gates_2026-04-19.json')
)

with open(DATA_PATH) as f:
    records = json.load(f)
print(f"Loaded {len(records)} records from {DATA_PATH}\n")

# ---- Check 1: landing-ratio trend fit ----
by_n = defaultdict(list)
for r in records:
    if r.get('landing_ratio') is not None:
        by_n[r['n']].append(r['landing_ratio'])

mean_lr = {n: sum(xs) / len(xs) for n, xs in by_n.items()}
min_lr = {n: min(xs) for n, xs in by_n.items()}

print("Check 1: Landing-ratio trend")
print(f"  n | mean λ | min λ")
for n in sorted(mean_lr):
    print(f"  {n} | {mean_lr[n]:.4f} | {min_lr[n]:.4f}")

# Fit forms: c/n, c/(n-k) for k in {1, 2, 2.5, 3}, geometric
ns = sorted(mean_lr)
ys = [mean_lr[n] for n in ns]

def sse(pred, actual):
    return sum((p - a) ** 2 for p, a in zip(pred, actual))

# c/n fit: c = mean of n*y
c_overn = sum(n * y for n, y in zip(ns, ys)) / len(ns)
pred_overn = [c_overn / n for n in ns]

fits = {'c/n (c=%.3f)' % c_overn: (pred_overn, sse(pred_overn, ys))}

for k in [1, 1.5, 2, 2.5, 3, 3.5]:
    c_k = sum((n - k) * y for n, y in zip(ns, ys)) / len(ns)
    pred_k = [c_k / (n - k) if (n - k) > 0 else float('inf') for n in ns]
    fits[f'c/(n-{k}) (c={c_k:.3f})'] = (pred_k, sse(pred_k, ys))

# Geometric: y_n = a * r^(n - n_0)
# Fit via log-linear: log y = log a + (n-n_0) log r
logy = [math.log(y) for y in ys]
# least-squares on (n, log y)
mean_n = sum(ns) / len(ns)
mean_ly = sum(logy) / len(logy)
num = sum((n - mean_n) * (ly - mean_ly) for n, ly in zip(ns, logy))
den = sum((n - mean_n) ** 2 for n in ns)
slope = num / den
intercept = mean_ly - slope * mean_n
pred_geo = [math.exp(intercept + slope * n) for n in ns]
fits[f'geometric (slope={slope:.3f}, r={math.exp(slope):.3f})'] = (
    pred_geo, sse(pred_geo, ys)
)

print("\n  Fit comparison (SSE across n=5..8 means):")
for label, (pred, err) in sorted(fits.items(), key=lambda x: x[1][1]):
    pred_str = ' '.join(f'{p:.3f}' for p in pred)
    print(f"    {label:30s} pred=[{pred_str}]  SSE={err:.5f}")

# Best fit summary
best = min(fits.items(), key=lambda x: x[1][1])
print(f"\n  Best fit: {best[0]} (SSE={best[1][1]:.5f})")

# Per-record min: what's the floor over all records?
print(f"\n  Per-record min landing ratios:")
for n in sorted(by_n):
    ratios = sorted(by_n[n])
    p0 = ratios[0]
    p10 = ratios[max(0, len(ratios) // 10)]
    print(f"    n={n}: p0={p0:.3f}, p10={p10:.3f}, "
          f"(n-2)·p0={(n-2)*p0:.2f}, n·p0={n*p0:.2f}")

# ---- Check 2: ε collision-correction settle ----
print("\nCheck 2: ε collision correction — trivial vs tight ansatz closure")

# For each record, evaluate:
#   bound_trivial = L·(n-3)/n·Σμ − L·(1/Σμ)·Σμ + λ·cross_cand + sinks − T
#                 = L·(n-3)/n·Σμ − L + λ·cross_cand + sinks − T
# But we need a λ that works uniformly. Use the empirical n-specific mean.
# For pre-commit, use fit c/(n-2) which was near-flat:
lambda_floor = {}  # per-n
for n in ns:
    # Use p0 over records as conservative per-n floor
    lambda_floor[n] = min_lr[n]

# Separately also report using fitted λ for comparison
fitted_lambda = {n: min(1.0, max(0.0, fits[best[0]][0][ns.index(n)]))
                 for n in ns}

def eval_record(r, lam_func, eps_func):
    n = r['n']; L = r['L']; sm = r['Sigma_mu']
    shadow_term = L * (n - 3) / n * sm - eps_func(r) * L * sm
    cross_term = lam_func(r) * r['cross_cand']
    rhs = r['T_size'] - r['sinks'] + 1  # need E - (T - sinks) ≥ 1
    lhs = shadow_term + cross_term
    return lhs - rhs, shadow_term, cross_term

def eps_trivial(r):
    return 1.0 / r['Sigma_mu'] if r['Sigma_mu'] > 0 else 0.0

def eps_tight(r):
    # empirical ε = 1 - shadow / (L·(n-3)/n·Σμ)
    return 0.03

def lam_p0(r):
    return lambda_floor[r['n']]

def lam_fitted(r):
    return fitted_lambda[r['n']]

print(f"\n  Using λ = per-n empirical min, ε = trivial (1/Σμ):")
cnt_pass = cnt_fail = 0
fail_examples = []
for r in records:
    delta, sh, cr = eval_record(r, lam_p0, eps_trivial)
    if delta >= 0:
        cnt_pass += 1
    else:
        cnt_fail += 1
        fail_examples.append((delta, r))
print(f"    pass: {cnt_pass}, fail: {cnt_fail}")
if fail_examples:
    fail_examples.sort(key=lambda x: x[0])
    print(f"    worst fail delta = {fail_examples[0][0]:.2f}")
    fail_by_n = defaultdict(int)
    for d, r in fail_examples:
        fail_by_n[r['n']] += 1
    print(f"    fails by n: {dict(fail_by_n)}")
    for d, r in fail_examples[:3]:
        print(f"      n={r['n']} ms={r['ms']} L={r['L']} T={r['T_size']} "
              f"E={r['E_size']} sinks={r['sinks']} Σμ={r['Sigma_mu']} "
              f"cross_cand={r['cross_cand']} delta={d:.2f}")

print(f"\n  Using λ = per-n empirical min, ε = tight (0.03):")
cnt_pass = cnt_fail = 0
for r in records:
    delta, sh, cr = eval_record(r, lam_p0, eps_tight)
    if delta >= 0: cnt_pass += 1
    else: cnt_fail += 1
print(f"    pass: {cnt_pass}, fail: {cnt_fail}")

# ---- Check 3: cross_cand floor shape ----
print("\nCheck 3: cross_cand floor shape")

# Compute cross_cand / L per record, then check if
#   (a) cross_cand / L ≥ const uniformly
#   (b) cross_cand / (L·f(n, ms)) ≥ const where f is explicit
#   (c) varies by cycle at fixed (n, L, ms)
print(f"  cross_cand/L by n:")
for n in sorted(by_n):
    rs = [r for r in records if r['n'] == n]
    ratios = [r['cross_cand'] / r['L'] for r in rs]
    print(f"    n={n}: min={min(ratios):.2f}, mean={sum(ratios)/len(ratios):.2f}, "
          f"max={max(ratios):.2f}")

# Try cross_cand / (L·Σ(m-1))
print(f"\n  cross_cand/(L·Σ(m-1)) by n:")
for n in sorted(by_n):
    rs = [r for r in records if r['n'] == n]
    xs = [r['cross_cand'] / (r['L'] * sum(m - 1 for m in r['ms'])) for r in rs]
    print(f"    n={n}: min={min(xs):.3f}, mean={sum(xs)/len(xs):.3f}, "
          f"max={max(xs):.3f}")

# Try cross_cand / (L·Σμ) (since Σμ ≤ Σ(m-1))
print(f"\n  cross_cand/(L·Σμ) by n:")
for n in sorted(by_n):
    rs = [r for r in records if r['n'] == n]
    xs = [r['cross_cand'] / (r['L'] * r['Sigma_mu']) for r in rs]
    print(f"    n={n}: min={min(xs):.3f}, mean={sum(xs)/len(xs):.3f}, "
          f"max={max(xs):.3f}")

# Variance at fixed (n, L, ms)
print(f"\n  Spread of cross_cand/L at fixed (n, L, ms):")
by_key = defaultdict(list)
for r in records:
    key = (r['n'], r['L'], tuple(r['ms']))
    by_key[key].append(r['cross_cand'] / r['L'])
worst_spread = 0
worst_key = None
multi_keys = 0
for key, xs in by_key.items():
    if len(xs) >= 2:
        multi_keys += 1
        if min(xs) > 0:
            rr = max(xs) / min(xs)
            if rr > worst_spread:
                worst_spread = rr
                worst_key = key
print(f"    multi-cycle keys: {multi_keys}")
print(f"    max spread: {worst_spread:.2f}× (at {worst_key})")

if worst_spread > 2.0:
    print(f"\n  *** SHAPE (c): cross_cand varies > 2× at fixed (n,L,ms). ***")
    print(f"  T1 regression — cross_cand floor is cycle-structural.")
else:
    print(f"\n  cross_cand/L behaves as shape (a) or (b): bounded spread at fixed key.")
