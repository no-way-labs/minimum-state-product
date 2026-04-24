"""Test Sol 3 v1 for n=3..14 and look for patterns in cycle length and good config count."""

import os
import sys
import time

sys.path.insert(0, os.path.dirname(__file__))
from verifier import verify_system


def make_sol3v1_rules(state_counts):
    n = len(state_counts)

    def f_bottom(L, S, R):
        m = state_counts[0]
        if (S + 1) % m == R % m:
            return (S - 1) % m
        return S

    def f_top(L, S, R):
        m = state_counts[n - 1]
        if L % m == R % m and (L % m + 1) % m != S:
            return (L % m + 1) % m
        return S

    def make_f_middle(m):
        def f_middle(L, S, R):
            if (S + 1) % m == L % m:
                return L % m
            if (S + 1) % m == R % m:
                return R % m
            return S
        return f_middle

    fs = [f_bottom]
    for i in range(1, n - 1):
        fs.append(make_f_middle(state_counts[i]))
    fs.append(f_top)
    return fs


print(f"{'n':>3} {'product':>10} {'valid':>6} {'cycle_len':>10} {'good':>6} {'bad':>8} {'time':>8}")
print("-" * 60)

for n in range(3, 15):
    ms = tuple([2] + [3] * (n - 1))
    product = 2 * 3 ** (n - 1)

    # Skip n>=13 if product too large (>1M configs)
    if product > 2_000_000:
        print(f"{n:>3} {product:>10} {'skip':>6} {'':>10} {'':>6} {'':>8} {'too large':>8}")
        continue

    t0 = time.time()
    fs = make_sol3v1_rules(ms)
    result = verify_system(list(ms), fs)
    elapsed = time.time() - t0

    if result['valid']:
        cl = result['cycle_length']
        good = len(result['good_configs'])
        bad = product - good
        print(f"{n:>3} {product:>10} {'PASS':>6} {cl:>10} {good:>6} {bad:>8} {elapsed:>7.1f}s")
    else:
        print(f"{n:>3} {product:>10} {'FAIL':>6} {'':>10} {'':>6} {'':>8} {elapsed:>7.1f}s")
        print(f"    Properties: {result['properties']}")

# Also test the standard Dijkstra Sol 3 (all 3-state) for comparison
print(f"\n{'='*60}")
print("Comparison: Standard Dijkstra Sol 3 (all 3-state)")
print(f"{'='*60}")
print(f"{'n':>3} {'product':>10} {'valid':>6} {'cycle_len':>10} {'good':>6} {'bad':>8} {'time':>8}")
print("-" * 60)

for n in range(3, 12):
    ms = tuple([3] * n)
    product = 3 ** n
    if product > 2_000_000:
        print(f"{n:>3} {product:>10} {'skip':>6}")
        continue

    t0 = time.time()
    fs = make_sol3v1_rules(ms)  # With all m=3, this is standard Sol 3
    result = verify_system(list(ms), fs)
    elapsed = time.time() - t0

    if result['valid']:
        cl = result['cycle_length']
        good = len(result['good_configs'])
        bad = product - good
        print(f"{n:>3} {product:>10} {'PASS':>6} {cl:>10} {good:>6} {bad:>8} {elapsed:>7.1f}s")
    else:
        print(f"{n:>3} {product:>10} {'FAIL':>6} {'':>10} {'':>6} {'':>8} {elapsed:>7.1f}s")
