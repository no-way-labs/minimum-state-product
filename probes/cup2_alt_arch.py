#!/usr/bin/env python3
"""Test alternative architectures achieving product 4·3^(n-2).

Instead of ms=(2,3,...,3,2) with binary at both endpoints,
try other placements of two binary processors.
All use Sol 3 v1 rules.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import verify_system


def sol3_v1_rules(ms, n):
    """Standard Sol 3 v1: bottom(P0), middle(P1..P_{n-2}), top(P_{n-1})."""
    def make_bottom(m0):
        def f(L, S, R):
            if (S + 1) % m0 == R % m0:
                return (S - 1) % m0
            return S
        return f

    def make_top(m_top):
        def f(L, S, R):
            if L % m_top == R % m_top and (L % m_top + 1) % m_top != S:
                return (L % m_top + 1) % m_top
            return S
        return f

    def make_middle(m_i):
        def f(L, S, R):
            if (S + 1) % m_i == L % m_i:
                return L % m_i
            if (S + 1) % m_i == R % m_i:
                return R % m_i
            return S
        return f

    fs = [make_bottom(ms[0])]
    for i in range(1, n - 1):
        fs.append(make_middle(ms[i]))
    fs.append(make_top(ms[n - 1]))
    return fs


def test_arch(n, ms, label):
    """Test a specific architecture."""
    prod = 1
    for m in ms:
        prod *= m
    fs = sol3_v1_rules(ms, n)
    result = verify_system(ms, fs)
    status = "VALID" if result['valid'] else "INVALID"
    props = result.get('properties', {})
    detail = "; ".join(f"{k}: {v[1]}" for k, v in props.items() if v[1])
    extra = ""
    if result['valid']:
        extra = f" good={len(result.get('good_configs', set()))}, cycle_len={result.get('cycle_length', '?')}"
    print(f"  {label}: ms={tuple(ms)}, prod={prod}: {status} [{detail}]{extra}")
    return result


def main():
    print("Testing alternative architectures with product 4·3^(n-2)")
    print("=" * 80)

    for nv in [5, 7, 9]:
        print(f"\nn={nv}:")

        # Architecture 1: binary at positions 0 and n-1 (endpoints)
        ms1 = [2] + [3] * (nv - 2) + [2]
        test_arch(nv, ms1, "binary at 0,n-1")

        # Architecture 2: binary at positions 0 and 1 (adjacent at bottom)
        ms2 = [2, 2] + [3] * (nv - 2)
        test_arch(nv, ms2, "binary at 0,1")

        # Architecture 3: binary at n-2 and n-1 (adjacent at top)
        ms3 = [3] * (nv - 2) + [2, 2]
        test_arch(nv, ms3, "binary at n-2,n-1")

        # Architecture 4: binary at 0 and 2 (non-adjacent)
        ms4 = [2, 3, 2] + [3] * (nv - 3)
        test_arch(nv, ms4, "binary at 0,2")

        # Architecture 5: binary at 1 and n-1
        ms5 = [3, 2] + [3] * (nv - 3) + [2]
        test_arch(nv, ms5, "binary at 1,n-1")

        # Also test with just one extra binary (product 2·2·3^(n-2) = 4·3^(n-2)):
        # Actually ms=(2,2,3,...,3) has n-2 ternary and 2 binary → product = 4·3^(n-2) ✓

    # Bonus: test ms=(2,2,3,...,3) with Sol 3 v1 for a range of n
    print("\n\nSol 3 v1 on ms=(2,2,3,...,3) for n=3..12:")
    print("-" * 60)
    for nv in range(3, 13):
        ms = [2, 2] + [3] * (nv - 2)
        prod = 4 * 3 ** (nv - 2)
        if prod > 500000:
            print(f"  n={nv}: SKIP (prod={prod})")
            continue
        test_arch(nv, ms, f"n={nv}")


if __name__ == "__main__":
    main()
