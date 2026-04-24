#!/usr/bin/env python3
"""sol3_adapt.py — Adapt Dijkstra Sol 3 to lower products and verify.

Step 1: Try direct adaptations of Sol 3's f_bottom/f_middle/f_top rules
to mixed state counts. The key challenge is cross-range comparisons
when neighbors have different state counts.

Step 2: If direct adaptation fails, use Z3 to search for valid systems
that follow Sol 3's structural pattern (same rule for all middle procs).
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))

from itertools import product as cartesian
from verifier import verify_system


def sol3_original(n, K=3):
    """Original Sol 3 rules for all-K system."""
    def f_bottom(L, S, R):
        if (S + 1) % K == R:
            return (S - 1) % K
        return S

    def f_top(L, S, R):
        if L == R and (L + 1) % K != S:
            return (L + 1) % K
        return S

    def f_middle(L, S, R):
        if (S + 1) % K == L:
            return L
        if (S + 1) % K == R:
            return R
        return S

    return [f_bottom] + [f_middle] * (n - 2) + [f_top]


def sol3_adapt_v1(ms, n):
    """Adaptation v1: replace K with m_i in mod operations.

    For each processor i, use m_i as the modulus.
    Cross-range comparisons: compare raw values (L, R might exceed m_i-1).
    """
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
            new_L = L % m_i
            new_R = R % m_i
            if (S + 1) % m_i == new_L:
                return new_L
            if (S + 1) % m_i == new_R:
                return new_R
            return S
        return f

    fs = [make_bottom(ms[0])]
    for i in range(1, n - 1):
        fs.append(make_middle(ms[i]))
    fs.append(make_top(ms[n - 1]))
    return fs


def sol3_adapt_v2(ms, n):
    """Adaptation v2: use min(m_i, m_neighbor) for comparisons.

    Keep comparisons in the shared range.
    """
    def make_bottom(m0, m1):
        K = min(m0, m1)
        def f(L, S, R):
            if (S + 1) % K == R % K:
                return (S - 1) % m0
            return S
        return f

    def make_top(m_top, m_prev, m_next):
        K = min(m_top, m_prev, m_next)
        def f(L, S, R):
            if L % K == R % K and (L % K + 1) % K != S % K:
                return (L % K + 1) % m_top
            return S
        return f

    def make_middle(m_i, m_prev, m_next):
        K_L = min(m_i, m_prev)
        K_R = min(m_i, m_next)
        def f(L, S, R):
            if (S + 1) % K_L == L % K_L:
                return L % m_i
            if (S + 1) % K_R == R % K_R:
                return R % m_i
            return S
        return f

    fs = [make_bottom(ms[0], ms[1])]
    for i in range(1, n - 1):
        fs.append(make_middle(ms[i], ms[i - 1], ms[i + 1]))
    fs.append(make_top(ms[n - 1], ms[n - 2], ms[0]))
    return fs


def sol3_adapt_v3(ms, n):
    """Adaptation v3: keep K=3 for all comparisons, but cap output at m_i.

    The idea: Sol 3's logic is defined in mod-3 space.
    If m_i=2, the output (S-1)%3 might produce 2 which is invalid.
    Cap: if result >= m_i, keep S unchanged.
    """
    K = 3

    def make_bottom(m0):
        def f(L, S, R):
            if (S + 1) % K == R % K:
                result = (S - 1) % K
                if result < m0:
                    return result
            return S
        return f

    def make_top(m_top):
        def f(L, S, R):
            if L % K == R % K and (L % K + 1) % K != S % K:
                result = (L % K + 1) % K
                if result < m_top:
                    return result
            return S
        return f

    def make_middle(m_i):
        def f(L, S, R):
            if (S + 1) % K == L % K:
                result = L % K
                if result < m_i:
                    return result
            if (S + 1) % K == R % K:
                result = R % K
                if result < m_i:
                    return result
            return S
        return f

    fs = [make_bottom(ms[0])]
    for i in range(1, n - 1):
        fs.append(make_middle(ms[i]))
    fs.append(make_top(ms[n - 1]))
    return fs


def sol3_adapt_v4(ms, n):
    """Adaptation v4: binary processors use toggle (S+1)%2,
    ternary processors use Sol 3 rules with K=3.
    Cross-comparisons: binary proc compares S with R%2.
    """
    K = 3

    def make_bottom(m0, m1):
        def f(L, S, R):
            if m0 == 2:
                # Binary bottom: toggle if R's parity matches trigger
                if S != R % 2:
                    return 1 - S
                return S
            else:
                if (S + 1) % 3 == R % 3:
                    return (S - 1) % 3
                return S
        return f

    def make_top(m_top, m_prev, m0):
        def f(L, S, R):
            if m_top == 2:
                if L % 2 == R % 2 and L % 2 != S:
                    return L % 2
                return S
            else:
                if L % 3 == R % 3 and (L % 3 + 1) % 3 != S:
                    return (L % 3 + 1) % 3
                return S
        return f

    def make_middle(m_i, m_prev, m_next):
        def f(L, S, R):
            if m_i == 2:
                # Binary middle: copy left if different, else copy right if different
                if S != L % 2:
                    return L % 2
                if S != R % 2:
                    return R % 2
                return S
            else:
                if (S + 1) % 3 == L % 3:
                    return L % 3
                if (S + 1) % 3 == R % 3:
                    return R % 3
                return S
        return f

    fs = [make_bottom(ms[0], ms[1])]
    for i in range(1, n - 1):
        fs.append(make_middle(ms[i], ms[i - 1], ms[i + 1]))
    fs.append(make_top(ms[n - 1], ms[n - 2], ms[0]))
    return fs


def sol3_adapt_v5(ms, n):
    """Adaptation v5: All processors use Sol 1 style (copy left) for non-bottom.
    Bottom: privileged if s_0 != (s_{n-1}+1) % m_0, move: s_0 := (s_{n-1}+1) % m_0.
    Others: privileged if s_i != s_{i-1} % m_i, move: s_i := s_{i-1} % m_i.
    """
    def make_bottom(m0):
        def f(L, S, R):
            target = (L + 1) % m0
            if S != target:
                return target
            return S
        return f

    def make_other(m_i):
        def f(L, S, R):
            target = L % m_i
            if S != target:
                return target
            return S
        return f

    fs = [make_bottom(ms[0])]
    for i in range(1, n):
        fs.append(make_other(ms[i]))
    return fs


def sol3_adapt_v6(ms, n):
    """Adaptation v6: Dijkstra Sol 1 with K = max(ms).
    Distinguished proc: if s_0 == s_{n-1}, move: s_0 := (s_0+1) % m_0.
    Others: if s_i != s_{i-1}, move: s_i := s_{i-1} (if s_{i-1} < m_i, else s_i := s_{i-1} % m_i).
    """
    def make_distinguished(m0):
        def f(L, S, R):
            if L % m0 == S:
                return (S + 1) % m0
            return S
        return f

    def make_other(m_i):
        def f(L, S, R):
            target = L % m_i
            if S != target:
                return target
            return S
        return f

    fs = [make_distinguished(ms[0])]
    for i in range(1, n):
        fs.append(make_other(ms[i]))
    return fs


def test_all_rotations(ms_base, n, adapt_fn, name):
    """Test adaptation at all rotations of a multiset."""
    results = []
    tested = set()
    for rot in range(n):
        ms = tuple(ms_base[(i + rot) % n] for i in range(n))
        if ms in tested:
            continue
        tested.add(ms)

        fs = adapt_fn(list(ms), n)
        result = verify_system(list(ms), fs)
        valid = result.get('valid', False)
        results.append((ms, valid, result))

        if valid:
            cycle_len = result.get('cycle_length', '?')
            n_good = len(result.get('good_configs', set()))
            print(f"    {ms}: VALID! cycle={cycle_len}, good={n_good}")
            return results  # Found one!

    return results


def main():
    n = 9
    print("=" * 70)
    print("DIJKSTRA SOL 3 ADAPTATION TO LOWER PRODUCTS")
    print("=" * 70)

    # Reference: verify original Sol 3 at (3^9)
    print("\n--- Reference: Sol 3 at (3^9) = 19683 ---")
    ms_ref = [3] * n
    fs_ref = sol3_original(n, K=3)
    ref_result = verify_system(ms_ref, fs_ref)
    print(f"  Valid: {ref_result.get('valid')}")
    if ref_result.get('valid'):
        print(f"  Cycle length: {ref_result.get('cycle_length')}")
        print(f"  Good configs: {len(ref_result.get('good_configs', set()))}")

    # Test multisets
    test_ms = [
        ((2, 3, 3, 3, 3, 3, 3, 3, 3), 13122),
        ((2, 2, 3, 3, 3, 3, 3, 3, 3), 8748),
        ((2, 2, 2, 3, 3, 3, 3, 3, 3), 5832),
        ((2, 2, 2, 2, 3, 3, 3, 3, 3), 3888),
        ((2, 2, 2, 2, 2, 3, 3, 3, 3), 2592),
    ]

    adaptations = [
        ("v1: m_i mod", sol3_adapt_v1),
        ("v2: min(m_i, m_j) mod", sol3_adapt_v2),
        ("v3: K=3 cap", sol3_adapt_v3),
        ("v4: binary toggle + ternary Sol3", sol3_adapt_v4),
        ("v5: Sol 1 copy-left", sol3_adapt_v5),
        ("v6: Sol 1 distinguished", sol3_adapt_v6),
    ]

    for ms_base, product in test_ms:
        print(f"\n{'=' * 60}")
        print(f"ms={ms_base}, product={product}")
        print(f"{'=' * 60}")

        for name, adapt_fn in adaptations:
            print(f"\n  {name}:")

            # Test base orientation
            fs = adapt_fn(list(ms_base), n)
            result = verify_system(list(ms_base), fs)
            valid = result.get('valid', False)

            if valid:
                cycle_len = result.get('cycle_length', '?')
                n_good = len(result.get('good_configs', set()))
                print(f"    {ms_base}: VALID! cycle={cycle_len}, good={n_good}")
                print(f"    *** WITNESS FOUND AT PRODUCT {product}! ***")
                props = result.get('properties', {})
                for k, v in props.items():
                    print(f"      {k}: {v}")
                continue

            # Try all rotations
            found = False
            tested = {ms_base}
            for rot in range(1, n):
                ms_rot = tuple(ms_base[(i + rot) % n] for i in range(n))
                if ms_rot in tested:
                    continue
                tested.add(ms_rot)
                fs = adapt_fn(list(ms_rot), n)
                result = verify_system(list(ms_rot), fs)
                if result.get('valid', False):
                    cycle_len = result.get('cycle_length', '?')
                    n_good = len(result.get('good_configs', set()))
                    print(f"    {ms_rot}: VALID! cycle={cycle_len}, good={n_good}")
                    print(f"    *** WITNESS FOUND AT PRODUCT {product}! ***")
                    found = True
                    break

            if not found:
                # Show why it failed for the base orientation
                props = result.get('properties', {})
                fail_reason = next((f"{k}: {v}" for k, v in props.items()
                                   if isinstance(v, tuple) and not v[0]), "unknown")
                print(f"    FAILED ({fail_reason})")


if __name__ == "__main__":
    main()
