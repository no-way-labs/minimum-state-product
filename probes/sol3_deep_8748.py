#!/usr/bin/env python3
"""sol3_deep_8748.py — Deep search for witnesses at product 8748.

v1 adaptation works at 13122 = {2,3^8} but fails at 8748 = {2^2,3^7}.
The issue is 2 binary processors adjacent in the ring.

Strategy:
1. Try all rotations of {2,2,3,3,3,3,3,3,3} (where binary procs are at different separations)
2. Try many more adaptation variants
3. Try Z3 parameterized search
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))

from itertools import product as cartesian, permutations
from verifier import verify_system


def sol3_adapt_v1(ms, n):
    """v1: replace K with m_i in mod operations."""
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


def sol3_adapt_v7(ms, n):
    """v7: hybrid — bottom/top use K=3 logic with clamping,
    middle procs use per-processor modulus.
    Binary procs: if they're middle, use Sol3-like with m_i=2.
    If they're bottom/top, use binary-specific rules.
    """
    def make_bottom(m0, m_right):
        if m0 == 2:
            def f(L, S, R):
                # Binary bottom: privileged if S+1 mod 2 == R mod 2
                if (S + 1) % 2 == R % 2:
                    return (S + 1) % 2  # toggle
                return S
            return f
        else:
            def f(L, S, R):
                if (S + 1) % 3 == R % 3:
                    return (S - 1) % 3
                return S
            return f

    def make_top(m_top, m_left, m_right):
        if m_top == 2:
            def f(L, S, R):
                if L % 2 == R % 2 and (L % 2 + 1) % 2 != S:
                    return (L % 2 + 1) % 2
                return S
            return f
        else:
            def f(L, S, R):
                if L % 3 == R % 3 and (L % 3 + 1) % 3 != S:
                    return (L % 3 + 1) % 3
                return S
            return f

    def make_middle(m_i, m_left, m_right):
        if m_i == 2:
            def f(L, S, R):
                if (S + 1) % 2 == L % 2:
                    return L % 2
                if (S + 1) % 2 == R % 2:
                    return R % 2
                return S
            return f
        else:
            def f(L, S, R):
                if (S + 1) % 3 == L % 3:
                    return L % 3
                if (S + 1) % 3 == R % 3:
                    return R % 3
                return S
            return f

    fs = [make_bottom(ms[0], ms[1])]
    for i in range(1, n - 1):
        fs.append(make_middle(ms[i], ms[i-1], ms[i+1]))
    fs.append(make_top(ms[n-1], ms[n-2], ms[0]))
    return fs


def sol3_adapt_v8(ms, n):
    """v8: bottom does (S-1)%m0 when triggered, but trigger uses direct comparison.
    Middle uses direct copy-neighbor, not modular comparison.
    """
    def make_bottom(m0):
        def f(L, S, R):
            # Privileged: S is "just before" R in mod-m0 cycle
            if (S + 1) % m0 == R % m0:
                return (S - 1) % m0
            return S
        return f

    def make_top(m_top):
        def f(L, S, R):
            # Privileged: L and R are the same (mod m_top), and S isn't "next"
            l_mod = L % m_top
            r_mod = R % m_top
            if l_mod == r_mod and S != (l_mod + 1) % m_top:
                return (l_mod + 1) % m_top
            return S
        return f

    def make_middle(m_i):
        def f(L, S, R):
            # Privileged: S is "next after" L (copy L) or "next after" R (copy R)
            l_mod = L % m_i
            r_mod = R % m_i
            if S == (l_mod + 1) % m_i:
                return l_mod
            if S == (r_mod + 1) % m_i:
                return r_mod
            return S
        return f

    fs = [make_bottom(ms[0])]
    for i in range(1, n - 1):
        fs.append(make_middle(ms[i]))
    fs.append(make_top(ms[n - 1]))
    return fs


def sol3_swap_bt(ms, n):
    """Try swapping bottom and top assignments.
    Maybe making the binary processor the top (or bottom) helps.
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


def main():
    n = 9
    print("=" * 70)
    print("DEEP SEARCH AT PRODUCT 8748")
    print("=" * 70)

    # Generate all distinct rotations of (2,2,3,3,3,3,3,3,3)
    ms_base = (2, 2, 3, 3, 3, 3, 3, 3, 3)
    rotations = set()
    for rot in range(n):
        ms = tuple(ms_base[(i + rot) % n] for i in range(n))
        rotations.add(ms)
    rotations = sorted(rotations)
    print(f"\n{len(rotations)} distinct rotations")

    adaptations = [
        ("v1", sol3_adapt_v1),
        ("v7", sol3_adapt_v7),
        ("v8", sol3_adapt_v8),
    ]

    found_any = False
    for ms in rotations:
        bin_pos = [i for i in range(n) if ms[i] == 2]
        sep = min((bin_pos[1] - bin_pos[0]) % n, (bin_pos[0] - bin_pos[1]) % n)

        for name, adapt_fn in adaptations:
            fs = adapt_fn(list(ms), n)
            result = verify_system(list(ms), fs)
            if result.get('valid', False):
                print(f"\n  *** VALID: {name} at {ms}, sep={sep} ***")
                print(f"  Cycle length: {result.get('cycle_length')}")
                print(f"  Good configs: {len(result.get('good_configs', set()))}")
                found_any = True

    if not found_any:
        print("\n  No direct adaptations work at product 8748.")

    # Now try: what if we also try non-{2,2,3^7} multisets at product 8748?
    # {4, 3^8} has product 4*6561 = 26244 -- too high
    # Actually {4, 3^7} has 8 entries, not 9. We need 9 entries.
    # {4, 3, 3, 3, 3, 3, 3, 3, 3} = 4 * 3^8 = 26244, not 8748.
    # 8748 = 4 * 3^7 = 2^2 * 3^7.
    # With 9 entries: need product = 8748 = 4 * 2187 = 4 * 3^7.
    # Options: {2, 2, 3, 3, 3, 3, 3, 3, 3} = 4 * 3^7 = 8748. ✓
    # {4, 3, 3, 3, 3, 3, 3, 3, ...} with 8 threes and one 4: 4 * 3^8 = 26244. ✗
    # So the only multiset at 8748 with all entries ≥ 2 is {2, 2, 3^7}.

    # Let's try Z3 parameterized search at 8748
    print("\n" + "=" * 70)
    print("Z3 PARAMETERIZED SEARCH AT 8748")
    print("=" * 70)
    print("(See sol3_z3_search.py)")

    # Also: confirm and extract the 13122 witness
    print("\n" + "=" * 70)
    print("EXTRACTING 13122 WITNESS")
    print("=" * 70)
    ms_13122 = [2, 3, 3, 3, 3, 3, 3, 3, 3]
    fs_13122 = sol3_adapt_v1(ms_13122, n)
    result = verify_system(ms_13122, fs_13122)
    if result.get('valid'):
        print(f"  CONFIRMED VALID at product 13122")
        print(f"  ms = {ms_13122}")
        print(f"  Cycle length: {result.get('cycle_length')}")
        print(f"  Good configs: {len(result.get('good_configs', set()))}")

        # Print the rule table
        print(f"\n  Rule table:")
        for i in range(n):
            m_L = ms_13122[(i-1) % n]
            m_S = ms_13122[i]
            m_R = ms_13122[(i+1) % n]
            n_entries = m_L * m_S * m_R
            n_forcing = 0
            for L in range(m_L):
                for S in range(m_S):
                    for R in range(m_R):
                        val = fs_13122[i](L, S, R)
                        if val != S:
                            n_forcing += 1
            ptype = "BIN" if m_S == 2 else "TER"
            role = "bottom" if i == 0 else ("top" if i == n-1 else "middle")
            print(f"    P{i} ({ptype}, {role}): {n_forcing}/{n_entries} forcing entries")

        # Print the cycle
        cycle = result.get('cycle', [])
        print(f"\n  Good cycle ({len(cycle)} steps):")
        for idx, c in enumerate(cycle[:30]):
            c_next = cycle[(idx + 1) % len(cycle)]
            diffs = [j for j in range(n) if c[j] != c_next[j]]
            mover = diffs[0] if diffs else "?"
            print(f"    {idx:2d}: {c} → P{mover}")
        if len(cycle) > 30:
            print(f"    ... ({len(cycle)} total)")


if __name__ == "__main__":
    main()
