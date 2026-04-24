#!/usr/bin/env python3
"""sol3_separated_test.py — Test Sol 3 v1 on necklaces with SEPARATED binary procs.

The key insight: the 13122 witness works because there's no binary-binary edge.
At 8748, if the 2 binary procs are separated by ternary procs, ALL edges involve
at least one ternary proc — potentially enabling Sol 3 adaptation.

Necklaces of {2^2, 3^7} with n=9:
  sep=1: (2,2,3,3,3,3,3,3,3) — binary adjacent
  sep=2: (2,3,2,3,3,3,3,3,3) — 1 ternary between
  sep=3: (2,3,3,2,3,3,3,3,3) — 2 ternary between
  sep=4: (2,3,3,3,2,3,3,3,3) — 3 ternary between (max separation)
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))

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


def main():
    n = 9
    print("=" * 70)
    print("SEPARATED BINARY NECKLACE TEST AT PRODUCT 8748")
    print("=" * 70)

    # All necklaces of {2^2, 3^7}
    necklaces = [
        (2, 2, 3, 3, 3, 3, 3, 3, 3),  # sep=1
        (2, 3, 2, 3, 3, 3, 3, 3, 3),  # sep=2
        (2, 3, 3, 2, 3, 3, 3, 3, 3),  # sep=3
        (2, 3, 3, 3, 2, 3, 3, 3, 3),  # sep=4 (max)
    ]

    for ms_base in necklaces:
        bin_pos = [i for i in range(n) if ms_base[i] == 2]
        sep = min((bin_pos[1] - bin_pos[0]) % n, (bin_pos[0] - bin_pos[1]) % n)

        print(f"\n{'─' * 60}")
        print(f"Necklace: {ms_base}, sep={sep}")
        print(f"Binary at: {bin_pos}")
        print(f"{'─' * 60}")

        # Test ALL rotations of this necklace
        tested = set()
        for rot in range(n):
            ms = tuple(ms_base[(i + rot) % n] for i in range(n))
            if ms in tested:
                continue
            tested.add(ms)

            fs = sol3_adapt_v1(list(ms), n)
            result = verify_system(list(ms), fs)
            valid = result.get('valid', False)

            bin_pos_rot = [i for i in range(n) if ms[i] == 2]
            if valid:
                cycle_len = result.get('cycle_length', '?')
                n_good = len(result.get('good_configs', set()))
                print(f"  {ms} bin={bin_pos_rot}: VALID! cycle={cycle_len}, good={n_good}")
                props = result.get('properties', {})
                for k, v in props.items():
                    print(f"    {k}: {v}")
            else:
                props = result.get('properties', {})
                fail = next((f"{k}" for k, v in props.items()
                            if isinstance(v, tuple) and not v[0]
                            or isinstance(v, str)), "?")
                print(f"  {ms} bin={bin_pos_rot}: FAIL ({fail})")

    # Also try with ternary top being a binary proc
    print(f"\n{'─' * 60}")
    print("ALTERNATIVE: binary at bottom AND top positions")
    print(f"{'─' * 60}")

    # ms with binary at pos 0 and pos 8 (adjacent through wrap-around, sep=1)
    # Already covered by (2,3,3,3,3,3,3,3,2) rotation of sep=1 necklace

    # ms with binary at pos 0 and pos 4 (sep=4, binary at bottom+middle)
    ms_alt = (2, 3, 3, 3, 2, 3, 3, 3, 3)
    # In this case, P0=bottom (binary), P4=middle (binary)
    # All edges of binary procs involve ternary neighbors
    fs = sol3_adapt_v1(list(ms_alt), n)
    result = verify_system(list(ms_alt), fs)
    valid = result.get('valid', False)
    if valid:
        print(f"  {ms_alt}: VALID!")
        props = result.get('properties', {})
        for k, v in props.items():
            print(f"    {k}: {v}")
    else:
        print(f"  {ms_alt}: FAIL")

    # Try with binary at pos 8 (top) and some middle pos
    for pos2 in [1, 2, 3, 4]:
        ms_bt = [3] * n
        ms_bt[8] = 2  # top
        ms_bt[pos2] = 2  # middle
        ms_bt = tuple(ms_bt)
        fs = sol3_adapt_v1(list(ms_bt), n)
        result = verify_system(list(ms_bt), fs)
        valid = result.get('valid', False)
        if valid:
            cycle_len = result.get('cycle_length', '?')
            n_good = len(result.get('good_configs', set()))
            print(f"  {ms_bt}: VALID! cycle={cycle_len}, good={n_good}")
        else:
            props = result.get('properties', {})
            fail = next((f"{k}" for k, v in props.items()
                        if isinstance(v, tuple) and not v[0]), "?")
            print(f"  {ms_bt}: FAIL ({fail})")


if __name__ == "__main__":
    main()
