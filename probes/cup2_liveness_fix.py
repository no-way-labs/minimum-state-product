#!/usr/bin/env python3
"""Identify the liveness fix pattern for the Type A dead config.

The Type A dead config is (0,2,1,...,1,0) for all n ≥ 6.
Which entry does the greedy construction activate, and is there a universal fix?
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from cup2_clb_general import build_system_general
from cup2_universal_rules import T_bot, T_low, T_mid, T_high, T_top, build_universal_system


def main():
    print("LIVENESS FIX PATTERN")
    print("=" * 70)

    for nv in range(6, 13):
        prod = 4 * 3 ** (nv - 2)
        if prod > 500000:
            break

        ms_g, fs_g, comp_g, cycle_g, movers_g = build_system_general(nv)
        ms_u, fs_u = build_universal_system(nv, T_bot, T_low, T_mid, T_high, T_top)
        n = nv

        # Find the difference
        for p in range(n):
            m_L = ms_g[(p - 1) % n]
            m_S = ms_g[p]
            m_R = ms_g[(p + 1) % n]
            for L in range(m_L):
                for S in range(m_S):
                    for R in range(m_R):
                        u_val = fs_u[p](L, S, R)
                        g_val = fs_g[p](L, S, R)
                        if u_val != g_val:
                            print(f"n={nv}: P{p} f({L},{S},{R}): "
                                  f"universal={u_val}, greedy={g_val}")

    # The dead config is (0,2,1,...,1,0)
    print("\n\nDead config analysis:")
    print("-" * 60)
    for nv in range(6, 13):
        prod = 4 * 3 ** (nv - 2)
        if prod > 500000:
            break
        n = nv
        dead = tuple([0, 2] + [1] * (n - 3) + [0])
        print(f"\nn={nv}: dead config = {dead}")
        ms = [2] + [3] * (n - 2) + [2]

        # Which entries does each proc see?
        for p in range(n):
            L = dead[(p - 1) % n]
            S = dead[p]
            R = dead[(p + 1) % n]

            # What does universal rule give?
            if p == 0:
                u = T_bot[(L, S, R)]
            elif p == 1:
                u = T_low[(L, S, R)]
            elif p < n - 2:
                u = T_mid[(L, S, R)]
            elif p == n - 2:
                u = T_high[(L, S, R)]
            else:
                u = T_top[(L, S, R)]

            priv = "←PRIV" if u != S else "stay"
            print(f"  P{p}: f({L},{S},{R}) = {u} {priv}")

    # What if we fix the dead config by modifying T_mid at (2,1,1)?
    # Let's check: at the dead config, P2 sees (L=2, S=1, R=1).
    # T_mid says f(2,1,1)=1 (stay). If we set f(2,1,1)=0 or 2, P2 would fire.
    # But this would affect ALL configs where an interior proc sees (2,1,1).
    # Is that safe?
    print("\n\nProposed universal fix: T_mid(2,1,1) = 0 (instead of 1)")
    print("-" * 60)

    # Test: modify T_mid at (2,1,1) and check validity for all n
    T_mid_fixed = dict(T_mid)
    T_mid_fixed[(2, 1, 1)] = 0

    from verifier import verify_system
    import time

    for nv in range(6, 14):
        prod = 4 * 3 ** (nv - 2)
        if prod > 500000:
            break

        n = nv
        ms = [2] + [3] * (n - 2) + [2]

        def make_f(table):
            def f(L, S, R):
                return table[(L, S, R)]
            return f

        fs = [make_f(T_bot)]
        fs.append(make_f(T_low))
        for i in range(2, n - 2):
            fs.append(make_f(T_mid_fixed))
        fs.append(make_f(T_high))
        fs.append(make_f(T_top))

        t0 = time.time()
        # Check liveness
        all_configs = list(cartesian(*(range(m) for m in ms)))
        dead_count = sum(1 for c in all_configs if not any(
            fs[i](c[(i-1)%n], c[i], c[(i+1)%n]) != c[i] for i in range(n)))

        result = verify_system(ms, fs)
        elapsed = time.time() - t0
        valid = result['valid']
        if valid:
            gcnt = len(result.get('good_configs', set()))
            clen = result.get('cycle_length', '?')
            print(f"  n={nv}: dead={dead_count}, VALID, good={gcnt}, cycle={clen} ({elapsed:.1f}s)")
        else:
            props = result.get('properties', {})
            fail = {k: v[1] for k, v in props.items() if not v[0]}
            print(f"  n={nv}: dead={dead_count}, INVALID: {fail} ({elapsed:.1f}s)")

    # Also try f(2,1,1)=2
    print("\n\nAlternative fix: T_mid(2,1,1) = 2")
    print("-" * 60)
    T_mid_fixed2 = dict(T_mid)
    T_mid_fixed2[(2, 1, 1)] = 2

    for nv in range(6, 14):
        prod = 4 * 3 ** (nv - 2)
        if prod > 500000:
            break

        n = nv
        ms = [2] + [3] * (n - 2) + [2]

        def make_f(table):
            def f(L, S, R):
                return table[(L, S, R)]
            return f

        fs = [make_f(T_bot)]
        fs.append(make_f(T_low))
        for i in range(2, n - 2):
            fs.append(make_f(T_mid_fixed2))
        fs.append(make_f(T_high))
        fs.append(make_f(T_top))

        t0 = time.time()
        all_configs = list(cartesian(*(range(m) for m in ms)))
        dead_count = sum(1 for c in all_configs if not any(
            fs[i](c[(i-1)%n], c[i], c[(i+1)%n]) != c[i] for i in range(n)))

        result = verify_system(ms, fs)
        elapsed = time.time() - t0
        valid = result['valid']
        if valid:
            gcnt = len(result.get('good_configs', set()))
            clen = result.get('cycle_length', '?')
            print(f"  n={nv}: dead={dead_count}, VALID, good={gcnt}, cycle={clen} ({elapsed:.1f}s)")
        else:
            props = result.get('properties', {})
            fail = {k: v[1] for k, v in props.items() if not v[0]}
            print(f"  n={nv}: dead={dead_count}, INVALID: {fail} ({elapsed:.1f}s)")


if __name__ == "__main__":
    main()
