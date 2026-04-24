#!/usr/bin/env python3
"""n8_n9_witness_analysis.py — Analyze the ACTUAL M_5=96 and M_8=2592 witnesses.

The key error in previous analysis: we assumed minimum-length cycles (CL=sum(ms)).
But actual valid systems can have LONGER good cycles! The M_9=8748 witness has CL=25
for ms=(2,3,3,3,3,3,3,3,2), where sum(ms)=23.

With longer cycles, procs fire MORE than m_p times, using context-dependent transitions.
This changes the entire entry conflict picture.

Let's look at what ACTUAL valid systems do.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict
from math import prod
from verifier import verify_system

def build_bounce_verified(n, ms):
    """Build bounce-cycle system with good-targeting completion, return verification result."""
    up_down = list(range(n)) + list(range(n - 2, 0, -1))
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    full = up_down * (n + 5)
    movers = None
    for step, mover in enumerate(full):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            movers = full[:step + 1]
            break
        if nc in visited:
            return None
        visited.add(nc)
        cycle.append(nc)

    if movers is None:
        return None

    good_set = set(cycle)
    all_configs = list(cartesian(*(range(m) for m in ms)))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    det = {}
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        mv = movers[idx]
        for p in range(n):
            L = c[(p - 1) % n]; S = c[p]; R = c[(p + 1) % n]
            key = (p, L, S, R)
            if p == mv:
                det[key] = c_next[p]
            else:
                det[key] = S

    free_entries = []
    for p in range(n):
        m_L = ms[(p - 1) % n]; m_S = ms[p]; m_R = ms[(p + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    if key not in det:
                        free_entries.append(key)

    triple_index = defaultdict(list)
    for c in non_good:
        for p in range(n):
            L = c[(p-1) % n]; S = c[p]; R = c[(p+1) % n]
            triple_index[(p, L, S, R)].append(c)

    comp = dict(det)
    for key in free_entries:
        p, L, S, R = key
        best_out = S; best_good = 0; best_ng = float('inf')
        for out in range(ms[p]):
            if out == S:
                ng = 0; gc = 0
            else:
                gc = sum(1 for c in triple_index.get(key, [])
                         if tuple(c[j] if j != p else out for j in range(n)) in good_set)
                ng = sum(1 for c in triple_index.get(key, [])
                         if tuple(c[j] if j != p else out for j in range(n)) in non_good_set)
            if gc > best_good or (gc == best_good and ng < best_ng):
                best_out = out; best_good = gc; best_ng = ng
        comp[key] = best_out

    for c in all_configs:
        has_priv = any(comp.get((p, c[(p-1)%n], c[p], c[(p+1)%n]), c[p]) != c[p] for p in range(n))
        if not has_priv:
            for p in range(n):
                L2 = c[(p-1)%n]; S2 = c[p]; R2 = c[(p+1)%n]
                key = (p, L2, S2, R2)
                if key not in det:
                    for out in range(ms[p]):
                        if out != S2:
                            comp[key] = out
                            break
                    break

    def make_f(p_idx):
        def f(L, S, R):
            return comp.get((p_idx, L, S, R), S)
        return f

    fs = [make_f(p) for p in range(n)]
    return {
        'ms': ms, 'fs': fs, 'comp': comp, 'cycle': cycle, 'movers': movers,
        'good_set': good_set, 'det': det, 'free_entries': free_entries,
        'non_good': non_good, 'non_good_set': non_good_set,
    }


def analyze_witness_cycle(sys_info, verified_result):
    """Analyze the good cycle of a verified witness."""
    n = len(sys_info['ms'])
    ms = sys_info['ms']
    fs = sys_info['fs']

    # Get the good cycle from verified result
    if not verified_result.get('valid'):
        print("  System not valid!")
        return

    good_configs = verified_result.get('good_configs', set())
    if not good_configs:
        print("  No good configs returned!")
        return

    # Build the good cycle by following the deterministic successor map
    start = min(good_configs)
    cycle = [start]
    movers_list = []
    visited = {start}
    c = start
    while True:
        # Find privileged proc
        priv = []
        for p in range(n):
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
            if fs[p](L, S, R) != S:
                priv.append(p)
        if len(priv) != 1:
            print(f"  Config {c} has {len(priv)} privileged procs!")
            break
        mv = priv[0]
        movers_list.append(mv)
        new_c = list(c)
        new_c[mv] = fs[mv](c[(mv-1)%n], c[mv], c[(mv+1)%n])
        new_c = tuple(new_c)
        if new_c == start:
            break
        if new_c in visited:
            print(f"  Cycle doesn't return to start!")
            break
        visited.add(new_c)
        cycle.append(new_c)
        c = new_c

    CL = len(cycle)
    print(f"  Good cycle length: {CL}")
    print(f"  sum(ms) = {sum(ms)} (minimum possible CL with inc/dec)")
    print(f"  CL > sum(ms): {CL > sum(ms)} (extra cycle length: {CL - sum(ms)})")

    # Fire counts per proc
    fire_counts = defaultdict(int)
    for mv in movers_list:
        fire_counts[mv] += 1
    print(f"  Fire counts: {dict(fire_counts)}")
    for p in range(n):
        fc = fire_counts.get(p, 0)
        print(f"    P{p} (m={ms[p]}): fires {fc} times ({fc/ms[p]:.1f}x)")

    # Transition analysis: is it incrementing?
    for p in range(n):
        inc_count = 0
        dec_count = 0
        other_count = 0
        for idx in range(CL):
            if movers_list[idx] == p:
                c = cycle[idx]
                old_val = c[p]
                new_val = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
                if new_val == (old_val + 1) % ms[p]:
                    inc_count += 1
                elif new_val == (old_val - 1) % ms[p]:
                    dec_count += 1
                else:
                    other_count += 1
        if fire_counts.get(p, 0) > 0:
            print(f"    P{p}: {inc_count} inc, {dec_count} dec, {other_count} other")

    # Entry conflict analysis
    mover_ctx = defaultdict(set)
    nonmover_ctx = defaultdict(set)
    for idx in range(CL):
        c = cycle[idx]
        mv = movers_list[idx]
        for p in range(n):
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
            ctx = (L, S, R)
            if p == mv:
                mover_ctx[p].add(ctx)
            else:
                nonmover_ctx[p].add(ctx)

    total_ec = 0
    for p in range(n):
        overlap = mover_ctx[p] & nonmover_ctx[p]
        total_ec += len(overlap)
        if overlap:
            print(f"  EC at P{p}: {overlap}")

    print(f"  Total entry conflicts: {total_ec}")
    return CL, movers_list, cycle


if __name__ == "__main__":
    # ================================================================
    # PART 1: Analyze M_5 = 96 witness
    # ================================================================
    print("=" * 70)
    print("PART 1: M_5 = 96 witness")
    print("=" * 70)

    n = 5
    ms_list = [
        (2, 2, 2, 3, 4),
    ]

    for ms in ms_list:
        ms_tuple = tuple(ms)
        product_val = prod(ms_tuple)
        print(f"\nms={ms_tuple}, product={product_val}")

        sys_info = build_bounce_verified(n, ms_tuple)
        if sys_info is None:
            print("  Bounce cycle failed!")
            continue

        result = verify_system(list(ms_tuple), sys_info['fs'], verbose=False)
        print(f"  Verified: {result['valid']}")
        if result['valid']:
            for prop, (ok, msg) in result['properties'].items():
                print(f"    {prop}: {ok} — {msg}")
            analyze_witness_cycle(sys_info, result)

    # ================================================================
    # PART 2: Analyze M_8 = 2592 witness
    # ================================================================
    print("\n" + "=" * 70)
    print("PART 2: M_8 = 2592 candidates")
    print("=" * 70)

    n = 8
    # Try various ms arrangements with product 2592 = 32*3^4
    # Multisets with product 2592: 2^3 * 4 * 3^4
    arrangements = [
        (2, 2, 2, 4, 3, 3, 3, 3),
        (2, 2, 2, 3, 4, 3, 3, 3),
        (2, 2, 2, 3, 3, 4, 3, 3),
        (2, 2, 2, 3, 3, 3, 4, 3),
        (2, 2, 2, 3, 3, 3, 3, 4),
        (2, 3, 2, 3, 4, 3, 2, 3),
        (2, 3, 2, 4, 3, 2, 3, 3),
        (2, 3, 3, 2, 3, 4, 2, 3),
        (3, 2, 3, 2, 3, 4, 2, 3),
    ]

    valid_found = []
    for ms in arrangements:
        ms_tuple = tuple(ms)
        product_val = prod(ms_tuple)
        if product_val != 2592:
            continue

        sys_info = build_bounce_verified(n, ms_tuple)
        if sys_info is None:
            print(f"  ms={ms_tuple}: bounce cycle failed")
            continue

        result = verify_system(list(ms_tuple), sys_info['fs'], verbose=False)
        status = "VALID" if result['valid'] else "INVALID"
        if result['valid']:
            valid_found.append(ms_tuple)
            print(f"\n  ms={ms_tuple}: {status}")
            for prop, (ok, msg) in result['properties'].items():
                print(f"    {prop}: {ok} — {msg}")
            analyze_witness_cycle(sys_info, result)
        else:
            reason = list(result['properties'].values())[-1][1] if result['properties'] else "?"
            print(f"  ms={ms_tuple}: {status} ({reason})")

    if not valid_found:
        print("\nNo valid system found with bounce cycle + good-targeting at n=8!")
        print("Trying different construction approach...")

    # ================================================================
    # PART 3: Try the CUP-2 construction at n=8
    # ================================================================
    print("\n" + "=" * 70)
    print("PART 3: CUP-2 style ms=(2,3,...,3,2) at n=8")
    print("=" * 70)

    n = 8
    ms = tuple([2] + [3]*(n-2) + [2])
    product_val = prod(ms)
    print(f"ms={ms}, product={product_val} (threshold = 4*3^6 = {4*3**6})")

    sys_info = build_bounce_verified(n, ms)
    if sys_info is None:
        print("  Bounce cycle failed!")
    else:
        result = verify_system(list(ms), sys_info['fs'], verbose=False)
        print(f"  Verified: {result['valid']}")
        if result['valid']:
            for prop, (ok, msg) in result['properties'].items():
                print(f"    {prop}: {ok} — {msg}")
            analyze_witness_cycle(sys_info, result)

    # ================================================================
    # PART 4: What IS the M_8 witness? Is it at product 2592 or 2916?
    # ================================================================
    print("\n" + "=" * 70)
    print("PART 4: Verify M_8 value")
    print("=" * 70)
    print("M_8 = 32*3^4 = 2592. This uses ms with 3 binary + 1 quaternary + 4 ternary.")
    print("But do we actually have a witness?")
    print()

    # Try all possible multisets with product 2592 = 2^5 * 3^4 = 2*2*2*4*3*3*3*3
    # at n=8
    # 2592 = 2^5 * 3^4
    # Need 8 factors, each >= 2
    # Possible factorizations into 8 parts each >= 2:
    # The parts sorted: 2,2,2,2,2,3,3,3 -> product = 32*27 = 864 (not 2592)
    # Need product 2592 with 8 factors >= 2
    # 2592 = 2^5 * 3^4
    # Options: {2,2,2,2,2,3,3,3,3} = 9 numbers -> too many for n=8
    # Wait: 2^5 * 3^4 = 32 * 81 = 2592. With 8 factors >= 2:
    # 2,2,2,4,3,3,3,3 -> product = 8*4*81 = 2592. Yes!
    # 2,2,2,2,3,3,3,6 -> product = 16*3^3*6 = 16*162 = 2592. But 6 is new.
    # 2,2,2,2,3,3,9,1 -> has a 1, not allowed.

    # Actually the claim was M_n = 32*3^(n-4) for n=5..8.
    # At n=5: 32*3 = 96 = 2*2*2*3*4. Known valid.
    # At n=6: 32*9 = 288 = 2*2*2*3*4*3. Known valid?
    # At n=7: 32*27 = 864 = 2*2*2*3*4*3*3. Known valid?
    # At n=8: 32*81 = 2592 = 2*2*2*3*4*3*3*3. Known valid?

    # Let me check if M_8 is really 2592 or if it's 2916 = 4*3^6
    print("Is M_8 = 2592 or 2916?")
    print("2592 = 32*3^4 = 2^5*3^4")
    print("2916 = 4*3^6")
    print()

    # Check: does ms=(2,3,3,3,3,3,3,2) at product 2916 have a valid system?
    ms_2916 = tuple([2] + [3]*6 + [2])
    print(f"ms={ms_2916}, product={prod(ms_2916)}")
    sys_info = build_bounce_verified(8, ms_2916)
    if sys_info:
        result = verify_system(list(ms_2916), sys_info['fs'], verbose=False)
        print(f"  Verified: {result['valid']}")
        if result['valid']:
            for prop, (ok, msg) in result['properties'].items():
                print(f"    {prop}: {ok} — {msg}")

    # ================================================================
    # PART 5: Cycle length comparison between n=8 and n=9 for the
    # construction that WORKS: ms=(2,3,...,3,2)
    # ================================================================
    print("\n" + "=" * 70)
    print("PART 5: CUP-2 ms=(2,3,...,3,2) — cycle lengths and EC")
    print("=" * 70)

    for n in range(5, 12):
        ms = tuple([2] + [3]*(n-2) + [2])
        product_val = prod(ms)
        threshold = 4 * 3**(n-2)
        CL_min = sum(ms)  # minimum cycle length

        sys_info = build_bounce_verified(n, ms)
        if sys_info is None:
            print(f"n={n}: ms={ms}, product={product_val}, bounce failed")
            continue

        CL = len(sys_info['cycle'])

        # Check EC for the bounce cycle
        mover_ctx = defaultdict(set)
        nonmover_ctx = defaultdict(set)
        for idx in range(CL):
            c = sys_info['cycle'][idx]
            mv = sys_info['movers'][idx]
            for p in range(n):
                L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
                if p == mv:
                    mover_ctx[p].add((L, S, R))
                else:
                    nonmover_ctx[p].add((L, S, R))

        ec_total = sum(len(mover_ctx[p] & nonmover_ctx[p]) for p in range(n))

        # Fire counts
        fire_counts = defaultdict(int)
        for mv in sys_info['movers']:
            fire_counts[mv] += 1

        max_fire_ratio = max(fire_counts.get(p, 0) / ms[p] for p in range(n))

        # Context utilization per proc
        max_util = 0
        for p in range(n):
            m_L = ms[(p-1)%n]; m_S = ms[p]; m_R = ms[(p+1)%n]
            ctx_size = m_L * m_S * m_R
            used = len(mover_ctx[p] | nonmover_ctx[p])
            util = used / ctx_size
            if util > max_util:
                max_util = util

        result = verify_system(list(ms), sys_info['fs'], verbose=False)
        valid = result['valid']

        print(f"n={n}: ms={ms}, prod={product_val}, CL={CL}, sum(ms)={CL_min}, "
              f"EC={ec_total}, max_fire={max_fire_ratio:.1f}x, max_util={max_util:.3f}, "
              f"valid={valid}")
