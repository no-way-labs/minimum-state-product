#!/usr/bin/env python3
"""clb_generalize_n.py — Test good-targeting construction for all n >= 5.

Construction: ms = (2, 3, ..., 3, 2), product = 4·3^(n-2).
1. Build endpoint-binary bounce cycle with up-down mover pattern
2. Good-targeting completion (optimized with triple pre-indexing)
3. Liveness fix
4. Full 5-property verification

Tests whether M_n <= 4·3^(n-2) for all n >= 5.
"""

import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict
from verifier import verify_system


def build_and_verify(n, verbose=False):
    """Build and verify the good-targeting system for n processors.

    Returns dict with all results, or None if bounce cycle fails.
    """
    ms = tuple([2] + [3] * (n - 2) + [2])
    product_val = 4 * (3 ** (n - 2))

    t0 = time.time()

    # === Phase 1: Build bounce cycle ===
    up_down = list(range(n)) + list(range(n - 2, 0, -1))
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    max_steps = len(up_down) * (n + 5)
    full = up_down * (n + 5)
    movers = None
    for step, mover in enumerate(full):
        if step >= max_steps:
            break
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            movers = full[:step + 1]
            break
        if nc in visited:
            return None  # cycle didn't close cleanly
        visited.add(nc)
        cycle.append(nc)

    if movers is None:
        return None

    cycle_len = len(cycle)
    good_set = set(cycle)

    t1 = time.time()

    # === Phase 2: Enumerate configs ===
    all_configs = list(cartesian(*(range(m) for m in ms)))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    t2 = time.time()

    # === Phase 3: Extract determined entries ===
    det = {}
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        mv = movers[idx]
        for p in range(n):
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            key = (p, L, S, R)
            if p == mv:
                det[key] = c_next[p]
            else:
                det[key] = S

    # Find free entries
    free_entries = []
    for p in range(n):
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    if key not in det:
                        free_entries.append(key)

    t3 = time.time()

    # === Phase 4: Pre-index non-good configs by free triples ===
    free_set = set(free_entries)
    triple_index = defaultdict(list)
    for c in non_good:
        for p in range(n):
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            key = (p, L, S, R)
            if key in free_set:
                triple_index[key].append(c)

    t4 = time.time()

    # === Phase 5: Good-targeting completion + edge costs ===
    edge_costs = {}
    comp = dict(det)

    for key in free_entries:
        p, L, S, R = key
        matching = triple_index.get(key, [])
        best_out = S
        best_good = 0
        best_ng = 0  # S has 0 non-good->non-good edges (identity)

        for out in range(ms[p]):
            if out == S:
                edge_costs[(key, out)] = 0
                continue
            good_count = 0
            ng_count = 0
            for c in matching:
                new_c_t = c[:p] + (out,) + c[p + 1:]
                if new_c_t in good_set:
                    good_count += 1
                elif new_c_t in non_good_set:
                    ng_count += 1
            edge_costs[(key, out)] = ng_count
            if good_count > best_good or (good_count == best_good and ng_count < best_ng):
                best_out = out
                best_good = good_count
                best_ng = ng_count

        comp[key] = best_out

    t5 = time.time()

    # === Phase 6: Liveness fix ===
    liveness_fixes = 0
    for c in all_configs:
        has_priv = False
        for p in range(n):
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            if comp.get((p, L, S, R), S) != S:
                has_priv = True
                break
        if not has_priv:
            best_key = None
            best_cost = float('inf')
            best_out_val = None
            for p in range(n):
                L2 = c[(p - 1) % n]
                S2 = c[p]
                R2 = c[(p + 1) % n]
                key = (p, L2, S2, R2)
                if key not in det:
                    for out in range(ms[p]):
                        if out != S2:
                            cost = edge_costs.get((key, out), 0)
                            if cost < best_cost:
                                best_cost = cost
                                best_key = key
                                best_out_val = out
            if best_key:
                comp[best_key] = best_out_val
                liveness_fixes += 1

    t6 = time.time()

    # === Phase 7: Build transition functions and verify ===
    def make_f(p_idx):
        def f(L, S, R):
            return comp.get((p_idx, L, S, R), S)
        return f

    fs = [make_f(p) for p in range(n)]
    result = verify_system(list(ms), fs, verbose=verbose)

    t7 = time.time()

    # Collect mover sequence info
    movers_set = set()
    for m in movers:
        movers_set.add(m)

    return {
        'n': n,
        'ms': ms,
        'product': product_val,
        'cycle_len': cycle_len,
        'good_count': len(good_set) if result['valid'] else len(good_set),
        'verified_good': result.get('good_configs', None),
        'bad_count': len(non_good),
        'free_entries': len(free_entries),
        'det_entries': len(det),
        'liveness_fixes': liveness_fixes,
        'valid': result['valid'],
        'properties': result.get('properties', {}),
        'result': result,
        'timings': {
            'bounce_cycle': t1 - t0,
            'enumerate': t2 - t1,
            'determined': t3 - t2,
            'index': t4 - t3,
            'good_targeting': t5 - t4,
            'liveness_fix': t6 - t5,
            'verification': t7 - t6,
            'total': t7 - t0,
        },
    }


if __name__ == "__main__":
    print("=" * 80)
    print("Good-targeting construction: ms=(2,3,...,3,2), product=4*3^(n-2)")
    print("Testing conjecture: M_n <= 4*3^(n-2) for all n >= 5")
    print("=" * 80)

    results = []
    max_n = 15

    for n in range(5, max_n + 1):
        product_val = 4 * (3 ** (n - 2))
        print(f"\n{'─' * 80}")
        print(f"n={n}: ms=(2,{'3,' * (n - 2)}2), product=4*3^{n - 2}={product_val}")
        print(f"{'─' * 80}")

        if product_val > 8_000_000:
            print(f"  Skipping: product {product_val} too large")
            results.append({'n': n, 'product': product_val, 'valid': None,
                            'reason': 'too_large'})
            continue

        r = build_and_verify(n, verbose=False)

        if r is None:
            print(f"  FAILED: bounce cycle did not close")
            results.append({'n': n, 'product': product_val, 'valid': None,
                            'reason': 'cycle_failed'})
            continue

        results.append(r)

        status = "VALID" if r['valid'] else "FAILED"
        print(f"  Status: {status}")
        print(f"  Cycle length: {r['cycle_len']}")

        # Get verified good count from verifier if available
        vg = r.get('verified_good')
        if vg:
            print(f"  Good configs (verified): {len(vg)}")
        print(f"  Good configs (cycle): {r['good_count']}")
        print(f"  Bad configs: {r['bad_count']}")
        print(f"  Determined: {r['det_entries']}, Free: {r['free_entries']}")
        print(f"  Liveness fixes: {r['liveness_fixes']}")

        for prop, (ok, msg) in r['properties'].items():
            mark = '+' if ok else 'X'
            print(f"  [{mark}] {prop}: {msg}")

        t = r['timings']
        print(f"  Time: {t['total']:.1f}s "
              f"(cycle:{t['bounce_cycle']:.2f} enum:{t['enumerate']:.2f} "
              f"idx:{t['index']:.2f} gt:{t['good_targeting']:.2f} "
              f"live:{t['liveness_fix']:.2f} verify:{t['verification']:.2f})")

    # === Summary table ===
    print(f"\n\n{'=' * 80}")
    print("SUMMARY TABLE")
    print(f"{'=' * 80}")
    hdr = (f"{'n':>3} {'product':>10} {'valid':>6} {'cycle':>6} {'good':>8} "
           f"{'bad':>10} {'good%':>7} {'fixes':>6} {'time':>8}")
    print(hdr)
    print("─" * len(hdr))

    for r in results:
        n_val = r['n']
        pv = r['product']
        if r.get('valid') is None:
            reason = r.get('reason', '?')
            print(f"{n_val:>3} {pv:>10} {'SKIP':>6}  ({reason})")
            continue
        vg = r.get('verified_good')
        gc = len(vg) if vg else r['good_count']
        pct = gc / r['product'] * 100
        print(f"{n_val:>3} {pv:>10} {'YES' if r['valid'] else 'NO':>6} "
              f"{r['cycle_len']:>6} {gc:>8} {r['bad_count']:>10} "
              f"{pct:>6.2f}% {r['liveness_fixes']:>6} "
              f"{r['timings']['total']:>7.1f}s")

    # === Pattern analysis ===
    print(f"\n{'=' * 80}")
    print("PATTERN ANALYSIS")
    print(f"{'=' * 80}")

    valid_results = [r for r in results if r.get('valid') is not None]
    if len(valid_results) >= 2:
        print("\nBounce cycle length as function of n:")
        for r in valid_results:
            nv = r['n']
            cl = r['cycle_len']
            formulas = {
                '2n-1': 2 * nv - 1,
                '2(n-1)+1': 2 * (nv - 1) + 1,
                '3n-2': 3 * nv - 2,
                'lcm-based': None,
            }
            matches = [name for name, val in formulas.items()
                       if val is not None and val == cl]
            match_str = f" = {', '.join(matches)}" if matches else ""
            print(f"  n={nv}: cycle_len={cl}{match_str}")

        print("\nGood config ratio (good/product):")
        for r in valid_results:
            nv = r['n']
            vg = r.get('verified_good')
            gc = len(vg) if vg else r['good_count']
            ratio = gc / r['product']
            print(f"  n={nv}: good={gc}, product={r['product']}, "
                  f"ratio={ratio:.6f}")

        # Check if good count follows a formula
        print("\nGood config count patterns:")
        for r in valid_results:
            nv = r['n']
            vg = r.get('verified_good')
            gc = len(vg) if vg else r['good_count']
            formulas = {
                '8n-10': 8 * nv - 10,
                '8n-8': 8 * nv - 8,
                '6n-5': 6 * nv - 5,
            }
            matches = [f"{name}={val}" for name, val in formulas.items()
                       if val == gc]
            match_str = f"  matches: {', '.join(matches)}" if matches else ""
            print(f"  n={nv}: good={gc}{match_str}")

    # Final verdict
    print(f"\n{'=' * 80}")
    all_valid = all(r['valid'] for r in results if r.get('valid') is not None)
    tested = [r['n'] for r in results if r.get('valid') is not None]
    if all_valid and tested:
        print(f"CONJECTURE SUPPORTED: M_n <= 4*3^(n-2) verified for n={min(tested)}..{max(tested)}")
    else:
        failed = [r['n'] for r in results if r.get('valid') == False]
        if failed:
            print(f"CONJECTURE FAILS at n={failed}")
        passed = [r['n'] for r in results if r.get('valid') == True]
        if passed:
            print(f"Valid at n={passed}")
    print(f"{'=' * 80}")
