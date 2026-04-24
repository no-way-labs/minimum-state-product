#!/usr/bin/env python3
"""clb_fast_generalize.py — Optimized construction + verification for large n.

Uses integer encoding + numpy for batch operations. Handles n=16-20.
Key optimizations:
  - Integer config encoding with strides (no tuple creation)
  - numpy vectorized L/S/R extraction and counting
  - bytearray for O(1) good/bad lookups
  - Custom DFS convergence check with integer arithmetic
"""

import sys
import os
import time
import numpy as np

sys.path.insert(0, os.path.dirname(__file__))


def build_and_verify_fast(n, verbose=False):
    ms = tuple([2] + [3] * (n - 2) + [2])
    product_val = 4 * (3 ** (n - 2))

    # Mixed-radix encoding strides
    strides = [1]
    for i in range(1, n):
        strides.append(strides[-1] * ms[i - 1])

    def encode(c):
        s = 0
        for i in range(n):
            s += c[i] * strides[i]
        return s

    def decode(idx):
        c = [0] * n
        tmp = idx
        for i in range(n):
            c[i] = tmp % ms[i]
            tmp //= ms[i]
        return c

    t0 = time.time()

    # === Phase 1: Bounce cycle ===
    up_down = list(range(n)) + list(range(n - 2, 0, -1))
    config = [0] * n
    cycle = [list(config)]
    visited = {encode(config)}
    full = up_down * (n + 5)
    movers = None
    start_idx = encode(config)
    for step, mover in enumerate(full):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        idx = encode(config)
        if idx == start_idx:
            movers = full[:step + 1]
            break
        if idx in visited:
            return None
        visited.add(idx)
        cycle.append(list(config))

    if movers is None:
        return None

    cycle_len = len(cycle)
    t1 = time.time()
    print(f"  [1] Bounce cycle: {t1 - t0:.2f}s, len={cycle_len}")

    # === Phase 2: Mark good configs + determined entries ===
    is_good = bytearray(product_val)
    for c in cycle:
        is_good[encode(c)] = 1

    det = {}
    for idx_c in range(len(cycle)):
        c = cycle[idx_c]
        c_next = cycle[(idx_c + 1) % len(cycle)]
        mv = movers[idx_c]
        for p in range(n):
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            key = (p, L, S, R)
            if p == mv:
                det[key] = c_next[p]
            else:
                det[key] = S

    free_entries = []
    free_set = set()
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
                        free_set.add(key)

    t2 = time.time()
    print(f"  [2] Determined: {t2 - t1:.2f}s, det={len(det)}, free={len(free_entries)}")

    # === Phase 3: Good-targeting with numpy ===
    good_np = np.frombuffer(is_good, dtype=np.uint8).copy().astype(np.bool_)
    all_idx = np.arange(product_val, dtype=np.int64)

    comp = dict(det)
    edge_costs = {}

    # Group free entries by processor
    free_by_proc = {}
    for key in free_entries:
        p = key[0]
        if p not in free_by_proc:
            free_by_proc[p] = []
        free_by_proc[p].append(key)

    for p in sorted(free_by_proc.keys()):
        tp = time.time()
        p_left = (p - 1) % n
        p_right = (p + 1) % n
        L_arr = ((all_idx // strides[p_left]) % ms[p_left]).astype(np.int32)
        S_arr = ((all_idx // strides[p]) % ms[p]).astype(np.int32)
        R_arr = ((all_idx // strides[p_right]) % ms[p_right]).astype(np.int32)
        bad_mask = ~good_np

        for key in free_by_proc[p]:
            _, L_val, S_val, R_val = key
            mask = bad_mask & (L_arr == L_val) & (S_arr == S_val) & (R_arr == R_val)
            matching = all_idx[mask]

            if len(matching) == 0:
                comp[key] = S_val
                for out in range(ms[p]):
                    edge_costs[(key, out)] = 0
                continue

            best_out = S_val
            best_good = 0
            best_ng = 0

            for out in range(ms[p]):
                if out == S_val:
                    edge_costs[(key, out)] = 0
                    continue
                delta = int((out - S_val) * strides[p])
                new_idx = matching + delta
                gc = int(np.sum(good_np[new_idx]))
                nc = len(matching) - gc
                edge_costs[(key, out)] = nc
                if gc > best_good or (gc == best_good and nc < best_ng):
                    best_out = out
                    best_good = gc
                    best_ng = nc

            comp[key] = best_out

        if verbose:
            print(f"    P{p}: {time.time() - tp:.2f}s, "
                  f"{len(free_by_proc[p])} entries")

    # Free numpy arrays to save memory
    del L_arr, S_arr, R_arr, bad_mask, all_idx
    good_np_copy = good_np.copy()
    del good_np

    t3 = time.time()
    print(f"  [3] Good-targeting: {t3 - t2:.2f}s")

    # === Phase 4: Liveness fix ===
    liveness_fixes = 0
    for idx in range(product_val):
        c = decode(idx)
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
            best_cost = 999999999
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

    t4 = time.time()
    print(f"  [4] Liveness fix: {t4 - t3:.2f}s, fixes={liveness_fixes}")

    # === Phase 5: Build lookup tables ===
    f_tables = []
    for p in range(n):
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        table = [[[0] * m_R for _ in range(m_S)] for _ in range(m_L)]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    table[L][S][R] = comp.get((p, L, S, R), S)
        f_tables.append(table)

    # === Phase 6: Verification ===
    # 6a: Liveness (every config has a privilege)
    dead_count = 0
    for idx in range(product_val):
        c = decode(idx)
        has_priv = False
        for p in range(n):
            if f_tables[p][c[(p - 1) % n]][c[p]][c[(p + 1) % n]] != c[p]:
                has_priv = True
                break
        if not has_priv:
            dead_count += 1
    t6a = time.time()
    print(f"  [6a] Liveness: {t6a - t4:.2f}s, dead={dead_count}")
    if dead_count > 0:
        return {'valid': False, 'reason': f'{dead_count} dead',
                'cycle_len': cycle_len, 'liveness_fixes': liveness_fixes}

    # 6b: Find single-privilege configs, build successor map
    succ_map = {}
    mover_map = {}
    single_count = 0
    for idx in range(product_val):
        c = decode(idx)
        privs = []
        for p in range(n):
            if f_tables[p][c[(p - 1) % n]][c[p]][c[(p + 1) % n]] != c[p]:
                privs.append(p)
        if len(privs) == 1:
            single_count += 1
            p = privs[0]
            new_S = f_tables[p][c[(p - 1) % n]][c[p]][c[(p + 1) % n]]
            new_idx = idx + (new_S - c[p]) * strides[p]
            succ_map[idx] = new_idx
            mover_map[idx] = p

    t6b = time.time()
    print(f"  [6b] Single-priv: {t6b - t6a:.2f}s, count={single_count}")

    # 6c: Find closed set + cycle
    good_candidates = set(succ_map.keys())
    changed = True
    while changed:
        changed = False
        to_remove = []
        for idx in good_candidates:
            if succ_map[idx] not in good_candidates:
                to_remove.append(idx)
        if to_remove:
            for idx in to_remove:
                good_candidates.discard(idx)
            changed = True

    # Find cycle
    visited_g = set()
    the_cycle = None
    for start in good_candidates:
        if start in visited_g:
            continue
        path = []
        path_set = set()
        node = start
        while node not in visited_g and node not in path_set:
            path.append(node)
            path_set.add(node)
            node = succ_map[node]
        if node in path_set:
            ci = path.index(node)
            the_cycle = path[ci:]
        visited_g.update(path)
        if the_cycle:
            break

    if the_cycle is None:
        return {'valid': False, 'reason': 'no cycle found'}

    # Build full good set (cycle + tails)
    cycle_set = set(the_cycle)
    good_final = set(cycle_set)
    rev = {}
    for idx in good_candidates:
        s = succ_map[idx]
        if s not in rev:
            rev[s] = []
        rev[s].append(idx)
    queue = list(cycle_set)
    while queue:
        node = queue.pop()
        for pred in rev.get(node, []):
            if pred not in good_final:
                good_final.add(pred)
                queue.append(pred)

    # Fairness
    procs_in_cycle = set()
    for idx in the_cycle:
        procs_in_cycle.add(mover_map[idx])
    fair = procs_in_cycle == set(range(n))

    t6c = time.time()
    print(f"  [6c] Closed set: {t6c - t6b:.2f}s, good={len(good_final)}, "
          f"cycle_len={len(the_cycle)}, fair={fair}")

    if not fair:
        return {'valid': False, 'reason': 'fairness failed',
                'cycle_len': len(the_cycle), 'good_count': len(good_final)}

    # 6d: Convergence — DFS on bad configs
    # Mark good in bytearray for O(1) lookup
    is_good_final = bytearray(product_val)
    for idx in good_final:
        is_good_final[idx] = 1

    color = bytearray(product_val)  # 0=white, 1=gray, 2=black
    has_bad_cycle = False
    bad_count = product_val - len(good_final)

    checked = 0
    for start in range(product_val):
        if is_good_final[start] or color[start] != 0:
            continue
        stack = [(start, 0)]  # (node, next_proc_to_check)
        color[start] = 1

        while stack:
            node, pi = stack[-1]

            # Find next privileged successor in bad
            found = False
            c = decode(node)
            while pi < n:
                L = c[(pi - 1) % n]
                S = c[pi]
                R = c[(pi + 1) % n]
                new_S = f_tables[pi][L][S][R]
                if new_S != S:
                    new_idx = node + (new_S - S) * strides[pi]
                    if not is_good_final[new_idx]:
                        if color[new_idx] == 1:
                            has_bad_cycle = True
                            break
                        if color[new_idx] == 0:
                            stack[-1] = (node, pi + 1)
                            color[new_idx] = 1
                            stack.append((new_idx, 0))
                            found = True
                            break
                pi += 1

            if has_bad_cycle:
                break
            if not found:
                color[node] = 2
                stack.pop()
                checked += 1
                if checked % 1000000 == 0:
                    elapsed = time.time() - t6c
                    pct = checked / bad_count * 100 if bad_count > 0 else 100
                    print(f"    DFS: {checked}/{bad_count} "
                          f"({pct:.1f}%) {elapsed:.1f}s")

        if has_bad_cycle:
            break

    t6d = time.time()
    print(f"  [6d] Convergence: {t6d - t6c:.2f}s, "
          f"cycle={'YES' if has_bad_cycle else 'NO'}")

    total_time = t6d - t0

    if has_bad_cycle:
        return {'valid': False, 'reason': 'convergence failed (bad cycle)',
                'cycle_len': len(the_cycle), 'good_count': len(good_final)}

    return {
        'valid': True,
        'n': n,
        'ms': ms,
        'product': product_val,
        'cycle_len': len(the_cycle),
        'good_count': len(good_final),
        'bad_count': bad_count,
        'liveness_fixes': liveness_fixes,
        'det_entries': len(det),
        'free_entries': len(free_entries),
        'total_time': total_time,
        'f_tables': f_tables,
        'comp': comp,
    }


if __name__ == "__main__":
    print("=" * 80)
    print("Fast good-targeting construction: ms=(2,3,...,3,2), product=4*3^(n-2)")
    print("=" * 80)

    # Parse command line for n range
    if len(sys.argv) >= 3:
        n_min = int(sys.argv[1])
        n_max = int(sys.argv[2])
    elif len(sys.argv) == 2:
        n_min = n_max = int(sys.argv[1])
    else:
        n_min = 16
        n_max = 18

    results = []
    for n_val in range(n_min, n_max + 1):
        pv = 4 * (3 ** (n_val - 2))
        print(f"\n{'─' * 80}")
        print(f"n={n_val}: product=4*3^{n_val - 2}={pv:,}")
        print(f"{'─' * 80}")

        r = build_and_verify_fast(n_val, verbose=True)
        if r is None:
            print("  FAILED: cycle didn't close")
            continue

        results.append(r)
        status = "VALID" if r['valid'] else "FAILED"
        print(f"\n  >>> {status} <<<")
        if r['valid']:
            print(f"  cycle={r['cycle_len']}, good={r['good_count']}, "
                  f"bad={r['bad_count']}, fixes={r['liveness_fixes']}")
            # Verify formulas
            cl_pred = 3 * n_val - 2
            gc_pred = n_val ** 2 - 2 * n_val + 8
            fx_pred = n_val - 3
            print(f"  Formula check: cycle={cl_pred}={'OK' if r['cycle_len'] == cl_pred else 'MISMATCH'}, "
                  f"good={gc_pred}={'OK' if r['good_count'] == gc_pred else 'MISMATCH'}, "
                  f"fixes={fx_pred}={'OK' if r['liveness_fixes'] == fx_pred else 'MISMATCH'}")
        print(f"  Total time: {r['total_time']:.1f}s")

    # Summary
    if results:
        print(f"\n{'=' * 80}")
        print("SUMMARY")
        print(f"{'=' * 80}")
        for r in results:
            if r['valid']:
                print(f"  n={r['n']}: VALID, product={r['product']:,}, "
                      f"cycle={r['cycle_len']}, good={r['good_count']}, "
                      f"time={r['total_time']:.1f}s")
            else:
                print(f"  n={r['n']}: FAILED ({r.get('reason', '?')})")
