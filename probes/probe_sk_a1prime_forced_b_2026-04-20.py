#!/usr/bin/env python3
"""E18: forced-B-conflict probe.

Per agent's suggestion post-E17 MECHANISM-FAIL: instead of decomposing A1'
via case split, check whether every A1'-violator pinned-det attempt
produces a specific SHARED B-conflict shape. If yes, that shape is the
concrete Lean proof target.

For each (p, L, R, S1, S2, v) pinned attempt:
  - Run DFS, collect the SET of B-conflict signatures encountered.
  - Across all attempts at n=5, look for:
    * Attempts where only a SINGLE B-conflict shape arises (forced).
    * Attempts that never produce B-conflicts (other pruning suffices).
    * Intersection: any B-conflict key that appears in EVERY attempt.

If some B-conflict key is universal across A1' violators, we have a
structural target: prove that pinning det creates that specific conflict.
"""
from __future__ import annotations

import time
from collections import Counter, defaultdict
from itertools import product as iproduct


def enumerate_cycles_collect_b(ms, n, L_max, tb, pinned, max_cycles):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []; seen = set(); t0 = time.time()
    b_keys = set()  # set of (ki, pinned_v, needs_stay) that triggered B-conflicts
    had_b = False

    def dfs(start, config, det, path, movers):
        nonlocal had_b
        if len(found) >= max_cycles or time.time()-t0 > tb: return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)): return
            L = len(movers)
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen:
                seen.add(norm); found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max: return
        for p in range(n):
            Lp = config[(p-1)%n]; Sp = config[p]; Rp = config[(p+1)%n]
            km = (p, Lp, Sp, Rp); forced_out = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp: continue
                if forced_out is not None and forced_out != new_val: continue
                new_det = dict(det); new_det[km] = new_val; ok = True
                for i in range(n):
                    if i == p: continue
                    Li = config[(i-1)%n]; Si = config[i]; Ri = config[(i+1)%n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si:
                        b_keys.add((ki, new_det[ki], Si))
                        had_b = True
                        ok = False; break
                    new_det[ki] = Si
                if not ok: continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if nc != start and nc in set(path): continue
                dfs(start, nc, new_det, path + [nc], movers + [p])

    for start in all_starts:
        if len(found) >= max_cycles or time.time()-t0 > tb: break
        dfs(start, start, dict(pinned), [start], [])
    return found, b_keys, had_b


if __name__ == "__main__":
    print("=" * 72)
    print("E18: forced-B-conflict probe (2026-04-20)")
    print("=" * 72)

    # Focus on n=5, a single ternary multiset, exhaustive over all A1' pinned-det
    # attempts to find shared B-conflict structure.
    trials = [
        (5, (3, 3, 3, 3, 3), 15, 5.0),
        (5, (2, 3, 3, 3, 3), 15, 5.0),
    ]

    all_attempts_b_keys = []  # list of (pin_desc, set_of_b_keys)
    no_b_attempts = []
    total_attempts = 0
    t_global = time.time()

    for n, ms, L_max, tb in trials:
        print(f"\n--- n={n}, ms={ms} ---", flush=True)
        for p in range(n):
            if ms[p] < 3: continue
            for L_val in range(ms[(p-1)%n]):
                for R_val in range(ms[(p+1)%n]):
                    for S1 in range(ms[p]):
                        for S2 in range(S1+1, ms[p]):
                            for v in range(ms[p]):
                                if v == S1 or v == S2: continue
                                pinned = {
                                    (p, L_val, S1, R_val): v,
                                    (p, L_val, S2, R_val): v,
                                }
                                total_attempts += 1
                                _, b_keys, had_b = enumerate_cycles_collect_b(
                                    ms, n, L_max, tb, pinned, 2)
                                pin_desc = (ms, p, L_val, R_val, S1, S2, v)
                                if had_b:
                                    all_attempts_b_keys.append((pin_desc, b_keys))
                                else:
                                    no_b_attempts.append(pin_desc)

    print(f"\n{'='*72}\nSummary ({time.time()-t_global:.0f}s)\n{'='*72}")
    print(f"  Total attempts: {total_attempts}")
    print(f"  Attempts with >=1 B-conflict: {len(all_attempts_b_keys)}")
    print(f"  Attempts with NO B-conflicts: {len(no_b_attempts)}")

    if no_b_attempts:
        print(f"\n  WARNING: {len(no_b_attempts)} attempts pruned without any B-conflict.")
        print("  These close by other means (A-conflict / E-no-close).")
        print("  B-conflict is NOT universally forced. First 3 such pins:")
        for d in no_b_attempts[:3]:
            print(f"    {d}")

    if all_attempts_b_keys:
        # Find intersection of B-keys across all attempts
        common = all_attempts_b_keys[0][1].copy()
        for _, keys in all_attempts_b_keys[1:]:
            common &= keys
        print(f"\n  B-keys appearing in ALL {len(all_attempts_b_keys)} B-positive attempts:")
        if common:
            for key in list(common)[:10]:
                print(f"    {key}")
        else:
            print("    (none — no universal B-conflict shape across all attempts)")

        # Distribution analysis
        all_keys = Counter()
        for _, keys in all_attempts_b_keys:
            for k in keys:
                all_keys[k] += 1
        print(f"\n  Top-10 B-keys by attempt-coverage:")
        for key, cnt in all_keys.most_common(10):
            pct = 100 * cnt / len(all_attempts_b_keys)
            print(f"    {key}: {cnt}/{len(all_attempts_b_keys)} ({pct:.0f}%)")

        # Structural pattern: is there always a B-key whose ki matches the pinned context?
        same_pos_hits = 0
        for (ms_, p_, L_, R_, S1_, S2_, v_), keys in all_attempts_b_keys:
            for (ki, pinned_v, needs_stay) in keys:
                if ki[0] == p_ and ki[1] == L_ and ki[3] == R_:
                    same_pos_hits += 1; break
        print(f"\n  Attempts with >=1 B-key at the SAME (p, L, R) as the pinned context:")
        print(f"    {same_pos_hits}/{len(all_attempts_b_keys)} "
              f"({100*same_pos_hits/len(all_attempts_b_keys):.0f}%)")

    print(f"\n{'='*72}")
    print("Interpretation")
    print(f"{'='*72}")
    if not no_b_attempts and all_attempts_b_keys:
        common = all_attempts_b_keys[0][1].copy()
        for _, keys in all_attempts_b_keys[1:]:
            common &= keys
        if common:
            print("  EVERY violator attempt produces B-conflicts AND they share")
            print("  at least one universal B-key.")
            print("  → Lean proof target: show that pinned-det forces that B-key.")
        else:
            print("  Every violator produces B-conflicts, but NO shared universal B-key.")
            print("  → Proof target must be existential: some B-conflict, not a fixed one.")
    elif no_b_attempts:
        print("  SOME violators prune without B-conflicts.")
        print("  → B-conflict mechanism is NOT universal; some cases use A-conflict.")
        print("  → Lean proof cannot rely solely on B-conflict; must handle A-only cases.")
