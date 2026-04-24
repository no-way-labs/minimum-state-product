#!/usr/bin/env python3
"""E14: A1'-violator probe at n=7 — confirm no-go at the regime where
R4 Read-2 hits its α_worst wall (n ≥ 8 binary-dominated).

Only a few multisets tested; full sweep would be expensive. Focus on
ternary-at-p cases to allow non-trivial A1' violations.
"""
from __future__ import annotations

import time
from itertools import product as iproduct


def enumerate_cycles(ms, n, L_max, tb, pinned, max_cycles):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []; seen = set(); t0 = time.time()

    def dfs(start, config, det, path, movers):
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
                    if ki in new_det and new_det[ki] != Si: ok = False; break
                    new_det[ki] = Si
                if not ok: continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if nc != start and nc in set(path): continue
                dfs(start, nc, new_det, path + [nc], movers + [p])

    for start in all_starts:
        if len(found) >= max_cycles or time.time()-t0 > tb: break
        dfs(start, start, dict(pinned), [start], [])
    return found


def audit(cyc, movers, n, p, L_val, R_val, S1, S2):
    L = len(movers); firings = []
    for k in range(L):
        if movers[k] != p: continue
        ck = cyc[k]
        if ck[(p-1)%n] == L_val and ck[(p+1)%n] == R_val:
            firings.append((k, ck[p]))
    s_vals = [s for _, s in firings]
    if S1 not in s_vals or S2 not in s_vals: return False
    targets = [(s, cyc[(k+1)%L][p]) for k, s in firings]
    t1 = [v for s, v in targets if s == S1]
    t2 = [v for s, v in targets if s == S2]
    return bool(t1) and bool(t2) and t1[0] == t2[0]


if __name__ == "__main__":
    print("=" * 72)
    print("E14: A1'-violator probe at n=7 (2026-04-20)")
    print("=" * 72)

    # Small ternary-rich subset at n=7. Full sweep too expensive.
    # Pick a few ms with m_p >= 3 at position 0 (allow nontrivial A1').
    trials = [
        (7, (3, 3, 3, 3, 3, 3, 3), 21, 8.0),
        (7, (3, 2, 3, 2, 3, 2, 3), 21, 8.0),
        (7, (3, 3, 2, 3, 2, 3, 3), 21, 8.0),
    ]

    total_attempts = 0; total_violators = 0
    t_global = time.time()

    for n, ms, L_max, tb in trials:
        print(f"\n--- n={n}, ms={ms} ---", flush=True)
        t_trial = time.time()
        attempts_trial = 0
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
                                total_attempts += 1; attempts_trial += 1
                                # Budget per trial: 120s total
                                if time.time() - t_trial > 120: break
                                cycles = enumerate_cycles(ms, n, L_max, tb, pinned, 2)
                                for cyc, movers, det in cycles:
                                    if len(movers) < 2*n: continue
                                    if audit(cyc, movers, n, p, L_val, R_val, S1, S2):
                                        total_violators += 1
                                        print(f"  VIOLATOR: p={p} (L,R)=({L_val},{R_val}) "
                                              f"S1={S1} S2={S2} v={v}", flush=True)
                            if time.time() - t_trial > 120: break
                        if time.time() - t_trial > 120: break
                    if time.time() - t_trial > 120: break
                if time.time() - t_trial > 120: break
            if time.time() - t_trial > 120: break
        print(f"  trial done: attempts={attempts_trial}  t={time.time()-t_trial:.0f}s", flush=True)

    print(f"\n{'='*72}")
    print(f"Summary ({time.time()-t_global:.0f}s)")
    print(f"{'='*72}")
    print(f"  Total attempts: {total_attempts}")
    print(f"  Violators: {total_violators}")
    if total_violators == 0:
        print("\n  VERDICT: A1' no-go extends to n=7 (on sampled trials).")
        print("  A1' universality hypothesis survives the regime where")
        print("  R4 Read-2 hit its α_worst wall.")
    else:
        print(f"\n  VERDICT: {total_violators} violators at n=7.")
        print("  A1' is NOT universal. Re-examine activation decision.")
