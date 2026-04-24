#!/usr/bin/env python3
"""(b) Forward-closure induction: track |π_p(S_k)| across peel steps.

For each peel step k, S_k = configs in VC_NG still alive after k peels.
S_0 = VC_NG, S_∞ = SK.

Questions:
  1. Does |π_p(S_k)| decrease monotonically?
  2. At what step k* does |π_p(S_k)| first drop below 2^(n-1)?
  3. Is there a position p for which |π_p(S_k)| never drops below 2^(n-1)?
  4. Which configs get peeled off each step, and do they have structure?

Key: we want to establish a FORWARD-CLOSURE argument.
  "∃p such that S_k ∪ C has |π_p(·)| ≥ 2^(n-1) at every k" would be a strong invariant.

The CORRECT target for Lemma C:
  "∃p such that S_k has |π_p(S_k)| ≥ 2^(n-1)" (no ∪C, since we want |SK| bound).
"""
from itertools import product as iproduct, combinations
from collections import defaultdict
import time, sys
sys.setrecursionlimit(100000)


def enumerate_cycles(ms, n, L_min, L_max, time_budget, max_cycles, start_limit=None):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    if start_limit: all_starts = all_starts[:start_limit]
    found = []; seen = set(); t0 = time.time()
    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget: return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)): return
            L = len(movers)
            if L < L_min: return
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen:
                seen.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max: return
        for p in range(n):
            Lp = config[(p - 1) % n]; Sp = config[p]; Rp = config[(p + 1) % n]
            km = (p, Lp, Sp, Rp); forced = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp: continue
                if forced is not None and forced != new_val: continue
                new_det = dict(det); new_det[km] = new_val; ok = True
                for i in range(n):
                    if i == p: continue
                    Li = config[(i - 1) % n]; Si = config[i]; Ri = config[(i + 1) % n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si: ok = False; break
                    new_det[ki] = Si
                if not ok: continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if nc != start and nc in set(path): continue
                dfs(start, nc, new_det, path + [nc], movers + [p])
    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget: break
        dfs(start, start, {}, [start], [])
    return found


def build_bounce_cycle(n):
    ms = tuple([2] + [3]*(n-2) + [2])
    up_down = list(range(n)) + list(range(n - 2, 0, -1))
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    movers = []
    full = up_down * 4
    for step, mover in enumerate(full):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            movers = full[:step + 1]
            break
        if nc in visited:
            raise RuntimeError(f"Cycle didn't close at n={n}")
        visited.add(nc)
        cycle.append(nc)
    det = {}
    for idx in range(len(cycle)):
        c = cycle[idx]; c_next = cycle[(idx + 1) % len(cycle)]
        mv = movers[idx]
        for p in range(n):
            L = c[(p - 1) % n]; S = c[p]; R = c[(p + 1) % n]
            key = (p, L, S, R)
            if p == mv: det[key] = c_next[p]
            else: det[key] = S
    return ms, cycle, det


def peel_trajectory(ms, n, cycle, det, bound):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n): V[i].add(c[i])
    V_sorted = [sorted(V[i]) for i in range(n)]
    all_configs = list(iproduct(*V_sorted))
    cycle_set = set(cycle)
    non_good = [c for c in all_configs if c not in cycle_set]
    ng_set = set(non_good)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    adj = defaultdict(list)
    for c in non_good:
        for p in range(n):
            Lp = c[(p - 1) % n]; Sp = c[p]; Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in move_entries:
                nc = list(c); nc[p] = move_entries[key]; nc = tuple(nc)
                if nc in ng_set: adj[c].append(nc)

    remaining = set(non_good)
    trajectory = []
    while True:
        # Record projection sizes of current S_k
        step_data = {'|S|': len(remaining)}
        for p in range(n):
            proj_s = {tuple(c[i] for i in range(n) if i != p) for c in remaining}
            step_data[f'proj{p}_S'] = len(proj_s)
            proj_suc = {tuple(c[i] for i in range(n) if i != p)
                        for c in remaining | cycle_set}
            step_data[f'proj{p}_SuC'] = len(proj_suc)
        trajectory.append(step_data)
        sinks = {c for c in remaining if not any(t in remaining for t in adj.get(c, []))}
        if not sinks: break
        remaining -= sinks

    return trajectory, len(remaining)


def main():
    print("=" * 100)
    print("PEEL TRAJECTORY — (b) forward-closure induction signal")
    print("=" * 100)
    cases = [
        (7, (2,2,2,3,3,3,3), 17, 35.0),
        (8, (2,2,2,3,3,3,3,3), 19, 50.0),
        (9, (2,2,3,2,3,3,3,3,3), 22, 40.0),
    ]
    for n, ms, L_max, tb in cases:
        bound = 2**(n-1)
        print(f"\n=== n={n} bound={bound} ms={ms} ===")
        t0 = time.time()
        cycles = enumerate_cycles(ms, n, L_min=2*n+2, L_max=L_max,
                                  time_budget=tb, max_cycles=1, start_limit=5)
        if not cycles:
            print(f"  no cycles found in {tb}s"); continue
        cycle, movers, det = cycles[0]
        print(f"  L={len(cycle)}  (DFS {time.time()-t0:.1f}s)")
        t0 = time.time()
        traj, sk_size = peel_trajectory(ms, n, cycle, det, bound)
        print(f"  |SK|={sk_size}  peel steps={len(traj)}  ({time.time()-t0:.1f}s)")
        print(f"  step  |S|    " + "  ".join(f"π{p}_S" for p in range(n)) + "    "
              + "  ".join(f"π{p}_SuC" for p in range(n)))
        for k, d in enumerate(traj):
            ps_s = [d[f'proj{p}_S'] for p in range(n)]
            ps_suc = [d[f'proj{p}_SuC'] for p in range(n)]
            marker_S = " " if max(ps_s) >= bound else "!"
            marker_SuC = " " if max(ps_suc) >= bound else "!"
            # Only print every few steps if many
            if k > 10 and k < len(traj) - 3: continue
            print(f"  k={k:2d} |S|={d['|S|']:5d}  " +
                  " ".join(f"{v:4d}" for v in ps_s) + marker_S + "  " +
                  " ".join(f"{v:4d}" for v in ps_suc) + marker_SuC)
        # Final step: check if (A) and (F) persist
        final = traj[-1]
        A_max = max(final[f'proj{p}_S'] for p in range(n))
        F_max = max(final[f'proj{p}_SuC'] for p in range(n))
        F_min = min(final[f'proj{p}_SuC'] for p in range(n))
        print(f"  FINAL: |S|={final['|S|']} (A) max π_p(S)={A_max}  "
              f"(F) π_p(SuC) min={F_min} max={F_max}")
        # Check monotonicity — for each p, min k at which π_p(S_k) drops below bound
        for p in range(n):
            ser = [d[f'proj{p}_S'] for d in traj]
            under = [k for k, v in enumerate(ser) if v < bound]
            first_under = under[0] if under else None
            suc_ser = [d[f'proj{p}_SuC'] for d in traj]
            suc_under = [k for k, v in enumerate(suc_ser) if v < bound]
            first_suc_under = suc_under[0] if suc_under else None
            # Only print a few
            if p < 3 or (first_under is not None and first_under < 3):
                print(f"  p={p} first k with π_p(S_k)<{bound}: {first_under};  "
                      f"first k with π_p(S_k∪C)<{bound}: {first_suc_under}  "
                      f"(final π_p(S)={ser[-1]}, π_p(SuC)={suc_ser[-1]})")


if __name__ == "__main__":
    main()
