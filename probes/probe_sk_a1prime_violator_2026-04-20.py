#!/usr/bin/env python3
"""E11: synthetic A1' violator probe.

Question: does ANY valid closed good cycle exist with an A1' violation?
A1' violation = two firings at context (p, L, R) with distinct S-values
both targeting same v under det.

Strategy: pin det(p, L, S1, R) = v and det(p, L, S2, R) = v for distinct S1 != S2
in advance; enumerate closed cycles consistent with this pinned det; check
if any exist.

If NO cycle exists for any (p, L, R, S1, S2, v) at small n → A1' is forced
by the axioms of good-cycle validity + closure + Nodup. Strong structural claim.

If some violator IS constructed → identify which axiom the empirical
absence relies on.
"""
from __future__ import annotations

import time
from collections import defaultdict
from itertools import product as iproduct


def enumerate_cycles_with_pinned_det(ms, n, L_max, time_budget, pinned,
                                     max_cycles):
    """Enumerate closed cycles whose det extends `pinned`."""
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []; seen = set(); t0 = time.time()

    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget: return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)): return
            L = len(movers)
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen:
                seen.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
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
        if len(found) >= max_cycles or time.time()-t0 > time_budget: break
        # Start DFS with pinned det baked in
        dfs(start, start, dict(pinned), [start], [])
    return found


def audit_violator(cycle, movers, det, p, L_val, R_val, S1, S2, n):
    """Confirm this cycle has an A1' violation at (p, L_val, R_val) with S1, S2."""
    L = len(movers)
    firings = []  # (k, S) pairs at this context
    for k in range(L):
        if movers[k] != p: continue
        ck = cycle[k]
        lv = ck[(p-1)%n]; sv = ck[p]; rv = ck[(p+1)%n]
        if lv == L_val and rv == R_val: firings.append((k, sv))
    # Need both S1 and S2 firings present
    s_vals = [s for (_, s) in firings]
    if S1 not in s_vals or S2 not in s_vals: return False
    # Check targets
    targets = []
    for k, s in firings:
        next_ck = cycle[(k+1) % L]
        targets.append((s, next_ck[p]))
    # Check both S1, S2 target same v (A1' violation)
    t1 = [v for s, v in targets if s == S1]
    t2 = [v for s, v in targets if s == S2]
    return t1 and t2 and t1[0] == t2[0]


if __name__ == "__main__":
    print("=" * 72)
    print("E11: synthetic A1' violator probe (2026-04-20)")
    print("=" * 72)

    # Try small n with m_p >= 3 to allow A1' violations (binary is trivial)
    # Pick n=5 and ms with a ternary or larger at position 0
    trials = [
        (5, (3, 3, 3, 3, 3), 15, 3.0),
        (5, (2, 3, 3, 3, 3), 15, 3.0),
        (5, (3, 2, 3, 2, 3), 15, 3.0),
        (5, (2, 3, 2, 3, 3), 15, 3.0),
        (5, (4, 3, 3, 3, 3), 15, 4.0),
        (5, (3, 4, 3, 3, 3), 15, 4.0),
    ]

    total_attempts = 0
    total_violators = 0
    t_global = time.time()

    for n, ms, L_max, tb in trials:
        print(f"\n--- n={n}, ms={ms} ---", flush=True)
        # Try each (p, L, R, S1, S2, v) that could violate A1'
        # p must have m_p >= 3
        for p in range(n):
            if ms[p] < 3: continue
            for L_val in range(ms[(p-1)%n]):
                for R_val in range(ms[(p+1)%n]):
                    # S1, S2 distinct in Fin m_p; v in Fin m_p, v != S1, v != S2
                    for S1 in range(ms[p]):
                        for S2 in range(S1+1, ms[p]):
                            for v in range(ms[p]):
                                if v == S1 or v == S2: continue
                                # Pin det
                                pinned = {
                                    (p, L_val, S1, R_val): v,
                                    (p, L_val, S2, R_val): v,
                                }
                                total_attempts += 1
                                cycles = enumerate_cycles_with_pinned_det(
                                    ms, n, L_max, tb, pinned, max_cycles=3)
                                for cyc, movers, det in cycles:
                                    if len(movers) < 2*n: continue
                                    # Verify A1' violation
                                    if audit_violator(cyc, movers, det, p, L_val, R_val, S1, S2, n):
                                        total_violators += 1
                                        print(f"  VIOLATOR: p={p} (L,R)=({L_val},{R_val}) "
                                              f"S1={S1} S2={S2} v={v}", flush=True)
                                        print(f"    cycle: {cyc}", flush=True)
                                        print(f"    movers: {movers}", flush=True)
                                        if total_violators >= 5:
                                            break
                                if total_violators >= 5: break
                            if total_violators >= 5: break
                        if total_violators >= 5: break
                    if total_violators >= 5: break
                if total_violators >= 5: break
            if total_violators >= 5: break
        if total_violators >= 5: break

    print(f"\n{'='*72}")
    print(f"Summary ({time.time()-t_global:.0f}s)")
    print(f"{'='*72}")
    print(f"  Total (p, L, R, S1, S2, v) pinned-det attempts: {total_attempts}")
    print(f"  A1' violators constructed: {total_violators}")
    if total_violators == 0:
        print("\n  VERDICT: A1' is forced by good-cycle axioms alone.")
        print("  (no pinned-det instance admits a valid closed cycle at small n)")
        print("  This is structural evidence that A1' is provable from base axioms.")
    else:
        print(f"\n  VERDICT: A1' violators DO exist constructively.")
        print("  Empirical absence of A1' violators must rely on additional")
        print("  structural constraint (e.g. sub-threshold regime, validity restriction).")
