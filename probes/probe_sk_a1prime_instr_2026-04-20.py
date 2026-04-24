#!/usr/bin/env python3
"""E13: Instrumented A1'-violator probe.

Extends E12 by logging which specific axiom prunes each DFS branch
under pinned-det A1' violation.

Prune categories:
  A: firing-choice det conflict (at the would-be mover p)
  B: non-mover det conflict (other position i's context pinned inconsistent)
  C: Nodup violation (disabled if enforce_nodup=False)
  D: coverage failure at closure (not all of [n] are movers)
  E: no closure within L_max (implicit; counted as "no_close")

For each B event, record the conflicting (q, L, S, R, pinned_v, observed_v)
tuple. Dominant B-contexts point to which det-consistency check is
load-bearing for forcing A1'.
"""
from __future__ import annotations

import time
from collections import Counter
from itertools import product as iproduct


def enumerate_cycles_instr(ms, n, L_max, tb, pinned, max_cycles):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []; seen = set(); t0 = time.time()
    prune_counts = Counter()
    b_examples = []  # (conflicting_key, pinned_val, observed_val)

    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time()-t0 > tb: return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)):
                prune_counts['D_coverage'] += 1
                return
            L = len(movers)
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen:
                seen.add(norm); found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max:
            prune_counts['E_no_close'] += 1
            return
        for p in range(n):
            Lp = config[(p-1)%n]; Sp = config[p]; Rp = config[(p+1)%n]
            km = (p, Lp, Sp, Rp); forced_out = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp: continue
                if forced_out is not None and forced_out != new_val:
                    prune_counts['A_firing_conflict'] += 1
                    continue
                new_det = dict(det); new_det[km] = new_val; ok = True
                for i in range(n):
                    if i == p: continue
                    Li = config[(i-1)%n]; Si = config[i]; Ri = config[(i+1)%n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si:
                        prune_counts['B_nonmover_conflict'] += 1
                        if len(b_examples) < 20:
                            b_examples.append({
                                'ki': ki, 'pinned_v': new_det[ki], 'needs_stay': Si,
                                'depth': len(path),
                            })
                        ok = False; break
                    new_det[ki] = Si
                if not ok: continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if nc != start and nc in set(path):
                    prune_counts['C_nodup'] += 1; continue
                dfs(start, nc, new_det, path + [nc], movers + [p])

    for start in all_starts:
        if len(found) >= max_cycles or time.time()-t0 > tb: break
        dfs(start, start, dict(pinned), [start], [])
    return found, prune_counts, b_examples


if __name__ == "__main__":
    print("=" * 72)
    print("E13: Instrumented A1'-violator probe (2026-04-20)")
    print("=" * 72)

    # Minimum setup: n=5, ternary-at-0 multisets. Focus on a single violator
    # attempt to get clean per-prune-category counts.
    trials = [
        (5, (3, 3, 3, 3, 3), 15, 5.0),
        (5, (2, 3, 3, 3, 3), 15, 5.0),
    ]

    agg_prune = Counter()
    agg_b_by_pos = Counter()  # (i, L_val, S_val, R_val) key position distribution
    agg_b_conflicts = []  # full conflicts
    total_attempts = 0
    total_violators = 0
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
                                cycles, prunes, b_ex = enumerate_cycles_instr(
                                    ms, n, L_max, tb, pinned, 3)
                                agg_prune.update(prunes)
                                for e in b_ex:
                                    agg_b_by_pos[(e['ki'][0], e['ki'][1], e['ki'][2], e['ki'][3])] += 1
                                    if len(agg_b_conflicts) < 20:
                                        agg_b_conflicts.append(e)
                                if cycles:
                                    # Check for A1' violator among results
                                    for cyc, movers, det in cycles:
                                        if len(movers) < 2*n: continue
                                        # Quick A1' violator check
                                        firings = [(k, cyc[k][p]) for k in range(len(movers))
                                                   if movers[k] == p
                                                   and cyc[k][(p-1)%n] == L_val
                                                   and cyc[k][(p+1)%n] == R_val]
                                        if len(firings) >= 2:
                                            s_vals = [s for _, s in firings]
                                            if S1 in s_vals and S2 in s_vals:
                                                total_violators += 1

    print(f"\n{'='*72}\nSummary ({time.time()-t_global:.0f}s)\n{'='*72}")
    print(f"  Total pinned-det attempts: {total_attempts}")
    print(f"  A1' violators constructed: {total_violators}")

    print(f"\n  Prune category totals:")
    for cat, cnt in sorted(agg_prune.items(), key=lambda x: -x[1]):
        print(f"    {cat}: {cnt:,}")

    total_b = agg_prune.get('B_nonmover_conflict', 0)
    total_prune = sum(agg_prune.values())
    if total_prune > 0:
        print(f"\n  B (non-mover det conflict) share: "
              f"{100*total_b/total_prune:.1f}%  of all prunes")

    print(f"\n  Top B-conflict key positions (q, L, S, R):")
    for key, cnt in agg_b_by_pos.most_common(10):
        print(f"    {key}: {cnt} events")

    print(f"\n  Sample B-conflicts (first 5):")
    for e in agg_b_conflicts[:5]:
        print(f"    ki={e['ki']}  pinned_v={e['pinned_v']}  "
              f"needs_stay={e['needs_stay']}  depth={e['depth']}")

    print(f"\n{'='*72}\nInterpretation\n{'='*72}")
    if total_b / max(total_prune, 1) > 0.5:
        print("  DOMINANT PRUNE: B (non-mover det conflict).")
        print("  Load-bearing axiom: det-consistency at non-mover positions.")
        print("  Lean proof direction: show A1' violator pins det at some q ≠ p")
        print("  in a way that conflicts with required stay-values at q in")
        print("  other cycle configs.")
    elif agg_prune.get('A_firing_conflict', 0) / max(total_prune, 1) > 0.5:
        print("  DOMINANT PRUNE: A (firing-choice conflict at mover).")
        print("  Load-bearing axiom: det-consistency at the firing context.")
    elif agg_prune.get('E_no_close', 0) / max(total_prune, 1) > 0.5:
        print("  DOMINANT PRUNE: E (no closure within L_max).")
        print("  Load-bearing axiom: cycle closure. Need larger L_max to confirm.")
    else:
        print("  Prune distribution is spread. No single axiom dominates.")
