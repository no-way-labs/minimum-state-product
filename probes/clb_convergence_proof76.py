#!/usr/bin/env python3
"""
CONVERGENCE PROOF 76: Why boundary (0,2,2,1) configs are dead ends
===================================================================
For the rank-3 bound proof: show that NO jdz excursion edge starts
from a config with boundary (P0=0, P1=2, P(n-2)=2, P(n-1)=1).

Analysis:
1. Which anomalous entries can fire at boundary (0,2,2,1)?
   Only mid(2,1,1)→0 (entries 1,2,4,5 blocked by boundary values)
2. For configs where mid CAN fire: does the excursion produce a jdz edge?
3. What specific mechanism prevents jdz edges?
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter

def delta_fc_val(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))

def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])

def int_21(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)

def int_j_20(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)

def int_j_21(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)

def int_20(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)

def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in range(5, 12):
        t0 = time.time()
        ms, fs = build_system(n_val)
        result = verify_system(ms, fs)
        assert result['valid']
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_list = [c for c in all_configs if c not in good_set]
        bad_set = set(bad_list)
        n = n_val

        # Find all bad configs with boundary (0,2,2,1)
        target_bdry = []
        for c in bad_list:
            if c[0] == 0 and c[1] == 2 and c[n-2] == 2 and c[n-1] == 1:
                target_bdry.append(c)

        if not target_bdry:
            print(f"n={n}: no bad configs with boundary (0,2,2,1)")
            continue

        print(f"\n{'=' * 70}", flush=True)
        print(f"n={n}: {len(target_bdry)} bad configs with boundary (0,2,2,1) ({time.time()-t0:.1f}s)", flush=True)

        # For each config, check if any anomalous entry can fire
        n_anom_source = 0
        n_has_mid_context = 0
        mid_fire_results = []

        # Build dfc_le0 adjacency and anomalous source info
        dfc_le0_adj = defaultdict(list)
        all_anom_sources = set()
        anom_info = {}

        for c in bad_list:
            for i in range(n):
                L = c[(i-1) % n]
                S = c[i]
                R = c[(i+1) % n]
                out = fs[i](L, S, R)
                if out != S:
                    lst = list(c)
                    lst[i] = out
                    succ = tuple(lst)
                    if succ in bad_set:
                        dfc = delta_fc_val(L, S, R, out)
                        if dfc <= 0:
                            dfc_le0_adj[c].append(succ)
                        if out != L and out != R:
                            all_anom_sources.add(c)
                            anom_info.setdefault(c, []).append((i, L, S, R, out, succ, dfc))

        for c in target_bdry:
            is_anom = c in all_anom_sources
            if is_anom:
                n_anom_source += 1

            # Check specifically for mid(2,1,1)→0 context
            has_mid = False
            for j in range(2, n - 2):
                if c[j-1] == 2 and c[j] == 1 and c[j+1] == 1:
                    # mid context at position j
                    out = fs[j](c[j-1], c[j], c[j+1])
                    if out == 0 and out != c[j-1] and out != c[j+1]:
                        has_mid = True
                        # Trace the excursion
                        lst = list(c)
                        lst[j] = 0
                        b = tuple(lst)
                        step_dfc = delta_fc_val(c[j-1], c[j], c[j+1], 0)

                        # BFS from b through dfc<=0 to find anomalous sources
                        visited = {b}
                        queue = [b]
                        head = 0
                        reached_anom = []
                        while head < len(queue):
                            node = queue[head]
                            head += 1
                            if node in all_anom_sources:
                                reached_anom.append(node)
                            for nxt in dfc_le0_adj.get(node, []):
                                if nxt not in visited:
                                    visited.add(nxt)
                                    queue.append(nxt)

                        # For each reached anomalous source v: check jdz invariants
                        jdz_valid = []
                        jdz_invalid_reasons = Counter()
                        for v in reached_anom:
                            d21 = int_21(v, n) - int_21(c, n)
                            dj20 = int_j_20(v, n) - int_j_20(c, n)
                            dj21 = int_j_21(v, n) - int_j_21(c, n)
                            d20 = int_20(v, n) - int_20(c, n)
                            dfc_edge = fc(v, n) - fc(c, n)

                            if d21 == 0 and dj20 == 0:
                                jdz_valid.append((v, dfc_edge, d21, dj20, dj21, d20))
                            else:
                                reasons = []
                                if d21 != 0:
                                    reasons.append(f"Δint21={d21}")
                                if dj20 != 0:
                                    reasons.append(f"Δintj20={dj20}")
                                jdz_invalid_reasons[tuple(reasons)] += 1

                        mid_fire_results.append({
                            'config': c,
                            'pos': j,
                            'step_dfc': step_dfc,
                            'reached_anom': len(reached_anom),
                            'visited': len(visited),
                            'jdz_valid': jdz_valid,
                            'jdz_invalid': jdz_invalid_reasons,
                        })

            if has_mid:
                n_has_mid_context += 1

        print(f"  Anomalous sources: {n_anom_source}/{len(target_bdry)}", flush=True)
        print(f"  Has mid(2,1,1) context: {n_has_mid_context}/{len(target_bdry)}", flush=True)

        # Summarize mid fire results
        total_mid_fires = len(mid_fire_results)
        total_jdz_valid = sum(len(r['jdz_valid']) for r in mid_fire_results)
        total_reached = sum(r['reached_anom'] for r in mid_fire_results)

        print(f"\n  Mid firings: {total_mid_fires}", flush=True)
        print(f"  Reached anomalous sources: {total_reached}", flush=True)
        print(f"  JDZ-valid edges: {total_jdz_valid}", flush=True)

        # Why are they jdz-invalid?
        all_reasons = Counter()
        for r in mid_fire_results:
            for reason, cnt in r['jdz_invalid'].items():
                all_reasons[reason] += cnt

        print(f"\n  JDZ-invalid reasons:", flush=True)
        for reason, cnt in all_reasons.most_common(10):
            print(f"    {' AND '.join(reason)}: {cnt}", flush=True)

        if total_jdz_valid > 0:
            print(f"\n  WARNING: {total_jdz_valid} JDZ-VALID EDGES from boundary (0,2,2,1)!", flush=True)
            for r in mid_fire_results:
                for v, dfc_edge, d21, dj20, dj21, d20 in r['jdz_valid']:
                    bdry_v = (v[0], v[1], v[n-2], v[n-1])
                    print(f"    {r['config']} → {v}", flush=True)
                    print(f"      mid at pos {r['pos']}, Δfc={dfc_edge}, bdry_v={bdry_v}", flush=True)
                    print(f"      Δint21={d21}, Δintj20={dj20}, Δintj21={dj21}, Δint20={d20}", flush=True)

        # Also check: are there configs with boundary (0,2,2,1) that have
        # anomalous entries OTHER than mid that can fire?
        other_entries = 0
        for c in target_bdry:
            if c in all_anom_sources:
                for pos, L, S, R, out, succ, dfc in anom_info.get(c, []):
                    if not (2 <= pos <= n-3):  # not mid
                        other_entries += 1
        print(f"\n  Non-mid anomalous entries at boundary (0,2,2,1): {other_entries}", flush=True)

        elapsed = time.time() - t0
        print(f"  Time: {elapsed:.1f}s", flush=True)

if __name__ == '__main__':
    main()
