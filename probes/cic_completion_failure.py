#!/usr/bin/env python3
"""CIC Exploration 8: Anatomy of completion failure at n=5.

At n=4 ms=(2,2,2,3), product=24 < 36: 15 valid sub-threshold systems exist.
At n=5 ms=(2,2,2,3,3), product=72 < 108: ZERO valid systems for ANY cycle type.

This script traces exactly WHY completion fails at n=5:
1. Find candidate non-sweep good cycles at n=5
2. Complete each cycle (good-targeting)
3. Identify which Dijkstra property fails
4. Trace the failure mechanism in detail
5. Compare with n=4 where completion succeeds
6. Identify the structural reason for the n=5 transition
"""

from itertools import product as iproduct
from collections import defaultdict, Counter
import sys
import os
import time
sys.path.insert(0, os.path.dirname(__file__))
from verifier import verify_system


def enumerate_good_cycles(ms, n, max_cycles=200, max_time=60.0):
    """Enumerate good cycles via DFS."""
    t0 = time.time()
    product_val = 1
    for m in ms:
        product_val *= m
    if product_val > 500:
        return []

    all_configs = list(iproduct(*[range(m) for m in ms]))
    cycles = []

    for start_idx in range(min(len(all_configs), product_val)):
        if time.time() - t0 > max_time:
            break
        start = all_configs[start_idx]
        stack = [(start, [start], {}, [])]
        nodes = 0
        while stack and nodes < 500000:
            if time.time() - t0 > max_time:
                break
            nodes += 1
            config, path, det, movers = stack.pop()
            for p in range(n):
                for new_val in range(ms[p]):
                    if new_val == config[p]:
                        continue
                    if movers:
                        last = movers[-1]
                        diff = min(abs(p - last), n - abs(p - last))
                        if diff > 1:
                            continue
                    new_det = dict(det)
                    consistent = True
                    L = config[(p - 1) % n]
                    S = config[p]
                    R = config[(p + 1) % n]
                    key_m = (p, L, S, R)
                    if key_m in new_det:
                        if new_det[key_m] != new_val:
                            consistent = False
                    else:
                        new_det[key_m] = new_val
                    if consistent:
                        for i in range(n):
                            if i == p:
                                continue
                            Li = config[(i - 1) % n]
                            Si = config[i]
                            Ri = config[(i + 1) % n]
                            key_i = (i, Li, Si, Ri)
                            if key_i in new_det:
                                if new_det[key_i] != Si:
                                    consistent = False
                                    break
                            else:
                                new_det[key_i] = Si
                    if not consistent:
                        continue
                    new_config = list(config)
                    new_config[p] = new_val
                    new_config = tuple(new_config)
                    if new_config == start and len(path) >= n:
                        me_ok = True
                        for idx in range(len(path)):
                            c = path[idx]
                            priv = []
                            for i in range(n):
                                Li = c[(i - 1) % n]
                                Si = c[i]
                                Ri = c[(i + 1) % n]
                                ki = (i, Li, Si, Ri)
                                if ki in new_det and new_det[ki] != Si:
                                    priv.append(i)
                            if len(priv) != 1:
                                me_ok = False
                                break
                        if me_ok:
                            cycle_tup = tuple(path)
                            if cycle_tup not in [tuple(c)
                                                  for c, _, _ in cycles]:
                                cycles.append((path, movers + [p], new_det))
                                if len(cycles) >= max_cycles:
                                    return cycles
                        continue
                    if new_config not in set(path) and len(path) < 5 * n:
                        stack.append((
                            new_config,
                            path + [new_config],
                            new_det,
                            movers + [p]
                        ))
    return cycles


def complete_system(cycle, movers, det, ms, n):
    """Complete a good cycle to a full system using good-targeting.
    Returns (fs_list, comp_dict) where fs_list is list of callables."""
    good_set = set(cycle)
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

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

    # Good-targeting completion
    comp = dict(det)
    for key in free_entries:
        p, L, S, R = key
        best_out = S  # default: identity (no privilege)
        best_good = 0
        best_ng = float('inf')
        for out in range(ms[p]):
            good_count = 0
            ng_count = 0
            for c in non_good:
                if (c[(p - 1) % n] == L and c[p] == S
                        and c[(p + 1) % n] == R):
                    new_c = list(c)
                    new_c[p] = out
                    nc = tuple(new_c)
                    if nc in good_set:
                        good_count += 1
                    elif nc in non_good_set:
                        ng_count += 1
            if out != S:
                if (good_count > best_good or
                        (good_count == best_good and ng_count < best_ng)):
                    best_out = out
                    best_good = good_count
                    best_ng = ng_count
        comp[key] = best_out

    # Build transition functions
    fs = []
    for p in range(n):
        t = {}
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    t[(L, S, R)] = comp.get((p, L, S, R), S)
        fs.append(lambda L, S, R, _t=t: _t.get((L, S, R), S))

    return fs, comp


def diagnose_failure(ms, fs, n, cycle, det):
    """Diagnose exactly which Dijkstra property fails and why."""
    all_configs = list(iproduct(*[range(m) for m in ms]))
    good_set = set(cycle)

    # Compute privilege for all configs
    priv_map = {}
    for c in all_configs:
        priv = []
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            if fs[i](L, S, R) != S:
                priv.append(i)
        priv_map[c] = priv

    result = {
        'liveness': True,
        'mutual_exclusion': True,
        'closure': True,
        'convergence': True,
        'fairness': True,
    }

    # 1. Liveness: every config has ≥1 privileged
    dead = [c for c in all_configs if len(priv_map[c]) == 0]
    if dead:
        result['liveness'] = False
        result['dead_configs'] = dead
        return result

    # 2. Mutual exclusion: good configs have exactly 1 privileged
    me_violations = [c for c in cycle if len(priv_map[c]) != 1]
    if me_violations:
        result['mutual_exclusion'] = False
        result['me_violations'] = me_violations
        return result

    # 3. Closure: moves from good -> good
    closure_violations = []
    for c in cycle:
        priv = priv_map[c]
        if len(priv) == 1:
            i = priv[0]
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            new_s = fs[i](L, S, R)
            new_c = list(c)
            new_c[i] = new_s
            new_c = tuple(new_c)
            if new_c not in good_set:
                closure_violations.append((c, i, new_c))
    if closure_violations:
        result['closure'] = False
        result['closure_violations'] = closure_violations
        return result

    # 4. Find the actual good set (closed under single-privilege successor)
    single_priv = {c for c in all_configs if len(priv_map[c]) == 1}
    succ = {}
    for c in single_priv:
        i = priv_map[c][0]
        L = c[(i - 1) % n]
        S = c[i]
        R = c[(i + 1) % n]
        new_s = fs[i](L, S, R)
        new_c = list(c)
        new_c[i] = new_s
        succ[c] = tuple(new_c)

    # Find maximal closed subset
    closed = set(single_priv)
    changed = True
    while changed:
        changed = False
        to_remove = set()
        for c in closed:
            if succ[c] not in closed:
                to_remove.add(c)
        if to_remove:
            closed -= to_remove
            changed = True

    # Find cycles in closed set
    visited = set()
    found_cycles = []
    for c in closed:
        if c in visited:
            continue
        path = []
        node = c
        path_set = set()
        while node not in visited and node not in path_set:
            path.append(node)
            path_set.add(node)
            node = succ[node]
        if node in path_set:
            cycle_start = path.index(node)
            found_cycle = path[cycle_start:]
            found_cycles.append(found_cycle)
        visited.update(path)

    result['single_priv_count'] = len(single_priv)
    result['closed_set_size'] = len(closed)
    result['found_cycle_count'] = len(found_cycles)
    if found_cycles:
        result['found_cycle_lengths'] = [len(fc) for fc in found_cycles]

    if not found_cycles:
        result['convergence'] = False
        result['convergence_detail'] = 'no cycle in closed single-priv set'
        return result

    # Check fairness for each found cycle
    fair_cycles = []
    for fc in found_cycles:
        procs_in_cycle = set()
        for c in fc:
            i = priv_map[c][0]
            procs_in_cycle.add(i)
        if procs_in_cycle == set(range(n)):
            fair_cycles.append(fc)

    if not fair_cycles:
        result['fairness'] = False
        result['fairness_detail'] = 'no cycle visits all processors'
        result['found_cycle_procs'] = [
            sorted(set(priv_map[c][0] for c in fc)) for fc in found_cycles
        ]
        return result

    # Check convergence for each fair cycle
    for fc in fair_cycles:
        fc_set = set(fc)
        # Build good set (cycle + tails)
        rev = defaultdict(list)
        for c in closed:
            rev[succ[c]].append(c)
        good = set(fc_set)
        queue = list(fc_set)
        while queue:
            node = queue.pop()
            for pred in rev[node]:
                if pred not in good:
                    good.add(pred)
                    queue.append(pred)

        bad = set(all_configs) - good

        # Check for bad cycles
        bad_succs = defaultdict(list)
        for c in bad:
            for i in priv_map[c]:
                new_c = list(c)
                L = c[(i - 1) % n]
                S = c[i]
                R = c[(i + 1) % n]
                new_c[i] = fs[i](L, S, R)
                nc = tuple(new_c)
                if nc in bad:
                    bad_succs[c].append(nc)

        # Find SCCs in bad graph
        color = {c: 0 for c in bad}
        has_bad_cycle = False
        bad_cycle_configs = []
        for start in bad:
            if color[start] != 0:
                continue
            stack = [(start, False)]
            while stack:
                node, returning = stack.pop()
                if returning:
                    color[node] = 2
                    continue
                if color[node] == 1:
                    color[node] = 2
                    continue
                if color[node] == 2:
                    continue
                color[node] = 1
                stack.append((node, True))
                for s in bad_succs[node]:
                    if color[s] == 1:
                        has_bad_cycle = True
                        bad_cycle_configs.append(s)
                    if color[s] == 0:
                        stack.append((s, False))

        if has_bad_cycle:
            result['convergence'] = False
            result['convergence_detail'] = 'bad cycle exists'
            result['bad_count'] = len(bad)
            result['good_count'] = len(good)
            result['bad_cycle_sample'] = bad_cycle_configs[:5]

            # Find actual bad SCC via Tarjan
            idx_counter = [0]
            tarjan_stack = []
            on_stack = set()
            lowlink = {}
            index = {}
            sccs = []

            def strongconnect(v):
                index[v] = idx_counter[0]
                lowlink[v] = idx_counter[0]
                idx_counter[0] += 1
                tarjan_stack.append(v)
                on_stack.add(v)
                for w in bad_succs.get(v, []):
                    if w not in index:
                        strongconnect(w)
                        lowlink[v] = min(lowlink[v], lowlink[w])
                    elif w in on_stack:
                        lowlink[v] = min(lowlink[v], index[w])
                if lowlink[v] == index[v]:
                    scc = []
                    while True:
                        w = tarjan_stack.pop()
                        on_stack.discard(w)
                        scc.append(w)
                        if w == v:
                            break
                    if len(scc) > 1:
                        sccs.append(scc)

            sys.setrecursionlimit(10000)
            for v in bad:
                if v not in index:
                    strongconnect(v)

            result['bad_sccs'] = len(sccs)
            result['bad_scc_sizes'] = sorted([len(s) for s in sccs],
                                              reverse=True)[:10]

            # Analyze what transitions create the bad cycle
            if sccs:
                scc = sccs[0]  # largest SCC
                scc_set = set(scc)
                # Which transitions keep configs in the SCC?
                scc_transitions = []
                for c in scc:
                    for i in priv_map[c]:
                        new_c = list(c)
                        L = c[(i - 1) % n]
                        S = c[i]
                        R = c[(i + 1) % n]
                        new_c[i] = fs[i](L, S, R)
                        nc = tuple(new_c)
                        if nc in scc_set:
                            entry_key = (i, L, S, R)
                            is_det = entry_key in det
                            scc_transitions.append(
                                (c, i, nc, is_det, entry_key,
                                 fs[i](L, S, R)))
                result['scc_transitions_sample'] = scc_transitions[:20]

                # Key: how many SCC-internal transitions come from
                # DETERMINED vs FREE entries?
                det_count = sum(1 for _, _, _, is_det, _, _ in scc_transitions
                                if is_det)
                free_count = sum(1 for _, _, _, is_det, _, _ in scc_transitions
                                 if not is_det)
                result['scc_det_transitions'] = det_count
                result['scc_free_transitions'] = free_count

            return result

    # All properties hold
    result['valid'] = True
    return result


def analyze_entry_structure(cycle, movers, det, ms, n):
    """Analyze the structure of determined vs free entries."""
    total_entries = 0
    det_entries = 0
    free_entries = 0
    mover_entries = 0
    nonmover_entries = 0

    for p in range(n):
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    total_entries += 1
                    key = (p, L, S, R)
                    if key in det:
                        det_entries += 1
                        if det[key] != S:
                            mover_entries += 1
                        else:
                            nonmover_entries += 1
                    else:
                        free_entries += 1

    # Per-processor breakdown
    proc_info = []
    for p in range(n):
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        p_total = m_L * m_S * m_R
        p_det = 0
        p_mover = 0
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    if key in det:
                        p_det += 1
                        if det[key] != S:
                            p_mover += 1
        proc_info.append({
            'proc': p,
            'ms': ms[p],
            'total': p_total,
            'det': p_det,
            'mover': p_mover,
            'free': p_total - p_det,
            'det_pct': 100 * p_det / p_total,
        })

    return {
        'total': total_entries,
        'determined': det_entries,
        'free': free_entries,
        'mover': mover_entries,
        'nonmover': nonmover_entries,
        'det_pct': 100 * det_entries / total_entries,
        'proc_info': proc_info,
    }


# ============================================================
# PART 1: Compare n=4 (succeeds) vs n=5 (fails)
# ============================================================
print("=" * 70)
print("PART 1: COMPLETION FAILURE ANATOMY — n=4 vs n=5")
print("=" * 70)

# n=4: ms=(2,2,2,3), product=24 < 36
n4 = 4
ms4 = (2, 2, 2, 3)
print(f"\n--- n=4, ms={list(ms4)}, product=24, threshold=36 ---")

cycles4 = enumerate_good_cycles(ms4, n4, max_cycles=20, max_time=30.0)
print(f"Found {len(cycles4)} candidate cycles")

valid4 = 0
for idx, (cycle, movers, det) in enumerate(cycles4[:5]):
    fs, comp = complete_system(cycle, movers, det, ms4, n4)
    result = verify_system(ms4, fs)
    is_valid = result.get('valid', False)
    if is_valid:
        valid4 += 1

    if idx < 3:
        diag = diagnose_failure(ms4, fs, n4, cycle, det)
        entry_info = analyze_entry_structure(cycle, movers, det, ms4, n4)

        print(f"\n  Cycle {idx}: L={len(cycle)}, movers={movers}")
        print(f"    Entries: {entry_info['determined']}/{entry_info['total']} "
              f"det ({entry_info['det_pct']:.0f}%), "
              f"{entry_info['mover']} mover, "
              f"{entry_info['nonmover']} nonmover, "
              f"{entry_info['free']} free")
        print(f"    Valid: {is_valid}")
        if not is_valid:
            for prop in ['liveness', 'mutual_exclusion', 'closure',
                         'convergence', 'fairness']:
                if not diag.get(prop, True):
                    print(f"    FAILS: {prop}")
                    if prop == 'convergence':
                        print(f"      Detail: {diag.get('convergence_detail', '?')}")
                        print(f"      Good: {diag.get('good_count', '?')}, "
                              f"Bad: {diag.get('bad_count', '?')}")
                        print(f"      Bad SCCs: {diag.get('bad_sccs', '?')}, "
                              f"sizes: {diag.get('bad_scc_sizes', [])}")
                        if 'scc_det_transitions' in diag:
                            print(f"      SCC transitions: "
                                  f"{diag['scc_det_transitions']} det, "
                                  f"{diag['scc_free_transitions']} free")
                    elif prop == 'fairness':
                        print(f"      Detail: {diag.get('fairness_detail', '?')}")
                        print(f"      Cycle procs: "
                              f"{diag.get('found_cycle_procs', [])}")
                    break

print(f"\n  n=4 valid: {valid4}/{min(len(cycles4), 5)}")

# n=5: ms=(2,2,2,3,3), product=72 < 108
n5 = 5
ms5 = (2, 2, 2, 3, 3)
print(f"\n--- n=5, ms={list(ms5)}, product=72, threshold=108 ---")

cycles5 = enumerate_good_cycles(ms5, n5, max_cycles=20, max_time=60.0)
print(f"Found {len(cycles5)} candidate cycles")

for idx, (cycle, movers, det) in enumerate(cycles5[:5]):
    fs, comp = complete_system(cycle, movers, det, ms5, n5)
    result = verify_system(ms5, fs)
    is_valid = result.get('valid', False)

    diag = diagnose_failure(ms5, fs, n5, cycle, det)
    entry_info = analyze_entry_structure(cycle, movers, det, ms5, n5)

    print(f"\n  Cycle {idx}: L={len(cycle)}, movers={movers}")
    print(f"    Entries: {entry_info['determined']}/{entry_info['total']} "
          f"det ({entry_info['det_pct']:.0f}%), "
          f"{entry_info['mover']} mover, "
          f"{entry_info['nonmover']} nonmover, "
          f"{entry_info['free']} free")
    print(f"    Valid: {is_valid}")

    for prop in ['liveness', 'mutual_exclusion', 'closure',
                 'convergence', 'fairness']:
        if not diag.get(prop, True):
            print(f"    FAILS: {prop}")
            if prop == 'convergence':
                print(f"      Detail: {diag.get('convergence_detail', '?')}")
                print(f"      Good: {diag.get('good_count', '?')}, "
                      f"Bad: {diag.get('bad_count', '?')}")
                print(f"      Bad SCCs: {diag.get('bad_sccs', '?')}, "
                      f"sizes: {diag.get('bad_scc_sizes', [])}")
                if 'scc_det_transitions' in diag:
                    print(f"      SCC transitions: "
                          f"{diag['scc_det_transitions']} det, "
                          f"{diag['scc_free_transitions']} free")
                    # Show sample transitions
                    for t in diag.get('scc_transitions_sample', [])[:5]:
                        c, i, nc, is_det, key, out = t
                        src = "DET" if is_det else "FREE"
                        print(f"        P{i} at {c} → {nc} [{src}: "
                              f"({key[1]},{key[2]},{key[3]})→{out}]")
            elif prop == 'fairness':
                print(f"      Detail: {diag.get('fairness_detail', '?')}")
                print(f"      Cycle procs: "
                      f"{diag.get('found_cycle_procs', [])}")
            elif prop == 'liveness':
                if 'dead_configs' in diag:
                    print(f"      Dead configs: {diag['dead_configs'][:5]}")
            break

    # Per-processor entry detail
    if idx < 2:
        print(f"    Per-proc entries:")
        for pi in entry_info['proc_info']:
            print(f"      P{pi['proc']} (m={pi['ms']}): "
                  f"{pi['det']}/{pi['total']} det "
                  f"({pi['det_pct']:.0f}%), "
                  f"{pi['mover']} mover, {pi['free']} free")


# ============================================================
# PART 2: Deep dive into n=5 failure mechanism
# ============================================================
print(f"\n{'=' * 70}")
print("PART 2: DEEP DIVE — WHY DOES CONVERGENCE FAIL AT n=5?")
print("=" * 70)

# Take the first n=5 cycle and analyze the bad SCC in detail
if cycles5:
    cycle, movers, det = cycles5[0]
    fs, comp = complete_system(cycle, movers, det, ms5, n5)
    good_set = set(cycle)
    all_configs = list(iproduct(*[range(m) for m in ms5]))

    # Compute full privilege map
    priv_map = {}
    for c in all_configs:
        priv = []
        for i in range(n5):
            L = c[(i - 1) % n5]
            S = c[i]
            R = c[(i + 1) % n5]
            if fs[i](L, S, R) != S:
                priv.append(i)
        priv_map[c] = priv

    # Find single-priv configs
    single_priv = {c for c in all_configs if len(priv_map[c]) == 1}
    print(f"\n  Total configs: {len(all_configs)}")
    print(f"  Good cycle configs: {len(cycle)}")
    print(f"  Single-priv configs: {len(single_priv)}")
    print(f"  Multi-priv configs: "
          f"{sum(1 for c in all_configs if len(priv_map[c]) > 1)}")

    # Privilege distribution
    priv_dist = Counter(len(priv_map[c]) for c in all_configs)
    print(f"  Privilege distribution: "
          f"{dict(sorted(priv_dist.items()))}")

    # Find non-good configs with transitions that stay non-good
    non_good = [c for c in all_configs if c not in good_set]
    stuck_count = 0
    can_reach_good = 0
    for c in non_good:
        priv = priv_map[c]
        all_stay_non_good = True
        for i in priv:
            L = c[(i - 1) % n5]
            S = c[i]
            R = c[(i + 1) % n5]
            new_s = fs[i](L, S, R)
            new_c = list(c)
            new_c[i] = new_s
            nc = tuple(new_c)
            if nc in good_set or nc in single_priv:
                all_stay_non_good = False
        if all_stay_non_good:
            stuck_count += 1
        else:
            can_reach_good += 1

    print(f"\n  Non-good configs: {len(non_good)}")
    print(f"    All transitions stay non-good: {stuck_count}")
    print(f"    Some transition reaches good/single-priv: {can_reach_good}")

    # Analyze which entries cause the bad SCC
    # Build bad graph
    bad_set = set(non_good)
    bad_succs = defaultdict(list)
    bad_edge_info = defaultdict(list)
    for c in non_good:
        for i in priv_map[c]:
            L = c[(i - 1) % n5]
            S = c[i]
            R = c[(i + 1) % n5]
            new_s = fs[i](L, S, R)
            new_c = list(c)
            new_c[i] = new_s
            nc = tuple(new_c)
            if nc in bad_set:
                bad_succs[c].append(nc)
                key = (i, L, S, R)
                bad_edge_info[c].append((nc, i, key, key in det))

    # Tarjan's SCC
    idx_counter = [0]
    tarjan_stack = []
    on_stack = set()
    lowlink = {}
    index_map = {}
    sccs = []

    def strongconnect(v):
        index_map[v] = idx_counter[0]
        lowlink[v] = idx_counter[0]
        idx_counter[0] += 1
        tarjan_stack.append(v)
        on_stack.add(v)
        for w in bad_succs.get(v, []):
            if w not in index_map:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], index_map[w])
        if lowlink[v] == index_map[v]:
            scc = []
            while True:
                w = tarjan_stack.pop()
                on_stack.discard(w)
                scc.append(w)
                if w == v:
                    break
            if len(scc) > 1:
                sccs.append(scc)

    sys.setrecursionlimit(10000)
    for v in non_good:
        if v not in index_map:
            strongconnect(v)

    print(f"\n  Bad SCCs: {len(sccs)}")
    for si, scc in enumerate(sorted(sccs, key=len, reverse=True)[:5]):
        print(f"    SCC {si}: size {len(scc)}")
        scc_set = set(scc)
        # Count internal edges by det/free
        det_edges = 0
        free_edges = 0
        for c in scc:
            for nc, i, key, is_det in bad_edge_info[c]:
                if nc in scc_set:
                    if is_det:
                        det_edges += 1
                    else:
                        free_edges += 1
        print(f"      Internal edges: {det_edges} det, {free_edges} free")

        # Which processors move in SCC transitions?
        proc_moves = Counter()
        for c in scc:
            for nc, i, key, is_det in bad_edge_info[c]:
                if nc in scc_set:
                    proc_moves[i] += 1
        print(f"      Proc moves: {dict(sorted(proc_moves.items()))}")

        # Show sample configs and transitions
        if si == 0:
            print(f"      Sample configs:")
            for c in list(scc)[:8]:
                priv = priv_map[c]
                edges = []
                for nc, i, key, is_det in bad_edge_info[c]:
                    if nc in scc_set:
                        edges.append(
                            f"P{i}{'(D)' if is_det else '(F)'}→{nc}")
                print(f"        {c} priv={priv} → "
                      f"{'; '.join(edges[:3])}")


# ============================================================
# PART 3: State space ratio analysis
# ============================================================
print(f"\n{'=' * 70}")
print("PART 3: STATE SPACE RATIO — good/total vs n")
print("=" * 70)

print("\nFor sub-threshold ms=(2,2,2,3,...,3):")
for n_test in range(4, 8):
    ms_test = tuple([2, 2, 2] + [3] * (n_test - 3))
    prod = 1
    for m in ms_test:
        prod *= m
    threshold = 4 * (3 ** (n_test - 2))
    # Minimum good cycle length for adjacent-mover walk visiting all procs
    # Each binary fires ≥2, each ternary fires ≥2 → min length ≥ 2n
    # Typically 3n-2 for bounce, 2n for sweep
    min_good = 2 * n_test  # sweep minimum
    typical_good = 3 * n_test - 2  # bounce
    ratio_min = min_good / prod * 100
    ratio_typ = typical_good / prod * 100
    print(f"  n={n_test}: ms={list(ms_test)}, prod={prod}, "
          f"threshold={threshold}")
    print(f"    Min good cycle: {min_good} ({ratio_min:.1f}% of configs)")
    print(f"    Bounce cycle: {typical_good} ({ratio_typ:.1f}% of configs)")
    print(f"    Non-good configs: {prod - min_good}..{prod - typical_good}")


# ============================================================
# PART 4: Binary context exhaustion analysis
# ============================================================
print(f"\n{'=' * 70}")
print("PART 4: BINARY CONTEXT EXHAUSTION AT n=5")
print("=" * 70)

if cycles5:
    cycle, movers, det = cycles5[0]
    n = n5
    ms = ms5

    # For each binary processor, how many (L,R) contexts exist?
    # How many are used as mover entries? How many as nonmover?
    for p in range(n):
        if ms[p] != 2:
            continue
        m_L = ms[(p - 1) % n]
        m_R = ms[(p + 1) % n]
        total_contexts = m_L * m_R

        # Categorize each (L,R) context
        mover_0 = set()  # (L,R) where f(L,0,R) ≠ 0
        mover_1 = set()  # (L,R) where f(L,1,R) ≠ 1
        nonmover_0 = set()  # (L,R) where f(L,0,R) = 0
        nonmover_1 = set()  # (L,R) where f(L,1,R) = 1

        for L in range(m_L):
            for R in range(m_R):
                key0 = (p, L, 0, R)
                key1 = (p, L, 1, R)
                if key0 in det:
                    if det[key0] != 0:
                        mover_0.add((L, R))
                    else:
                        nonmover_0.add((L, R))
                if key1 in det:
                    if det[key1] != 1:
                        mover_1.add((L, R))
                    else:
                        nonmover_1.add((L, R))

        # Check No Binary 2-Cycle
        two_cycle = mover_0 & mover_1
        up_only = mover_0 - mover_1  # 0→1 but NOT 1→0
        down_only = mover_1 - mover_0  # 1→0 but NOT 0→1

        print(f"\n  P{p} (binary, m_L={m_L}, m_R={m_R}): "
              f"{total_contexts} (L,R) contexts")
        print(f"    State 0: {len(mover_0)} mover, {len(nonmover_0)} nonmover, "
              f"{total_contexts - len(mover_0) - len(nonmover_0)} free")
        print(f"    State 1: {len(mover_1)} mover, {len(nonmover_1)} nonmover, "
              f"{total_contexts - len(mover_1) - len(nonmover_1)} free")
        print(f"    UP (0→1): {up_only}")
        print(f"    DOWN (1→0): {down_only}")
        print(f"    2-CYCLE (both): {two_cycle}")
        if two_cycle:
            print(f"    *** BINARY 2-CYCLE VIOLATION! ***")

    # Also check ternary processors
    for p in range(n):
        if ms[p] != 3:
            continue
        m_L = ms[(p - 1) % n]
        m_R = ms[(p + 1) % n]
        total_contexts = m_L * m_R

        # Count determined entries per state
        det_by_state = {0: 0, 1: 0, 2: 0}
        mover_by_state = {0: 0, 1: 0, 2: 0}
        for L in range(m_L):
            for S in range(3):
                for R in range(m_R):
                    key = (p, L, S, R)
                    if key in det:
                        det_by_state[S] += 1
                        if det[key] != S:
                            mover_by_state[S] += 1

        print(f"\n  P{p} (ternary, m_L={m_L}, m_R={m_R}): "
              f"{total_contexts} (L,R) contexts per state")
        for S in range(3):
            total_for_state = total_contexts
            print(f"    State {S}: {det_by_state[S]}/{total_for_state} det, "
                  f"{mover_by_state[S]} mover")


# ============================================================
# PART 5: Alternative completion strategies
# ============================================================
print(f"\n{'=' * 70}")
print("PART 5: ALTERNATIVE COMPLETIONS AT n=5")
print("=" * 70)

def complete_identity(cycle, movers, det, ms, n):
    """Complete with identity (no privilege) for all free entries."""
    comp = dict(det)
    for p in range(n):
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    if key not in comp:
                        comp[key] = S  # identity
    fs = []
    for p in range(n):
        t = {}
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    t[(L, S, R)] = comp.get((p, L, S, R), S)
        fs.append(lambda L, S, R, _t=t: _t.get((L, S, R), S))
    return fs, comp


def complete_random(cycle, movers, det, ms, n, seed=42):
    """Complete with random non-identity assignments."""
    import random
    rng = random.Random(seed)
    comp = dict(det)
    for p in range(n):
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    if key not in comp:
                        # 50% chance of non-identity
                        if rng.random() < 0.5:
                            choices = [v for v in range(ms[p]) if v != S]
                            if choices:
                                comp[key] = rng.choice(choices)
                            else:
                                comp[key] = S
                        else:
                            comp[key] = S
    fs = []
    for p in range(n):
        t = {}
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    t[(L, S, R)] = comp.get((p, L, S, R), S)
        fs.append(lambda L, S, R, _t=t: _t.get((L, S, R), S))
    return fs, comp


if cycles5:
    cycle, movers, det = cycles5[0]

    strategies = [
        ("good-targeting", lambda c, m, d, ms, n:
         complete_system(c, m, d, ms, n)),
        ("identity", lambda c, m, d, ms, n:
         complete_identity(c, m, d, ms, n)),
    ]
    # Add random strategies
    for seed in range(10):
        strategies.append(
            (f"random-{seed}",
             lambda c, m, d, ms, n, s=seed:
             complete_random(c, m, d, ms, n, seed=s)))

    print(f"\n  Testing {len(strategies)} completion strategies on cycle 0:")
    for name, strategy in strategies:
        fs, comp = strategy(cycle, movers, det, ms5, n5)
        result = verify_system(ms5, fs)
        is_valid = result.get('valid', False)
        if is_valid:
            print(f"    {name}: VALID *** !")
        else:
            # Quick failure diagnosis
            diag = diagnose_failure(ms5, fs, n5, cycle, det)
            fail_prop = 'unknown'
            for prop in ['liveness', 'mutual_exclusion', 'closure',
                         'convergence', 'fairness']:
                if not diag.get(prop, True):
                    fail_prop = prop
                    break
            extra = ""
            if fail_prop == 'convergence':
                extra = f" (SCCs: {diag.get('bad_sccs', '?')})"
            elif fail_prop == 'liveness':
                extra = f" ({len(diag.get('dead_configs', []))} dead)"
            print(f"    {name}: INVALID — {fail_prop}{extra}")


# ============================================================
# PART 6: n=4 vs n=5 structural comparison
# ============================================================
print(f"\n{'=' * 70}")
print("PART 6: STRUCTURAL COMPARISON — WHY n=4 WORKS, n=5 DOESN'T")
print("=" * 70)

# Find a VALID n=4 cycle and compare its structure with n=5
if cycles4:
    for idx, (cycle4, movers4, det4) in enumerate(cycles4):
        fs4, comp4 = complete_system(cycle4, movers4, det4, ms4, n4)
        result4 = verify_system(ms4, fs4)
        if result4.get('valid', False):
            print(f"\n  VALID n=4 cycle {idx}: L={len(cycle4)}")
            print(f"    Movers: {movers4}")

            entry4 = analyze_entry_structure(cycle4, movers4, det4, ms4, n4)
            print(f"    Entries: {entry4['determined']}/{entry4['total']} det "
                  f"({entry4['det_pct']:.0f}%), "
                  f"{entry4['free']} free")

            all4 = list(iproduct(*[range(m) for m in ms4]))
            good4 = result4.get('good_configs', set())
            bad4 = set(all4) - good4
            print(f"    Good configs: {len(good4)}/{len(all4)} "
                  f"({100*len(good4)/len(all4):.1f}%)")
            print(f"    Bad configs: {len(bad4)} "
                  f"({100*len(bad4)/len(all4):.1f}%)")

            # Count transitions from bad that reach good
            priv_map4 = {}
            for c in all4:
                priv = []
                for i in range(n4):
                    L = c[(i - 1) % n4]
                    S = c[i]
                    R = c[(i + 1) % n4]
                    if fs4[i](L, S, R) != S:
                        priv.append(i)
                priv_map4[c] = priv

            reaches_good = 0
            for c in bad4:
                for i in priv_map4[c]:
                    L = c[(i - 1) % n4]
                    S = c[i]
                    R = c[(i + 1) % n4]
                    new_c = list(c)
                    new_c[i] = fs4[i](L, S, R)
                    nc = tuple(new_c)
                    if nc in good4:
                        reaches_good += 1
                        break
            print(f"    Bad configs with ≥1 transition to good: "
                  f"{reaches_good}/{len(bad4)} "
                  f"({100*reaches_good/len(bad4):.1f}%)")

            break

if cycles5:
    cycle5, movers5, det5 = cycles5[0]
    entry5 = analyze_entry_structure(cycle5, movers5, det5, ms5, n5)
    print(f"\n  INVALID n=5 cycle 0: L={len(cycle5)}")
    print(f"    Movers: {movers5}")
    print(f"    Entries: {entry5['determined']}/{entry5['total']} det "
          f"({entry5['det_pct']:.0f}%), "
          f"{entry5['free']} free")

    all5 = list(iproduct(*[range(m) for m in ms5]))
    good5 = set(cycle5)
    bad5 = set(all5) - good5
    print(f"    Good cycle configs: {len(good5)}/{len(all5)} "
          f"({100*len(good5)/len(all5):.1f}%)")
    print(f"    Bad configs: {len(bad5)} "
          f"({100*len(bad5)/len(all5):.1f}%)")


# ============================================================
# PART 7: Exhaustive completion search at n=5
# ============================================================
print(f"\n{'=' * 70}")
print("PART 7: EXHAUSTIVE COMPLETION SEARCH FOR n=5 CYCLE 0")
print("=" * 70)

if cycles5:
    cycle, movers, det = cycles5[0]
    n = n5
    ms = ms5

    # Count free entries
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
                        free_entries.append((key, ms[p]))

    total_free = len(free_entries)
    total_combinations = 1
    for _, m in free_entries:
        total_combinations *= m
    print(f"\n  Free entries: {total_free}")
    print(f"  Total combinations: {total_combinations}")

    if total_combinations <= 500000:
        print(f"  Exhaustive search feasible — trying all completions...")
        valid_found = 0
        t0 = time.time()

        # Generate all completions
        free_keys = [k for k, _ in free_entries]
        free_ranges = [range(m) for _, m in free_entries]

        tested = 0
        for values in iproduct(*free_ranges):
            tested += 1
            if tested % 50000 == 0:
                elapsed = time.time() - t0
                print(f"    Tested {tested}/{total_combinations} "
                      f"({elapsed:.1f}s)...")

            comp = dict(det)
            for key, val in zip(free_keys, values):
                comp[key] = val

            # Build fs
            fs = []
            for p in range(n):
                t = {}
                m_L = ms[(p - 1) % n]
                m_S = ms[p]
                m_R = ms[(p + 1) % n]
                for L in range(m_L):
                    for S in range(m_S):
                        for R in range(m_R):
                            t[(L, S, R)] = comp.get((p, L, S, R), S)
                fs.append(lambda L, S, R, _t=t: _t.get((L, S, R), S))

            result = verify_system(ms, fs)
            if result.get('valid', False):
                valid_found += 1
                print(f"    FOUND VALID COMPLETION!")
                # Show the free entry values
                for key, val in zip(free_keys, values):
                    if val != key[2]:  # non-identity
                        print(f"      {key} → {val}")
                if valid_found >= 3:
                    break

        elapsed = time.time() - t0
        print(f"\n  Exhaustive search: {valid_found} valid out of "
              f"{tested} tested ({elapsed:.1f}s)")
        if valid_found == 0:
            print(f"  *** NO VALID COMPLETION EXISTS for this cycle ***")
            print(f"  This is a PROOF that this particular cycle cannot")
            print(f"  be the good cycle of ANY valid system.")
    else:
        print(f"  Too many combinations for exhaustive search")
        print(f"  Using sampling instead...")
        import random
        rng = random.Random(42)
        valid_found = 0
        tested = 0
        t0 = time.time()

        for _ in range(100000):
            tested += 1
            comp = dict(det)
            for key, m in free_entries:
                comp[key] = rng.randrange(m)

            fs = []
            for p in range(n):
                t = {}
                m_L = ms[(p - 1) % n]
                m_S = ms[p]
                m_R = ms[(p + 1) % n]
                for L in range(m_L):
                    for S in range(m_S):
                        for R in range(m_R):
                            t[(L, S, R)] = comp.get((p, L, S, R), S)
                fs.append(lambda L, S, R, _t=t: _t.get((L, S, R), S))

            result = verify_system(ms, fs)
            if result.get('valid', False):
                valid_found += 1
                print(f"    FOUND VALID COMPLETION at attempt {tested}!")
                break

        elapsed = time.time() - t0
        print(f"\n  Sampled {tested} completions: {valid_found} valid "
              f"({elapsed:.1f}s)")


# ============================================================
# Summary
# ============================================================
print(f"\n{'=' * 70}")
print("SUMMARY: COMPLETION FAILURE MECHANISM")
print("=" * 70)
print("""
Tracing the anatomy of completion failure at n=5 vs n=4:

KEY QUESTIONS:
1. Which property fails? (liveness / ME / closure / convergence / fairness)
2. If convergence: are bad SCCs from determined or free entries?
3. Does ANY completion strategy work? (good-targeting, identity, random)
4. Is the failure universal across ALL candidate cycles?
5. What structural difference between n=4 and n=5 causes the transition?

HYPOTHESES:
A. State space ratio: good/total shrinks with n, leaving too many bad configs
B. Binary context exhaustion: 3 binary procs force too many entries,
   leaving insufficient freedom for convergence
C. Forced privilege chains: determined entries create unavoidable
   privilege chains among non-good configs
D. Topological obstruction: the non-good graph's structure inherently
   contains SCCs regardless of free entry assignment
""")
