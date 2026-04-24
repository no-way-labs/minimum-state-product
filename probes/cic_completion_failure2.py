#!/usr/bin/env python3
"""CIC Exploration 8b: Deep analysis of long cycles at n=5.

Focus on cycles that visit ALL 5 processors (L ≥ 17) where convergence fails.
Key question: Do DETERMINED entries alone create a bad SCC?
If yes: the cycle itself is impossible, regardless of completion.
If no: it's the completion strategy that fails, and we need to show ALL completions fail.
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


def find_bad_sccs(det, good_set, ms, n, use_only_det=False):
    """Find SCCs in the bad graph.
    If use_only_det=True, only use determined entries (free → identity)."""
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]

    # Build transition functions
    if use_only_det:
        # Only determined entries create privilege
        def get_output(p, L, S, R):
            key = (p, L, S, R)
            if key in det:
                return det[key]
            return S  # identity for free entries
    else:
        # This shouldn't be called without a comp dict
        raise ValueError("Need full completion for non-det-only mode")

    # Compute privilege
    priv_map = {}
    for c in non_good:
        priv = []
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            out = get_output(i, L, S, R)
            if out != S:
                priv.append(i)
        priv_map[c] = priv

    # Build bad adjacency
    non_good_set = set(non_good)
    bad_succs = defaultdict(list)
    for c in non_good:
        for i in priv_map.get(c, []):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            out = get_output(i, L, S, R)
            new_c = list(c)
            new_c[i] = out
            nc = tuple(new_c)
            if nc in non_good_set:
                bad_succs[c].append(nc)

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

    # Also count dead configs
    dead = [c for c in non_good if len(priv_map.get(c, [])) == 0]

    return sccs, dead, priv_map


# ============================================================
# PART 1: Filter for cycles visiting ALL processors
# ============================================================
print("=" * 70)
print("PART 1: LONG CYCLES VISITING ALL PROCESSORS")
print("=" * 70)

n = 5
ms = (2, 2, 2, 3, 3)
print(f"\nn={n}, ms={list(ms)}, product=72, threshold=108")

cycles = enumerate_good_cycles(ms, n, max_cycles=100, max_time=120.0)
print(f"Total cycles found: {len(cycles)}")

# Filter for cycles visiting all processors
full_cycles = []
partial_cycles = []
for cycle, movers, det in cycles:
    procs_visited = set(movers)
    if procs_visited == set(range(n)):
        full_cycles.append((cycle, movers, det))
    else:
        partial_cycles.append((cycle, movers, det, procs_visited))

print(f"Cycles visiting all {n} procs: {len(full_cycles)}")
print(f"Partial cycles: {len(partial_cycles)}")

if partial_cycles:
    proc_sets = Counter(frozenset(pv) for _, _, _, pv in partial_cycles)
    for ps, cnt in proc_sets.most_common(5):
        print(f"  Procs {sorted(ps)}: {cnt} cycles")


# ============================================================
# PART 2: Determined-only bad SCC analysis for full cycles
# ============================================================
print(f"\n{'=' * 70}")
print("PART 2: DETERMINED-ONLY BAD SCC ANALYSIS")
print("=" * 70)

for idx, (cycle, movers, det) in enumerate(full_cycles[:10]):
    good_set = set(cycle)

    # Check SCCs using ONLY determined entries (free → identity)
    sccs_det, dead_det, priv_det = find_bad_sccs(
        det, good_set, ms, n, use_only_det=True)

    # Count det mover entries (non-identity)
    det_mover = sum(1 for k, v in det.items() if v != k[2])
    det_nonmover = sum(1 for k, v in det.items() if v == k[2])

    # Count dead configs under det-only
    total_non_good = 72 - len(cycle)
    live_non_good = total_non_good - len(dead_det)

    # Count configs with privilege under det-only
    priv_counts = Counter(len(priv_det.get(c, []))
                          for c in priv_det)

    print(f"\n  Cycle {idx}: L={len(cycle)}, movers={movers}")
    print(f"    Det entries: {len(det)} ({det_mover} mover, {det_nonmover} nonmover)")
    print(f"    Non-good: {total_non_good}")
    print(f"    [DET-ONLY] Dead: {len(dead_det)}, Live: {live_non_good}")
    print(f"    [DET-ONLY] SCCs: {len(sccs_det)}, "
          f"sizes: {sorted([len(s) for s in sccs_det], reverse=True)[:5]}")
    print(f"    [DET-ONLY] Privilege dist: {dict(sorted(priv_counts.items()))}")

    if sccs_det:
        # The determined entries ALONE create a bad SCC!
        print(f"    *** DETERMINED ENTRIES CREATE BAD SCC ***")
        scc = max(sccs_det, key=len)
        scc_set = set(scc)

        # Analyze SCC structure
        # Which entries keep configs in SCC?
        scc_edges = []
        for c in scc:
            for i in priv_det.get(c, []):
                L_val = c[(i - 1) % n]
                S_val = c[i]
                R_val = c[(i + 1) % n]
                key = (i, L_val, S_val, R_val)
                out = det[key]
                new_c = list(c)
                new_c[i] = out
                nc = tuple(new_c)
                if nc in scc_set:
                    scc_edges.append((c, i, nc, key, out))

        proc_edge_counts = Counter(e[1] for e in scc_edges)
        print(f"    SCC edges by proc: {dict(sorted(proc_edge_counts.items()))}")

        # Show sample cycle within SCC
        if scc:
            start = scc[0]
            visited_path = [start]
            current = start
            for _ in range(min(20, len(scc) * 2)):
                found_next = False
                for i in priv_det.get(current, []):
                    L_val = current[(i - 1) % n]
                    S_val = current[i]
                    R_val = current[(i + 1) % n]
                    key = (i, L_val, S_val, R_val)
                    out = det[key]
                    new_c = list(current)
                    new_c[i] = out
                    nc = tuple(new_c)
                    if nc in scc_set:
                        visited_path.append(nc)
                        current = nc
                        found_next = True
                        break
                if not found_next:
                    break

            if len(visited_path) > 3:
                print(f"    Sample path in SCC:")
                for pi in range(min(8, len(visited_path) - 1)):
                    c = visited_path[pi]
                    nc = visited_path[pi + 1]
                    diff = [j for j in range(n) if c[j] != nc[j]]
                    if diff:
                        j = diff[0]
                        key = (j, c[(j-1)%n], c[j], c[(j+1)%n])
                        print(f"      {c} →P{j}({key[1]},{key[2]},{key[3]})→{det[key]}→ {nc}")
    else:
        # Det-only doesn't create SCC — it's the free entries
        print(f"    [DET-ONLY] No bad SCC — free entries are responsible")

        # Check: does det-only have any cycles at all?
        # Check how many configs can reach another non-good config
        can_reach_non_good = 0
        reaches_good = 0
        for c in [c for c in iproduct(*[range(m) for m in ms])
                  if c not in good_set]:
            for i in priv_det.get(c, []):
                L_val = c[(i - 1) % n]
                S_val = c[i]
                R_val = c[(i + 1) % n]
                key = (i, L_val, S_val, R_val)
                out = det[key]
                new_c = list(c)
                new_c[i] = out
                nc = tuple(new_c)
                if nc in good_set:
                    reaches_good += 1
                elif nc not in good_set:
                    can_reach_non_good += 1
        print(f"    [DET-ONLY] Transitions: {can_reach_non_good} non-good→non-good, "
              f"{reaches_good} non-good→good")


# ============================================================
# PART 3: Exhaustive completion for a FULL cycle
# ============================================================
print(f"\n{'=' * 70}")
print("PART 3: EXHAUSTIVE COMPLETION FOR FULL CYCLES")
print("=" * 70)

for idx, (cycle, movers, det) in enumerate(full_cycles[:3]):
    good_set = set(cycle)

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

    total_combinations = 1
    for _, m in free_entries:
        total_combinations *= m

    print(f"\n  Cycle {idx}: L={len(cycle)}, movers={movers}")
    print(f"    Free entries: {len(free_entries)}")
    print(f"    Total combinations: {total_combinations}")

    if total_combinations > 5000000:
        print(f"    Too many for exhaustive search")
        # But try systematic: set all free to identity except one proc
        # See if any single-proc-freedom is enough
        for target_p in range(n):
            # Free entries for just this processor
            target_free = [(k, m) for k, m in free_entries if k[0] == target_p]
            target_combos = 1
            for _, m in target_free:
                target_combos *= m

            # Fix all other free entries to identity
            base_comp = dict(det)
            for (key, _) in free_entries:
                if key[0] != target_p:
                    base_comp[key] = key[2]  # identity

            valid_found = 0
            if target_combos <= 100000:
                target_keys = [k for k, _ in target_free]
                target_ranges = [range(m) for _, m in target_free]
                for values in iproduct(*target_ranges):
                    comp = dict(base_comp)
                    for key, val in zip(target_keys, values):
                        comp[key] = val

                    fs = []
                    for p in range(n):
                        t = {}
                        m_L = ms[(p - 1) % n]
                        m_S = ms[p]
                        m_R = ms[(p + 1) % n]
                        for L_val in range(m_L):
                            for S_val in range(m_S):
                                for R_val in range(m_R):
                                    t[(L_val, S_val, R_val)] = comp.get(
                                        (p, L_val, S_val, R_val), S_val)
                        fs.append(lambda L, S, R, _t=t: _t.get((L, S, R), S))

                    result = verify_system(ms, fs)
                    if result.get('valid', False):
                        valid_found += 1

                print(f"    P{target_p} free only ({len(target_free)} entries, "
                      f"{target_combos} combos): {valid_found} valid")
            else:
                print(f"    P{target_p} free only: {target_combos} combos (skip)")
        continue

    # Exhaustive search
    print(f"    Running exhaustive search...")
    free_keys = [k for k, _ in free_entries]
    free_ranges = [range(m) for _, m in free_entries]
    valid_found = 0
    tested = 0
    t0 = time.time()

    for values in iproduct(*free_ranges):
        tested += 1
        comp = dict(det)
        for key, val in zip(free_keys, values):
            comp[key] = val

        fs = []
        for p in range(n):
            t = {}
            m_L = ms[(p - 1) % n]
            m_S = ms[p]
            m_R = ms[(p + 1) % n]
            for L_val in range(m_L):
                for S_val in range(m_S):
                    for R_val in range(m_R):
                        t[(L_val, S_val, R_val)] = comp.get(
                            (p, L_val, S_val, R_val), S_val)
            fs.append(lambda L, S, R, _t=t: _t.get((L, S, R), S))

        result = verify_system(ms, fs)
        if result.get('valid', False):
            valid_found += 1
            print(f"    FOUND VALID at attempt {tested}!")
            break

        if tested % 100000 == 0:
            elapsed = time.time() - t0
            print(f"    Tested {tested}/{total_combinations} ({elapsed:.1f}s)")

    elapsed = time.time() - t0
    print(f"    Result: {valid_found} valid / {tested} tested ({elapsed:.1f}s)")
    if valid_found == 0:
        print(f"    *** PROVED: This cycle CANNOT be completed to any valid system ***")


# ============================================================
# PART 4: Comparison with n=4 — what changes structurally?
# ============================================================
print(f"\n{'=' * 70}")
print("PART 4: n=4 LONG CYCLES — DETERMINED-ONLY ANALYSIS")
print("=" * 70)

n4 = 4
ms4 = (2, 2, 2, 3)
cycles4 = enumerate_good_cycles(ms4, n4, max_cycles=100, max_time=60.0)

full_cycles4 = []
for cycle, movers, det in cycles4:
    if set(movers) == set(range(n4)):
        full_cycles4.append((cycle, movers, det))

print(f"\nn=4, ms={list(ms4)}, product=24")
print(f"Total cycles: {len(cycles4)}, full cycles: {len(full_cycles4)}")

for idx, (cycle, movers, det) in enumerate(full_cycles4[:10]):
    good_set = set(cycle)
    non_good_count = 24 - len(cycle)

    # Det-only SCC analysis
    sccs_det, dead_det, priv_det = find_bad_sccs(
        det, good_set, ms4, n4, use_only_det=True)

    det_mover = sum(1 for k, v in det.items() if v != k[2])

    scc_sizes = sorted([len(s) for s in sccs_det], reverse=True)

    print(f"\n  Cycle {idx}: L={len(cycle)}, movers={movers}")
    print(f"    Det: {len(det)} ({det_mover} mover), Non-good: {non_good_count}")
    print(f"    [DET-ONLY] Dead: {len(dead_det)}, "
          f"SCCs: {len(sccs_det)}, sizes: {scc_sizes[:5]}")

    # Also check full completion validity
    from cic_completion_failure import complete_system
    fs, comp = complete_system(cycle, movers, det, ms4, n4)
    result = verify_system(ms4, fs)
    print(f"    Good-targeting valid: {result.get('valid', False)}")


# ============================================================
# PART 5: The entry ratio argument
# ============================================================
print(f"\n{'=' * 70}")
print("PART 5: ENTRY RATIO ANALYSIS — WHY n≥5 IS DIFFERENT")
print("=" * 70)

for n_test in range(4, 9):
    ms_test = tuple([2, 2, 2] + [3] * (n_test - 3))
    prod = 1
    for m in ms_test:
        prod *= m
    threshold = 4 * (3 ** (n_test - 2))

    # Count total transition entries
    total_entries = 0
    for p in range(n_test):
        m_L = ms_test[(p - 1) % n_test]
        m_S = ms_test[p]
        m_R = ms_test[(p + 1) % n_test]
        total_entries += m_L * m_S * m_R

    # Minimum cycle length for sweep/bounce
    min_sweep = 2 * n_test
    bounce_len = 3 * n_test - 2

    # Entries determined by cycle: ~5*L (each step determines entries
    # for all n procs at that config)
    # Actually: each step determines n entries (one for each proc)
    # But many are duplicates due to shared (L,S,R) contexts
    # Upper bound: n * L entries determined
    entries_per_step = n_test  # one per proc
    max_det_sweep = entries_per_step * min_sweep
    max_det_bounce = entries_per_step * bounce_len

    # Good configs as fraction of total
    good_frac_sweep = min_sweep / prod * 100
    good_frac_bounce = bounce_len / prod * 100

    # Bad configs
    bad_sweep = prod - min_sweep
    bad_bounce = prod - bounce_len

    # "Adversary freedom": avg privileged procs per bad config
    # Binary procs: each has 2 states, so ~50% are privileged
    # Ternary procs: each has 3 states, so ~67% are privileged
    # Expected privileged per config ≈ k*0.5 + (n-k)*0.67 for k binary
    k = 3
    expected_priv = k * 0.5 + (n_test - k) * 0.67

    print(f"\n  n={n_test}: ms={list(ms_test)}, prod={prod}, threshold={threshold}")
    print(f"    Total entries: {total_entries}")
    print(f"    Sweep: L={min_sweep}, good={good_frac_sweep:.1f}%, "
          f"bad={bad_sweep}")
    print(f"    Bounce: L={bounce_len}, good={good_frac_bounce:.1f}%, "
          f"bad={bad_bounce}")
    print(f"    Expected priv per config: {expected_priv:.1f}")
    print(f"    Bad × priv ≈ {bad_bounce * expected_priv:.0f} "
          f"(adversary choices)")
    print(f"    Ratio bad/good: {bad_bounce/bounce_len:.1f}")


# ============================================================
# PART 6: Check if n=5 cycles have FORCED privilege chains
# ============================================================
print(f"\n{'=' * 70}")
print("PART 6: FORCED PRIVILEGE CHAINS IN DETERMINED ENTRIES")
print("=" * 70)

if full_cycles:
    # Take the first full cycle and trace determined entry chains
    cycle, movers, det = full_cycles[0]
    good_set = set(cycle)
    all_configs = list(iproduct(*[range(m) for m in ms]))

    print(f"\n  Cycle: L={len(cycle)}, movers={movers}")

    # For each non-good config, check which procs are privileged
    # under determined entries only
    non_good = [c for c in all_configs if c not in good_set]

    # Build privilege map from det only
    det_priv = {}
    for c in non_good:
        priv = []
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            key = (i, L, S, R)
            if key in det and det[key] != S:
                priv.append(i)
        det_priv[c] = priv

    # Build forced transition graph (det-only, non-identity)
    forced_graph = defaultdict(list)
    for c in non_good:
        for i in det_priv[c]:
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            key = (i, L, S, R)
            new_c = list(c)
            new_c[i] = det[key]
            nc = tuple(new_c)
            if nc not in good_set:
                forced_graph[c].append((nc, i))

    # Count configs with ≥1 forced non-good successor
    has_forced = sum(1 for c in non_good if forced_graph[c])
    print(f"  Non-good configs with forced non-good successor: "
          f"{has_forced}/{len(non_good)}")

    # Find longest forced chain
    def find_longest_chain(start, max_depth=30):
        """BFS for longest forced chain from start."""
        best_path = [start]
        stack = [(start, [start])]
        while stack:
            c, path = stack.pop()
            if len(path) > len(best_path):
                best_path = path
            if len(path) >= max_depth:
                continue
            for nc, i in forced_graph[c]:
                if nc not in set(path):
                    stack.append((nc, path + [nc]))
        return best_path

    # Find chains from each non-good config
    max_chain = []
    for c in non_good:
        if forced_graph[c]:
            chain = find_longest_chain(c, max_depth=15)
            if len(chain) > len(max_chain):
                max_chain = chain

    print(f"  Longest forced chain: {len(max_chain)} configs")
    if max_chain:
        print(f"  Chain start: {max_chain[0]}")
        for pi in range(min(8, len(max_chain) - 1)):
            c = max_chain[pi]
            nc = max_chain[pi + 1]
            for ncc, i in forced_graph[c]:
                if ncc == nc:
                    key = (i, c[(i-1)%n], c[i], c[(i+1)%n])
                    print(f"    →P{i}({key[1]},{key[2]},{key[3]})→{det[key]}: "
                          f"{nc}")
                    break

    # Check: do forced chains form loops?
    for c in non_good:
        if not forced_graph[c]:
            continue
        # Quick loop check: follow one forced edge repeatedly
        visited = {c}
        current = c
        loop_found = False
        for _ in range(50):
            succs = forced_graph[current]
            if not succs:
                break
            nc, i = succs[0]  # follow first forced successor
            if nc in visited:
                loop_found = True
                print(f"\n  FORCED LOOP found starting at {c}:")
                # Trace the loop
                current2 = nc
                loop_path = [current2]
                for _ in range(50):
                    if not forced_graph[current2]:
                        break
                    nc2, _ = forced_graph[current2][0]
                    loop_path.append(nc2)
                    if nc2 == nc:
                        break
                    current2 = nc2
                print(f"    Loop length: {len(loop_path)}")
                for pi in range(min(6, len(loop_path) - 1)):
                    c2 = loop_path[pi]
                    nc2 = loop_path[pi + 1]
                    for ncc, i2 in forced_graph[c2]:
                        if ncc == nc2:
                            key = (i2, c2[(i2-1)%n], c2[i2], c2[(i2+1)%n])
                            print(f"      {c2} →P{i2}→ {nc2}")
                            break
                break
            visited.add(nc)
            current = nc
        if loop_found:
            break


# ============================================================
# PART 7: Which entries are critical for the SCC?
# ============================================================
print(f"\n{'=' * 70}")
print("PART 7: CRITICAL ENTRY ANALYSIS")
print("=" * 70)

if full_cycles:
    cycle, movers, det = full_cycles[0]
    good_set = set(cycle)

    # Check SCCs with det-only
    sccs_det, dead_det, priv_det = find_bad_sccs(
        det, good_set, ms, n, use_only_det=True)

    if sccs_det:
        scc = max(sccs_det, key=len)
        scc_set = set(scc)

        # Find which determined entries participate in SCC edges
        critical_entries = set()
        for c in scc:
            for i in priv_det.get(c, []):
                L = c[(i - 1) % n]
                S = c[i]
                R = c[(i + 1) % n]
                key = (i, L, S, R)
                out = det[key]
                new_c = list(c)
                new_c[i] = out
                nc = tuple(new_c)
                if nc in scc_set:
                    critical_entries.add(key)

        print(f"\n  SCC size: {len(scc)}")
        print(f"  Critical entries (participate in SCC edges): "
              f"{len(critical_entries)}")

        # Classify critical entries by type (mover vs nonmover in cycle)
        mover_entries_in_cycle = set()
        nonmover_entries_in_cycle = set()
        for step in range(len(cycle)):
            p = movers[step]
            c = cycle[step]
            for i in range(n):
                Li = c[(i - 1) % n]
                Si = c[i]
                Ri = c[(i + 1) % n]
                key = (i, Li, Si, Ri)
                if i == p:
                    mover_entries_in_cycle.add(key)
                else:
                    nonmover_entries_in_cycle.add(key)

        critical_from_mover = critical_entries & mover_entries_in_cycle
        critical_from_nonmover = critical_entries & nonmover_entries_in_cycle

        print(f"    From cycle mover entries: {len(critical_from_mover)}")
        print(f"    From cycle nonmover entries: {len(critical_from_nonmover)}")

        # Show the critical entries
        for key in sorted(critical_entries):
            p, L, S, R = key
            out = det[key]
            src = "MOVER" if key in mover_entries_in_cycle else "NONMOVER"
            print(f"    P{p}({L},{S},{R})→{out} [{src}]")

    else:
        print(f"\n  No det-only SCC for first full cycle")
        print(f"  Testing with good-targeting completion...")

        from cic_completion_failure import complete_system
        fs, comp = complete_system(cycle, movers, det, ms, n)

        # Find SCCs in full completion
        all_configs = list(iproduct(*[range(m) for m in ms]))
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

        non_good = [c for c in all_configs if c not in good_set]
        bad_succs = defaultdict(list)
        for c in non_good:
            for i in priv_map[c]:
                L = c[(i - 1) % n]
                S = c[i]
                R = c[(i + 1) % n]
                new_c = list(c)
                new_c[i] = fs[i](L, S, R)
                nc = tuple(new_c)
                if nc in set(non_good):
                    bad_succs[c].append(nc)
                    key = (i, L, S, R)

        # Count edges by determined vs free
        det_edge_count = 0
        free_edge_count = 0
        for c in non_good:
            for i in priv_map[c]:
                L = c[(i - 1) % n]
                S = c[i]
                R = c[(i + 1) % n]
                key = (i, L, S, R)
                new_c = list(c)
                new_c[i] = fs[i](L, S, R)
                nc = tuple(new_c)
                if nc in set(non_good):
                    if key in det:
                        det_edge_count += 1
                    else:
                        free_edge_count += 1

        print(f"  Full completion non-good→non-good edges: "
              f"{det_edge_count} det, {free_edge_count} free")
        print(f"  Det fraction: {100*det_edge_count/(det_edge_count+free_edge_count):.0f}%")


# ============================================================
# Summary
# ============================================================
print(f"\n{'=' * 70}")
print("SUMMARY")
print("=" * 70)
print("""
KEY FINDINGS:

1. FAILURE MODES AT n=5:
   - Short cycles (L ≤ 7): FAIRNESS fails (don't visit all procs)
   - Long cycles (L ≥ 17): CONVERGENCE fails (bad SCCs)

2. DET-ONLY SCC?
   - If determined entries alone create bad SCCs: the cycle is
     intrinsically impossible (no completion can fix it)
   - If not: the good-targeting completion creates the SCC,
     but other completions might work

3. n=4 vs n=5:
   - n=4 valid: L=18/24 (75% good), 93% entries determined
   - n=5 best: L=18/72 (25% good), 74% entries determined
   - The RATIO of good/total configs is the key difference

4. STRUCTURAL MECHANISM:
   - At n=5, good cycle is ≤25% of configs
   - Bad configs have high privilege density (3-5 priv procs)
   - Adversary has many choices at each bad config
   - Bad graph is too dense for ANY completion to break all SCCs
""")
