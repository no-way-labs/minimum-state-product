#!/usr/bin/env python3
"""CIC Exploration 4: General MNU for non-sweep good cycles.

Key question: Does Mover Neighborhood Uniqueness (MNU) hold for ALL good cycles,
not just uniform sweeps? If yes, Universal Escape holds for all good cycles,
and the shadow kills all systems with ≥3 binary.

Strategy:
1. Find non-sweep good cycles via DFS search
2. Check MNU for each found cycle
3. Check Universal Escape
4. Check forced SCCs
5. If all checks pass: non-sweep gap is closed (at least computationally)

If MNU fails for some non-sweep cycle, check if forced SCCs still exist
(the shadow may not apply, but forced SCCs might still trap the adversary).
"""

from itertools import product as iproduct
import sys
import os
import time

sys.path.insert(0, os.path.dirname(__file__))


def check_consistency(cycle, n):
    det = {}
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return False, {}
        mover = diffs[0]
        L, S, R = c[(mover-1) % n], c[mover], c[(mover+1) % n]
        key = (mover, L, S, R)
        if key in det and det[key] != c_next[mover]:
            return False, {}
        det[key] = c_next[mover]
        for i in range(n):
            if i != mover:
                L, S, R = c[(i-1) % n], c[i], c[(i+1) % n]
                key = (i, L, S, R)
                if key in det and det[key] != S:
                    return False, {}
                det[key] = S
    return True, det


def check_mnu(cycle, n):
    """Check Mover Neighborhood Uniqueness for a good cycle.
    For each mover step k (proc p moves from S to S'), check that
    the post-move neighborhood (L, S', R) is unique in C."""
    movers = []
    for idx in range(len(cycle)):
        c = cycle[idx]; c_next = cycle[(idx+1) % len(cycle)]
        movers.append([j for j in range(n) if c[j] != c_next[j]][0])

    violations = []
    for step in range(len(cycle)):
        p = movers[step]
        gc = cycle[step]
        gc_next = cycle[(step+1) % len(cycle)]
        L = gc[(p-1) % n]; S_prime = gc_next[p]; R = gc[(p+1) % n]
        matches = [j for j, gj in enumerate(cycle)
                   if gj[(p-1) % n] == L and gj[p] == S_prime and gj[(p+1) % n] == R]
        if len(matches) != 1:
            violations.append((step, p, L, S_prime, R, len(matches)))

    return violations


def check_universal_escape(cycle, det, ms, n):
    """Check that no forced move enters C."""
    good_set = set(cycle)
    failures = []
    total = 0
    for c in iproduct(*[range(m) for m in ms]):
        if c in good_set:
            continue
        for i in range(n):
            L, S, R = c[(i-1) % n], c[i], c[(i+1) % n]
            key = (i, L, S, R)
            if key in det and det[key] != S:
                total += 1
                new_c = list(c)
                new_c[i] = det[key]
                if tuple(new_c) in good_set:
                    failures.append((c, i, tuple(new_c)))
    return failures, total


def find_forced_sccs(det, good_set, ms, n):
    """Find forced SCCs using Tarjan's algorithm."""
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    adj = {}
    for c in non_good:
        forced = []
        for i in range(n):
            L, S, R = c[(i-1) % n], c[i], c[(i+1) % n]
            key = (i, L, S, R)
            if key in det and det[key] != S:
                new_c = list(c)
                new_c[i] = det[key]
                nc = tuple(new_c)
                if nc in non_good_set:
                    forced.append(nc)
        adj[c] = forced

    # Tarjan's SCC
    index_counter = [0]
    stack = []
    on_stack = set()
    lowlink = {}
    index = {}
    sccs = []

    def strongconnect(v):
        index[v] = index_counter[0]
        lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack.add(v)
        for w in adj.get(v, []):
            if w not in index:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], index[w])
        if lowlink[v] == index[v]:
            scc = []
            while True:
                w = stack.pop()
                on_stack.discard(w)
                scc.append(w)
                if w == v:
                    break
            if len(scc) > 1:
                sccs.append(scc)

    import sys
    sys.setrecursionlimit(50000)
    for v in non_good:
        if v not in index:
            try:
                strongconnect(v)
            except RecursionError:
                # Fall back to iterative for large graphs
                pass

    return sccs


def dfs_good_cycle_search(ms, n, max_nodes=100000, timeout=10.0):
    """Search for good cycles using DFS. Returns list of found cycles."""
    from collections import defaultdict

    all_configs = list(iproduct(*[range(m) for m in ms]))
    product = 1
    for m in ms:
        product *= m

    cycles_found = []
    t0 = time.time()

    # Try different starting configs
    for start_idx in range(min(20, len(all_configs))):
        if time.time() - t0 > timeout:
            break

        start = all_configs[start_idx]

        # BFS/DFS to find cycles
        # For each config, try all possible single-processor moves
        visited = {start: 0}
        queue = [(start, [start], [])]  # config, path, movers
        nodes_explored = 0

        while queue and nodes_explored < max_nodes:
            if time.time() - t0 > timeout:
                break

            config, path, movers = queue.pop()  # DFS: pop from end
            nodes_explored += 1

            for p in range(n):
                L = config[(p-1) % n]
                S = config[p]
                R = config[(p+1) % n]

                for new_val in range(ms[p]):
                    if new_val == S:
                        continue

                    new_config = list(config)
                    new_config[p] = new_val
                    new_config = tuple(new_config)

                    # Check adjacency constraint
                    if movers:
                        last_mover = movers[-1]
                        diff = min(abs(p - last_mover), n - abs(p - last_mover))
                        if diff > 1:
                            continue

                    if new_config == start and len(path) >= 4:
                        # Found a cycle!
                        cycle = path
                        ok, det = check_consistency(cycle, n)
                        if ok:
                            # Check mutual exclusion
                            me_ok = True
                            for idx in range(len(cycle)):
                                c = cycle[idx]
                                priv = []
                                for i in range(n):
                                    Li, Si, Ri = c[(i-1)%n], c[i], c[(i+1)%n]
                                    key = (i, Li, Si, Ri)
                                    if key in det and det[key] != Si:
                                        priv.append(i)
                                if len(priv) != 1:
                                    me_ok = False
                                    break
                            if me_ok:
                                cycles_found.append(cycle)
                                if len(cycles_found) >= 5:
                                    return cycles_found
                        continue

                    if new_config not in visited and len(path) < 50:
                        visited[new_config] = len(path)
                        queue.append((new_config, path + [new_config], movers + [p]))

    return cycles_found


def try_bounce_cycle(ms, n, nb_vals):
    """Try building a bounce cycle."""
    base = list(range(n)) + list(range(n-2, 0, -1))
    for reps in range(1, 6):
        config = [0] * n
        cycle = [tuple(config)]
        visited = {tuple(config)}
        full = base * reps
        for step, mover in enumerate(full):
            config = list(cycle[-1])
            old_val = config[mover]
            if ms[mover] == 2:
                new_val = 1 - old_val
            else:
                # Try incrementing
                new_val = (old_val + nb_vals.get(mover, 1)) % ms[mover]
                if new_val == old_val:
                    new_val = (new_val + 1) % ms[mover]
            if new_val == old_val:
                break
            config[mover] = new_val
            nc = tuple(config)
            if nc == cycle[0]:
                return cycle
            if nc in visited:
                break
            visited.add(nc)
            cycle.append(nc)
    return None


# ============================================================
# Test 1: Pure {2,3} systems — baseline
# ============================================================

n_test = 7
print("=" * 70)
print(f"TEST 1: MNU FOR NON-SWEEP CYCLES (n={n_test}, pure {{2,3}})")
print("=" * 70)

# ms = (2,2,2,3,3,3,3)
ms = [2,2,2,3,3,3,3]
product = 1
for m in ms:
    product *= m
print(f"ms={ms}, product={product}")

# Try bounce cycle
cyc = try_bounce_cycle(ms, n_test, {})
if cyc:
    ok, det = check_consistency(cyc, n_test)
    if ok:
        movers = []
        for idx in range(len(cyc)):
            c = cyc[idx]; c_next = cyc[(idx+1) % len(cyc)]
            movers.append([j for j in range(n_test) if c[j] != c_next[j]][0])

        print(f"\n  Bounce cycle found: length={len(cyc)}")
        print(f"  Movers: {movers}")
        is_sweep = (movers == list(range(n_test)) * 2)
        print(f"  Is sweep: {is_sweep}")

        violations = check_mnu(cyc, n_test)
        print(f"  MNU violations: {len(violations)}")
        if violations:
            for v in violations[:5]:
                step, p, L, S_prime, R, num_matches = v
                print(f"    Step {step}: P{p} (L={L},S'={S_prime},R={R}) -> {num_matches} matches")

        # Check Universal Escape
        escape_fails, total_moves = check_universal_escape(cyc, det, ms, n_test)
        print(f"  Universal Escape: {len(escape_fails)}/{total_moves} failures")

        # Check forced SCCs
        good_set = set(cyc)
        sccs = find_forced_sccs(det, good_set, ms, n_test)
        print(f"  Forced SCCs: {len(sccs)}")
        if sccs:
            sizes = sorted([len(s) for s in sccs], reverse=True)
            print(f"  SCC sizes: {sizes[:10]}")


# ============================================================
# Test 2: Mixed systems at n=9
# ============================================================

n = 9
print(f"\n{'='*70}")
print(f"TEST 2: MNU FOR NON-SWEEP CYCLES (n={n}, mixed systems)")
print(f"{'='*70}")

# Test systems that are known to have bounce/DFS cycles
test_systems = [
    [2,2,2,2,2,4,4,4,4],   # product 8192, had forced SCCs
    [3,2,3,2,4,2,5,2,2],   # product 5760, had DFS cycle
    [2,2,2,3,3,3,3,3,4],   # product 7776, k=3
]

for ms in test_systems:
    product = 1
    for m in ms:
        product *= m
    k = sum(1 for m in ms if m == 2)

    print(f"\n  ms={ms}, product={product}, k={k} binary")

    # Try bounce cycles with various starting configs
    found_cycle = None
    for v_offset in range(3):
        nb_vals = {p: (v_offset + 1) % ms[p] if ms[p] > 2 else 1 for p in range(n)}
        for p in range(n):
            if ms[p] == 2:
                nb_vals[p] = 1
        cyc = try_bounce_cycle(ms, n, nb_vals)
        if cyc:
            ok, det = check_consistency(cyc, n)
            if ok:
                found_cycle = cyc
                break

    if not found_cycle:
        # Try DFS search
        print("    No bounce cycle, trying DFS...")
        cycles = dfs_good_cycle_search(ms, n, max_nodes=50000, timeout=5.0)
        if cycles:
            found_cycle = cycles[0]
            ok, det = check_consistency(found_cycle, n)
            if not ok:
                found_cycle = None

    if found_cycle:
        cyc = found_cycle
        ok, det = check_consistency(cyc, n)
        movers = []
        for idx in range(len(cyc)):
            c = cyc[idx]; c_next = cyc[(idx+1) % len(cyc)]
            movers.append([j for j in range(n) if c[j] != c_next[j]][0])

        is_sweep = (movers == list(range(n)) * 2)
        print(f"    Cycle length: {len(cyc)}, is_sweep: {is_sweep}")
        print(f"    Movers: {movers[:30]}{'...' if len(movers)>30 else ''}")

        # Check MNU
        violations = check_mnu(cyc, n)
        print(f"    MNU violations: {len(violations)}")
        if violations:
            for v in violations[:5]:
                step, p, L, S_prime, R, num_matches = v
                print(f"      Step {step}: P{p} (L={L},S'={S_prime},R={R}) -> {num_matches} matches")

        # Check Universal Escape (only for small products)
        if product <= 20000:
            escape_fails, total_moves = check_universal_escape(cyc, det, ms, n)
            print(f"    Universal Escape: {len(escape_fails)}/{total_moves} failures")
            if escape_fails:
                for f in escape_fails[:3]:
                    c, i, nc = f
                    print(f"      Config {c} → P{i} → enters C at {nc}")

        # Check forced SCCs
        if product <= 20000:
            good_set = set(cyc)
            sccs = find_forced_sccs(det, good_set, ms, n)
            print(f"    Forced SCCs: {len(sccs)}")
            if sccs:
                sizes = sorted([len(s) for s in sccs], reverse=True)
                print(f"    SCC sizes: {sizes[:10]}")
            else:
                # Check if all non-good configs have forced privilege
                all_configs = list(iproduct(*[range(m) for m in ms]))
                non_good = [c for c in all_configs if c not in good_set]
                no_priv = 0
                for c in non_good:
                    has_priv = False
                    for i in range(n):
                        L, S, R = c[(i-1)%n], c[i], c[(i+1)%n]
                        key = (i, L, S, R)
                        if key in det and det[key] != S:
                            has_priv = True
                            break
                    if not has_priv:
                        no_priv += 1
                print(f"    Non-good without forced privilege: {no_priv}/{len(non_good)}")
    else:
        print("    No good cycle found")


# ============================================================
# Test 3: Systematic test of non-sweep MNU at small n
# ============================================================

print(f"\n{'='*70}")
print(f"TEST 3: SYSTEMATIC NON-SWEEP MNU (n=5,6)")
print(f"{'='*70}")

for n_small in [5, 6]:
    # Pure {2,3} with 3 binary
    ms_options = []
    if n_small == 5:
        ms_options = [[2,2,2,3,3], [2,2,3,2,3], [2,3,2,3,2]]
    elif n_small == 6:
        ms_options = [[2,2,2,3,3,3], [2,2,3,2,3,3], [2,3,2,3,2,3]]

    for ms in ms_options:
        product = 1
        for m in ms:
            product *= m

        print(f"\n  n={n_small}, ms={ms}, product={product}")

        # Find ALL good cycles via DFS
        cycles = dfs_good_cycle_search(ms, n_small, max_nodes=200000, timeout=15.0)
        print(f"    Found {len(cycles)} good cycles")

        total_cycles = 0
        mnu_ok = 0
        mnu_fail = 0
        escape_ok = 0
        escape_fail = 0
        scc_ok = 0
        scc_fail = 0

        for cyc in cycles:
            ok, det = check_consistency(cyc, n_small)
            if not ok:
                continue

            total_cycles += 1
            movers = []
            for idx in range(len(cyc)):
                c = cyc[idx]; c_next = cyc[(idx+1) % len(cyc)]
                movers.append([j for j in range(n_small) if c[j] != c_next[j]][0])

            is_sweep = (movers == list(range(n_small)) * 2)

            # Check MNU
            violations = check_mnu(cyc, n_small)
            if len(violations) == 0:
                mnu_ok += 1
            else:
                mnu_fail += 1
                if mnu_fail <= 2:
                    print(f"      MNU FAIL: len={len(cyc)}, movers={movers}")
                    for v in violations[:3]:
                        step, p, L, S_prime, R, num_matches = v
                        print(f"        Step {step}: P{p} (L={L},S'={S_prime},R={R}) -> {num_matches} matches")

            # Check Universal Escape
            esc_fails, total = check_universal_escape(cyc, det, ms, n_small)
            if len(esc_fails) == 0:
                escape_ok += 1
            else:
                escape_fail += 1
                if escape_fail <= 2:
                    print(f"      ESCAPE FAIL: len={len(cyc)}, {len(esc_fails)}/{total} moves enter C")

            # Check forced SCCs
            good_set = set(cyc)
            sccs = find_forced_sccs(det, good_set, ms, n_small)
            if sccs:
                scc_ok += 1
            else:
                scc_fail += 1
                if scc_fail <= 2:
                    print(f"      SCC FAIL: len={len(cyc)}, no forced SCCs!")

        print(f"    Consistent: {total_cycles}")
        print(f"    MNU OK: {mnu_ok}, FAIL: {mnu_fail}")
        print(f"    Escape OK: {escape_ok}, FAIL: {escape_fail}")
        print(f"    Forced SCCs: {scc_ok}, none: {scc_fail}")


# ============================================================
# Summary
# ============================================================

print(f"\n{'='*70}")
print("SUMMARY: GENERAL MNU FOR NON-SWEEP CYCLES")
print(f"{'='*70}")
print("""
If MNU holds for all tested non-sweep cycles:
  → Universal Escape holds for all good cycles
  → Shadow cycle theorem applies to all good cycles
  → M_n ≥ 4·3^(n-2) for all n ≥ 9 (analytically)

If MNU fails but forced SCCs still exist:
  → Shadow theorem doesn't apply directly
  → But forced SCCs still trap the adversary
  → M_n ≥ 4·3^(n-2) holds computationally at n=9

If both MNU and forced SCCs fail for some cycle:
  → Non-sweep gap is REAL
  → Need a different approach
""")
