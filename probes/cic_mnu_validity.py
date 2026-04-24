#!/usr/bin/env python3
"""CIC Exploration 5b: Check if MNU-failing cycles can form valid systems.

Key question: For n=4 ms=(2,3,3,2), MNU fails for 45/50 cycles.
Can those cycles be completed to VALID self-stabilizing systems?
If NO: MNU effectively holds for valid systems.
If YES: Shadow argument breaks, need forced SCC approach.
"""

from itertools import product as iproduct
from collections import defaultdict
import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from verifier import verify_system


def enumerate_good_cycles(ms, n, max_cycles=200, max_time=30.0):
    """Enumerate good cycles via DFS."""
    import time
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


def check_mnu(cycle, movers, n):
    """Check MNU. Returns list of violations."""
    violations = []
    for step in range(len(cycle)):
        p = movers[step]
        gc_next = cycle[(step + 1) % len(cycle)]
        L = cycle[step][(p - 1) % n]
        S_prime = gc_next[p]
        R = cycle[step][(p + 1) % n]
        matches = sum(1 for gj in cycle
                      if gj[(p - 1) % n] == L
                      and gj[p] == S_prime
                      and gj[(p + 1) % n] == R)
        if matches != 1:
            violations.append((step, p, L, S_prime, R, matches))
    return violations


def complete_and_verify(cycle, movers, det, ms, n):
    """Complete a good cycle to a full system and verify."""
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
        best_out = S
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

    result = verify_system(ms, fs)
    return result


def check_escape(cycle, det, ms, n):
    """Check Universal Escape."""
    good_set = set(cycle)
    failures = 0
    total = 0
    for c in iproduct(*[range(m) for m in ms]):
        if c in good_set:
            continue
        for i in range(n):
            L, S, R = c[(i - 1) % n], c[i], c[(i + 1) % n]
            key = (i, L, S, R)
            if key in det and det[key] != S:
                total += 1
                new_c = list(c)
                new_c[i] = det[key]
                if tuple(new_c) in good_set:
                    failures += 1
    return failures, total


def check_forced_sccs(det, good_set, ms, n):
    """Find forced SCCs among non-good configs."""
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    adj = {}
    for c in non_good:
        forced = []
        for i in range(n):
            L, S, R = c[(i - 1) % n], c[i], c[(i + 1) % n]
            key = (i, L, S, R)
            if key in det and det[key] != S:
                new_c = list(c)
                new_c[i] = det[key]
                nc = tuple(new_c)
                if nc in non_good_set:
                    forced.append(nc)
        adj[c] = forced

    # Tarjan's SCC (iterative)
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

    sys.setrecursionlimit(10000)
    for v in non_good:
        if v not in index:
            strongconnect(v)

    return sccs


# ============================================================
# Main analysis
# ============================================================
print("=" * 70)
print("MNU-FAILING CYCLE VALIDITY CHECK")
print("=" * 70)

n = 4
ms = (2, 3, 3, 2)
product_val = 36
print(f"\nn={n}, ms={list(ms)}, product={product_val}")

cycles = enumerate_good_cycles(ms, n, max_cycles=200, max_time=60.0)
print(f"Found {len(cycles)} good cycles")

mnu_ok_valid = 0
mnu_ok_invalid = 0
mnu_fail_valid = 0
mnu_fail_invalid = 0

mnu_fail_escape_ok = 0
mnu_fail_escape_fail = 0
mnu_fail_scc_yes = 0
mnu_fail_scc_no = 0

for idx, (cycle, movers, det) in enumerate(cycles):
    violations = check_mnu(cycle, movers, n)
    has_mnu = len(violations) == 0

    # Check escape
    esc_fails, esc_total = check_escape(cycle, det, ms, n)

    # Check forced SCCs
    good_set = set(cycle)
    sccs = check_forced_sccs(det, good_set, ms, n)

    # Complete to system and verify
    result = complete_and_verify(cycle, movers, det, ms, n)
    is_valid = result.get('valid', False)

    if has_mnu:
        if is_valid:
            mnu_ok_valid += 1
        else:
            mnu_ok_invalid += 1
    else:
        if is_valid:
            mnu_fail_valid += 1
        else:
            mnu_fail_invalid += 1
        if esc_fails == 0:
            mnu_fail_escape_ok += 1
        else:
            mnu_fail_escape_fail += 1
        if sccs:
            mnu_fail_scc_yes += 1
        else:
            mnu_fail_scc_no += 1

    # Print details for interesting cases
    if not has_mnu and idx < 10:
        viol_types = set()
        for v in violations:
            step, p, L, S_prime, R, cnt = v
            ptype = "binary" if ms[p] == 2 else "ternary"
            viol_types.add(ptype)
        print(f"\n  Cycle {idx}: L={len(cycle)}, MNU={'OK' if has_mnu else 'FAIL'}"
              f" ({len(violations)} violations at {viol_types})")
        print(f"    Movers: {movers}")
        print(f"    Escape: {esc_fails}/{esc_total}")
        print(f"    Forced SCCs: {len(sccs)}"
              f" (sizes: {sorted([len(s) for s in sccs], reverse=True)[:5]})")
        print(f"    Valid system: {is_valid}")
        if is_valid:
            nc = result.get('cycle_length', '?')
            ng = len(result.get('good_configs', set()))
            print(f"    *** VALID: good cycle len={nc}, "
                  f"good configs={ng}")

    if has_mnu and idx < 200:
        if is_valid:
            print(f"\n  Cycle {idx}: L={len(cycle)}, MNU=OK, VALID")
            print(f"    Movers: {movers}")

print(f"\n{'=' * 70}")
print("SUMMARY")
print(f"{'=' * 70}")
print(f"\nTotal cycles found: {len(cycles)}")
print(f"\nMNU OK  + VALID:   {mnu_ok_valid}")
print(f"MNU OK  + INVALID: {mnu_ok_invalid}")
print(f"MNU FAIL + VALID:  {mnu_fail_valid}  *** KEY ***")
print(f"MNU FAIL + INVALID: {mnu_fail_invalid}")
print(f"\nAmong MNU-failing cycles:")
print(f"  Escape OK:   {mnu_fail_escape_ok}")
print(f"  Escape FAIL: {mnu_fail_escape_fail}")
print(f"  Forced SCCs: {mnu_fail_scc_yes}")
print(f"  No SCCs:     {mnu_fail_scc_no}")

if mnu_fail_valid > 0:
    print("\n*** MNU FAILURE + VALID SYSTEM EXISTS ***")
    print("The shadow argument BREAKS for these cycles.")
    print("Must use forced SCC approach instead.")
elif mnu_fail_valid == 0:
    print("\n*** All MNU-failing cycles are INVALID ***")
    print("MNU effectively holds for all valid systems.")
    print("Shadow argument is sufficient.")


# ============================================================
# Also test n=3 systems
# ============================================================
print(f"\n{'=' * 70}")
print("n=3 SYSTEMS — ALL MNU OK, CHECKING VALIDITY")
print(f"{'=' * 70}")

for ms3 in [(2, 3, 2), (3, 3, 3), (2, 4, 3)]:
    n3 = 3
    prod = 1
    for m in ms3:
        prod *= m
    cycles = enumerate_good_cycles(ms3, n3, max_cycles=20, max_time=10.0)
    valid_count = 0
    for cycle, movers, det in cycles:
        result = complete_and_verify(cycle, movers, det, ms3, n3)
        if result.get('valid', False):
            valid_count += 1
    print(f"  ms={list(ms3)}, product={prod}: "
          f"{len(cycles)} cycles, {valid_count} valid")
