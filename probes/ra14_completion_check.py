#!/usr/bin/env python3
"""
RA14 v8: Completion check.

For the non-sweep non-EC cycles found by DFS at n=5 with 3 binary:
Can a complete valid self-stabilizing system be built around them?

If NO: the cycles are blocked at the system level, not the cycle level.
If YES: there's a real gap in the proof.
"""

import sys
import time
from collections import Counter, defaultdict
from itertools import product as iproduct
from math import prod

def check_ec(good, word, n):
    L = len(word)
    mt = defaultdict(set)
    nt = defaultdict(set)
    for t in range(L):
        c = good[t]
        m = word[t]
        for j in range(n):
            triple = (c[(j-1)%n], c[j], c[(j+1)%n])
            if j == m:
                mt[j].add(triple)
            else:
                nt[j].add(triple)
    for j in range(n):
        if mt[j] & nt[j]:
            return True
    return False

def is_uniform_sweep(word, n):
    L = len(word)
    if L % n != 0:
        return False
    reps = L // n
    doubled = word + word
    for start in range(n):
        for d in [1, -1]:
            sweep = [(start + d * i) % n for i in range(n)]
            full = sweep * reps
            for off in range(L):
                if doubled[off:off+L] == full:
                    return True
    return False

def enumerate_dfs(ms, n, max_cycles=5000, max_time=30.0):
    t0 = time.time()
    start = tuple([0]*n)
    results = []
    seen = set()
    max_len = min(4*n, prod(ms))
    def dfs(config, path, word, det):
        if time.time() - t0 > max_time or len(results) >= max_cycles:
            return
        for p in range(n):
            for nv in range(ms[p]):
                if nv == config[p]:
                    continue
                if word:
                    last = word[-1]
                    diff = min(abs(p - last), n - abs(p - last))
                    if diff > 1:
                        continue
                Lv = config[(p-1)%n]
                Sv = config[p]
                Rv = config[(p+1)%n]
                km = (p, Lv, Sv, Rv)
                nd = dict(det)
                if km in nd:
                    if nd[km] != nv:
                        continue
                else:
                    nd[km] = nv
                ok = True
                for i in range(n):
                    if i == p:
                        continue
                    ki = (i, config[(i-1)%n], config[i], config[(i+1)%n])
                    if ki in nd:
                        if nd[ki] != config[i]:
                            ok = False
                            break
                    else:
                        nd[ki] = config[i]
                if not ok:
                    continue
                nc = list(config)
                nc[p] = nv
                nc = tuple(nc)
                nw = word + [p]
                if nc == start and len(path) >= 2*n:
                    fc = Counter(nw)
                    if len(fc) == n:
                        ck = frozenset(path)
                        if ck not in seen:
                            seen.add(ck)
                            results.append((list(path), nw, dict(nd)))
                    continue
                if nc not in set(path) and len(path) < max_len:
                    path.append(nc)
                    dfs(nc, path, nw, nd)
                    path.pop()
    dfs(start, [start], [], {})
    return results


def verify_system(ms, n, tables):
    """
    Verify a complete self-stabilizing system.
    tables[p] maps (L, S, R) -> new_S.
    Returns (valid, details).
    """
    product_val = prod(ms)
    all_configs = list(iproduct(*(range(m) for m in ms)))

    # Check mutual exclusion and single privilege
    for config in all_configs:
        privileged = []
        for p in range(n):
            L = config[(p-1) % n]
            S = config[p]
            R = config[(p+1) % n]
            if (L, S, R) in tables[p] and tables[p][(L, S, R)] != S:
                privileged.append(p)
        if len(privileged) != 1:
            return False, f"Config {config}: {len(privileged)} privileged"

    # Check convergence (no non-trivial cycles reachable from any config)
    # Build the transition graph
    transitions = {}
    for config in all_configs:
        privileged = []
        for p in range(n):
            L = config[(p-1) % n]
            S = config[p]
            R = config[(p+1) % n]
            if (L, S, R) in tables[p] and tables[p][(L, S, R)] != S:
                privileged.append(p)
        if len(privileged) != 1:
            continue
        p = privileged[0]
        L = config[(p-1) % n]
        S = config[p]
        R = config[(p+1) % n]
        new_S = tables[p][(L, S, R)]
        new_config = list(config)
        new_config[p] = new_S
        transitions[config] = tuple(new_config)

    # Check that every config eventually reaches a cycle (liveness)
    # AND that the only cycle is the good cycle
    visited = {}
    for start_config in all_configs:
        if start_config in visited:
            continue
        path = []
        current = start_config
        path_set = set()
        while current not in visited and current not in path_set:
            path_set.add(current)
            path.append(current)
            if current not in transitions:
                break
            current = transitions[current]

        if current in path_set:
            # Found a cycle
            cycle_start = path.index(current)
            cycle = path[cycle_start:]
            cycle_set = frozenset(cycle)
            for c in path:
                visited[c] = cycle_set
        elif current in visited:
            for c in path:
                visited[c] = visited[current]
        else:
            return False, f"Config {start_config} reaches dead end"

    # All configs should reach the same cycle
    cycles = set(visited.values())
    if len(cycles) != 1:
        return False, f"Multiple cycles: {len(cycles)}"

    return True, "Valid"


def try_complete_system(ms, n, det):
    """Try to complete a deterministic transition function into a valid system.

    det: partial transition function from the good cycle.
    Returns: (success, tables) or (False, None)
    """
    # Extract what's determined
    tables = [dict() for _ in range(n)]
    for (p, L, S, R), new_S in det.items():
        tables[p][(L, S, R)] = new_S

    # For undefined contexts, try good-targeting: map to config in the good cycle
    # This is a heuristic — full completion is exponential
    all_configs = list(iproduct(*(range(m) for m in ms)))

    # Count undefined contexts per proc
    undefined = []
    for p in range(n):
        for L in range(ms[(p-1) % n]):
            for S in range(ms[p]):
                for R in range(ms[(p+1) % n]):
                    if (L, S, R) not in tables[p]:
                        undefined.append((p, L, S, R))

    # Try identity (non-mover) for all undefined
    tables_id = [dict(t) for t in tables]
    for p, L, S, R in undefined:
        tables_id[p][(L, S, R)] = S  # identity = no privilege

    valid, details = verify_system(ms, n, tables_id)
    if valid:
        return True, tables_id

    # Try random completions
    import random
    random.seed(42)
    for attempt in range(100):
        tables_try = [dict(t) for t in tables]
        for p, L, S, R in undefined:
            if random.random() < 0.5:
                tables_try[p][(L, S, R)] = S  # identity
            else:
                tables_try[p][(L, S, R)] = (S + 1) % ms[p]  # change

        valid, details = verify_system(ms, n, tables_try)
        if valid:
            return True, tables_try

    return False, None


# =============================================================================
# Main: check a few non-EC non-sweep cycles at n=5
# =============================================================================

print("=" * 70)
print("COMPLETION CHECK: can non-EC non-sweep cycles form valid systems?")
print("=" * 70)

n = 5
ms = [3, 3, 2, 2, 2]
print(f"n={n}, ms={ms}, product={prod(ms)}")

cycles = enumerate_dfs(ms, n, max_cycles=200, max_time=30.0)
print(f"Found {len(cycles)} cycles")

noec_ns = []
for cyc, w, det in cycles:
    if not is_uniform_sweep(w, n) and not check_ec(cyc, w, n):
        noec_ns.append((cyc, w, det))

print(f"Non-sweep non-EC: {len(noec_ns)}")

completions = 0
failures = 0
for i, (cyc, w, det) in enumerate(noec_ns[:20]):
    fc = Counter(w)
    success, tables = try_complete_system(ms, n, det)
    if success:
        completions += 1
        print(f"  [{i}] CL={len(w)}, fc={tuple(fc.get(p,0) for p in range(n))}: VALID SYSTEM FOUND")
    else:
        failures += 1
        if i < 5:
            print(f"  [{i}] CL={len(w)}, fc={tuple(fc.get(p,0) for p in range(n))}: completion failed")

print(f"\nCompletions: {completions}/{min(20, len(noec_ns))}")
print(f"Failures: {failures}/{min(20, len(noec_ns))}")

if completions > 0:
    print("\nWARNING: Non-EC non-sweep cycles CAN form valid systems!")
    print("This means the proof has a genuine gap.")
else:
    print("\nAll completion attempts failed.")
    print("This suggests cycle-level non-EC is necessary but not sufficient;")
    print("system-level constraints may block these cycles.")
