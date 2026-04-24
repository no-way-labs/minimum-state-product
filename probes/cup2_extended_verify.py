#!/usr/bin/env python3
"""Extended verification of CLB construction for larger n.

Also compare original vs fixed tiebreaker.
"""

import sys
import os
import time
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict, deque


def build_bounce_cycle(ms, n):
    up_down = list(range(n)) + list(range(n - 2, 0, -1))
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    full = up_down * (3 * n)
    for step, mover in enumerate(full):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            return cycle, full[:step + 1]
        if nc in visited:
            raise RuntimeError(f"Revisited {nc}")
        visited.add(nc)
        cycle.append(nc)
    raise RuntimeError("Cycle didn't close")


def build_system(n, fixed_tiebreaker=True):
    """Build the system. If fixed_tiebreaker=True, use best_ng=0."""
    ms = tuple([2] + [3] * (n - 2) + [2])
    cycle, movers = build_bounce_cycle(ms, n)
    good_set = set(cycle)

    all_configs = list(cartesian(*(range(m) for m in ms)))
    non_good_set = set(c for c in all_configs if c not in good_set)

    # Index configs by (p, L, S, R) for faster lookup
    config_index = defaultdict(list)
    for c in all_configs:
        if c not in good_set:
            for p in range(n):
                L = c[(p - 1) % n]
                S = c[p]
                R = c[(p + 1) % n]
                config_index[(p, L, S, R)].append(c)

    # Determined entries
    det = {}
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        mv = movers[idx]
        for p in range(n):
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            key = (p, L, S, R)
            if p == mv:
                det[key] = c_next[p]
            else:
                det[key] = S

    # Free entries
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

    # Greedy completion
    comp = dict(det)
    init_ng = 0 if fixed_tiebreaker else float('inf')

    for key in free_entries:
        p, L, S, R = key
        best_out = S
        best_good = 0
        best_ng = init_ng
        matching_configs = config_index[(p, L, S, R)]

        for out in range(ms[p]):
            ng = 0
            good_count = 0
            if out != S:
                for c in matching_configs:
                    new_c = tuple(c[j] if j != p else out for j in range(n))
                    if new_c in good_set:
                        good_count += 1
                    elif new_c in non_good_set:
                        ng += 1
            if good_count > best_good or (good_count == best_good and ng < best_ng):
                best_out = out
                best_good = good_count
                best_ng = ng
        comp[key] = best_out

    # Liveness fix
    liveness_fixes = 0
    for c in all_configs:
        has_priv = any(
            comp.get((p, c[(p - 1) % n], c[p], c[(p + 1) % n]), c[p]) != c[p]
            for p in range(n)
        )
        if not has_priv:
            liveness_fixes += 1
            best_key = None
            best_cost = float('inf')
            best_out_val = None
            for p in range(n):
                L2 = c[(p - 1) % n]
                S2 = c[p]
                R2 = c[(p + 1) % n]
                key2 = (p, L2, S2, R2)
                if key2 not in det:
                    for out in range(ms[p]):
                        if out != S2:
                            cost = sum(
                                1 for c2 in config_index[(p, L2, S2, R2)]
                                if tuple(c2[j] if j != p else out for j in range(n)) in non_good_set
                            )
                            if cost < best_cost:
                                best_cost = cost
                                best_key = key2
                                best_out_val = out
            if best_key:
                comp[best_key] = best_out_val

    def make_f(p_idx):
        def f(L, S, R):
            return comp.get((p_idx, L, S, R), S)
        return f

    fs = [make_f(p) for p in range(n)]
    return ms, fs, comp, cycle, movers, len(det), len(free_entries), liveness_fixes


def check_dag(ms, fs, good_set, n):
    """Check if bad-config graph is a DAG."""
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(c for c in all_configs if c not in good_set)

    # Build bad→bad adjacency
    in_deg = {c: 0 for c in bad_set}
    adj = {c: [] for c in bad_set}
    for c in bad_set:
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            if fs[i](L, S, R) != S:
                lst = list(c)
                lst[i] = fs[i](L, S, R)
                succ = tuple(lst)
                if succ in bad_set:
                    adj[c].append(succ)
                    in_deg[succ] += 1

    # Kahn's topological sort
    q = deque(c for c in bad_set if in_deg[c] == 0)
    processed = 0
    while q:
        c = q.popleft()
        processed += 1
        for s in adj[c]:
            in_deg[s] -= 1
            if in_deg[s] == 0:
                q.append(s)

    return processed == len(bad_set)


def check_properties(ms, fs, cycle, n):
    """Check mutual exclusion + closure + fairness on the good cycle."""
    # Each cycle config has exactly 1 privilege
    movers_in_cycle = set()
    for idx in range(len(cycle)):
        c = cycle[idx]
        priv = []
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            if fs[i](L, S, R) != S:
                priv.append(i)
        if len(priv) != 1:
            return False, f"cycle config {idx} has {len(priv)} privileges"
        movers_in_cycle.add(priv[0])

        # Check closure: successor is next cycle config
        p = priv[0]
        lst = list(c)
        lst[p] = fs[p](c[(p - 1) % n], c[p], c[(p + 1) % n])
        succ = tuple(lst)
        expected = cycle[(idx + 1) % len(cycle)]
        if succ != expected:
            return False, f"cycle config {idx} successor mismatch"

    # Fairness: all procs visited
    if movers_in_cycle != set(range(n)):
        return False, f"fairness: only {movers_in_cycle}"

    return True, "OK"


def main():
    print("EXTENDED VERIFICATION: CLB Construction")
    print("=" * 100)
    print(f"{'n':>3} {'cyc':>4} {'good':>6} {'det':>5} {'free':>5} {'lfx':>4} "
          f"{'ME+CL+F':>8} {'DAG':>4} {'VALID':>6} {'t(s)':>6}")
    print("-" * 100)

    for nv in range(4, 16):
        prod = 4 * 3 ** (nv - 2)
        if prod > 2000000:
            print(f"{nv:>3} SKIP (prod={prod})")
            continue

        t0 = time.time()
        ms, fs, comp, cycle, movers, n_det, n_free, lfx = build_system(nv, fixed_tiebreaker=True)
        n = nv
        good_set = set(cycle)

        # Extend good set: find all single-privilege configs that lead into cycle
        succ_map = {}
        all_configs = list(cartesian(*(range(m) for m in ms)))
        for c in all_configs:
            priv = []
            for i in range(n):
                L = c[(i - 1) % n]
                S = c[i]
                R = c[(i + 1) % n]
                if fs[i](L, S, R) != S:
                    priv.append(i)
            if len(priv) == 1:
                p = priv[0]
                lst = list(c)
                lst[p] = fs[p](c[(p - 1) % n], c[p], c[(p + 1) % n])
                succ_map[c] = tuple(lst)

        # Grow good set by following tails into cycle
        changed = True
        while changed:
            changed = False
            for c in list(succ_map.keys()):
                if c not in good_set and succ_map.get(c) in good_set:
                    good_set.add(c)
                    changed = True

        # Filter good_set to only closed subset
        changed = True
        while changed:
            changed = False
            to_remove = set()
            for c in good_set:
                if c not in succ_map:
                    to_remove.add(c)
                elif succ_map[c] not in good_set:
                    to_remove.add(c)
            if to_remove:
                good_set -= to_remove
                changed = True

        props_ok, props_msg = check_properties(ms, fs, cycle, n)
        is_dag = check_dag(ms, fs, good_set, n)

        # Check liveness
        dead = sum(1 for c in all_configs if not any(
            fs[i](c[(i-1)%n], c[i], c[(i+1)%n]) != c[i] for i in range(n)))

        elapsed = time.time() - t0
        valid = props_ok and is_dag and dead == 0
        n_good = len(good_set)

        print(f"{nv:>3} {len(cycle):>4} {n_good:>6} {n_det:>5} {n_free:>5} {lfx:>4} "
              f"{'OK' if props_ok else 'FAIL':>8} "
              f"{'Y' if is_dag else 'N':>4} "
              f"{'Y' if valid else 'N':>6} {elapsed:>6.1f}")

        # Verify formula
        if nv >= 5:
            exp_good = nv * nv - 2 * nv + 8
            if n_good != exp_good:
                print(f"    good formula mismatch: {n_good} vs {exp_good}")

    # Compare tiebreakers for n=5..10
    print("\n\nTIEBREAKER COMPARISON")
    print("-" * 60)
    for nv in range(5, 11):
        _, fs0, comp0, _, _, _, _, lfx0 = build_system(nv, fixed_tiebreaker=False)
        _, fs1, comp1, _, _, _, _, lfx1 = build_system(nv, fixed_tiebreaker=True)
        # Count differences
        diff = sum(1 for k in comp0 if comp0[k] != comp1[k])
        priv0 = sum(1 for k in comp0 if comp0[k] != k[2])
        priv1 = sum(1 for k in comp1 if comp1[k] != k[2])
        print(f"  n={nv}: diffs={diff}, priv_orig={priv0}, priv_fixed={priv1}, "
              f"lfx_orig={lfx0}, lfx_fixed={lfx1}")


if __name__ == "__main__":
    main()
