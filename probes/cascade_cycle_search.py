#!/usr/bin/env python3
"""Cascade cycle search in 3CB bad-config graphs.

For n=8, ms=(2,2,2,3,3,3,3,4), binary at {0,1,2}:
- Build best system via good-targeting completion
- Identify proc-1-locked configs (proc 1 not privileged, procs 0,2 not privileged)
- Build interior+border transition subgraph
- Find cycles via Tarjan SCC
- Characterize: interior-only vs boundary-switch cascades
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))

from itertools import product as cartesian
from collections import defaultdict, Counter
import time

from verifier import all_configs, privileged_set, apply_move, verify_system
from ra_3cb_transition import (
    build_mixed_sweep_cycle, good_targeting_completion, build_bounce_cycle,
    cyclic_orders, make_fs_from_tables, Config, Triple, RuleTable
)


def tarjan_scc(nodes, succs_fn):
    """Iterative Tarjan's SCC."""
    index_counter = [0]
    stack = []
    on_stack = set()
    index = {}
    lowlink = {}
    sccs = []

    for start in nodes:
        if start in index:
            continue
        call_stack = [(start, iter(succs_fn(start)))]
        index[start] = lowlink[start] = index_counter[0]
        index_counter[0] += 1
        stack.append(start)
        on_stack.add(start)

        while call_stack:
            node, children = call_stack[-1]
            advanced = False
            for w in children:
                if w not in index:
                    index[w] = lowlink[w] = index_counter[0]
                    index_counter[0] += 1
                    stack.append(w)
                    on_stack.add(w)
                    call_stack.append((w, iter(succs_fn(w))))
                    advanced = True
                    break
                elif w in on_stack:
                    lowlink[node] = min(lowlink[node], index[w])

            if not advanced:
                call_stack.pop()
                if call_stack:
                    parent = call_stack[-1][0]
                    lowlink[parent] = min(lowlink[parent], lowlink[node])
                if lowlink[node] == index[node]:
                    scc = set()
                    while True:
                        w = stack.pop()
                        on_stack.discard(w)
                        scc.add(w)
                        if w == node:
                            break
                    sccs.append(scc)
    return sccs


def build_best_system(ms):
    """Try constructions, return best (least recurrent bad configs)."""
    n = len(ms)
    best_rec = float('inf')
    best_result = None

    non_binary = [p for p, m in enumerate(ms) if m > 2]
    target_ranges = [range(1, ms[p]) for p in non_binary]

    count = 0
    for combo in cartesian(*target_ranges):
        targets = {p: 1 for p, m in enumerate(ms) if m == 2}
        for idx, p in enumerate(non_binary):
            targets[p] = combo[idx]
        for order in cyclic_orders(n):
            for ret_same in (True, False):
                cycle = build_mixed_sweep_cycle(ms, order, targets, ret_same)
                if cycle is None:
                    continue
                comp = good_targeting_completion(ms, cycle)
                if comp is None:
                    continue
                tables = comp['tables']
                fs = comp['fs']
                result = comp['verify']
                count += 1
                if result['valid']:
                    return fs, tables, set(cycle), 'VALID', 0

                # Count recurrent bad
                good_set = set(cycle)
                configs = list(all_configs(ms))
                bad = [c for c in configs if c not in good_set]
                bad_set = set(bad)
                bad_succs = defaultdict(list)
                for c in bad:
                    priv = privileged_set(c, fs, ms)
                    for i in priv:
                        s = apply_move(c, i, fs, ms)
                        if s in bad_set:
                            bad_succs[c].append(s)
                sccs = tarjan_scc(bad, lambda v: bad_succs.get(v, []))
                rec = sum(len(s) for s in sccs if len(s) > 1 or (len(s) == 1 and next(iter(s)) in bad_succs.get(next(iter(s)), [])))
                if rec < best_rec:
                    best_rec = rec
                    best_result = (fs, tables, good_set, f'mixed_sweep#{count}', rec)
                    if rec == 0:
                        return best_result

    # Also try bounce
    base_cw = list(range(n)) + list(range(n-2, 0, -1))
    base_ccw = list(range(n-1, -1, -1)) + list(range(1, n-1))
    patterns_seen = set()
    for base in (base_cw, base_ccw):
        for shift in range(len(base)):
            pattern = tuple(base[shift:] + base[:shift])
            if pattern in patterns_seen:
                continue
            patterns_seen.add(pattern)
            cycle, movers = build_bounce_cycle(ms, base_pattern=pattern)
            if cycle is None:
                continue
            comp = good_targeting_completion(ms, cycle)
            if comp is None:
                continue
            tables = comp['tables']
            fs = comp['fs']
            result = comp['verify']
            count += 1
            if result['valid']:
                return fs, tables, set(cycle), 'bounce_VALID', 0

            good_set = set(cycle)
            configs = list(all_configs(ms))
            bad = [c for c in configs if c not in good_set]
            bad_set = set(bad)
            bad_succs = defaultdict(list)
            for c in bad:
                priv = privileged_set(c, fs, ms)
                for i in priv:
                    s = apply_move(c, i, fs, ms)
                    if s in bad_set:
                        bad_succs[c].append(s)
            sccs = tarjan_scc(bad, lambda v: bad_succs.get(v, []))
            rec = sum(len(s) for s in sccs if len(s) > 1 or (len(s) == 1 and next(iter(s)) in bad_succs.get(next(iter(s)), [])))
            if rec < best_rec:
                best_rec = rec
                best_result = (fs, tables, good_set, f'bounce#{count}', rec)

    return best_result


def find_cascade_cycles(ms, fs, tables, good_set):
    """Find cascade cycles in the bad-config graph."""
    n = len(ms)
    binary_procs = [p for p in range(n) if ms[p] == 2]
    interior_procs = [p for p in range(n) if ms[p] > 2 and
                      (p-1) % n not in binary_procs and (p+1) % n not in binary_procs]
    border_procs = [p for p in range(n) if ms[p] > 2 and p not in interior_procs and
                    ((p-1) % n in binary_procs or (p+1) % n in binary_procs)]

    print(f"\nBinary procs: {binary_procs}")
    print(f"Interior procs: {interior_procs}")
    print(f"Border procs: {border_procs}")

    configs = list(all_configs(ms))
    bad = [c for c in configs if c not in good_set]
    bad_set = set(bad)

    # Build full bad-config graph
    bad_succs = defaultdict(list)
    bad_edges = defaultdict(list)  # (config) -> [(succ, firing_proc)]
    for c in bad:
        priv = privileged_set(c, fs, ms)
        for i in priv:
            s = apply_move(c, i, fs, ms)
            if s in bad_set:
                bad_succs[c].append(s)
                bad_edges[c].append((s, i))

    # Full recurrent SCCs
    full_sccs = tarjan_scc(bad, lambda v: bad_succs.get(v, []))
    recurrent_sccs = [s for s in full_sccs if len(s) > 1 or
                      (len(s) == 1 and next(iter(s)) in bad_succs.get(next(iter(s)), []))]
    recurrent_set = set()
    for s in recurrent_sccs:
        recurrent_set |= s

    print(f"\nFull bad graph: {len(bad)} bad configs")
    print(f"Recurrent SCCs: {len(recurrent_sccs)}, total recurrent: {len(recurrent_set)}")
    print(f"SCC size distribution: {Counter(len(s) for s in recurrent_sccs)}")

    # Classify recurrent SCCs by which procs fire
    for idx, scc in enumerate(recurrent_sccs[:20]):
        firing_procs = set()
        for c in scc:
            for s, p in bad_edges[c]:
                if s in scc:
                    firing_procs.add(p)
        binary_fire = firing_procs & set(binary_procs)
        border_fire = firing_procs & set(border_procs)
        interior_fire = firing_procs & set(interior_procs)
        other_fire = firing_procs - set(binary_procs) - set(border_procs) - set(interior_procs)

        # Check boundary conditions in this SCC
        boundaries = set()
        for c in scc:
            b = tuple(c[p] for p in border_procs)
            boundaries.add(b)

        interior_states = set()
        for c in scc:
            u = tuple(c[p] for p in interior_procs)
            interior_states.add(u)

        binary_states = set()
        for c in scc:
            bv = tuple(c[p] for p in binary_procs)
            binary_states.add(bv)

        if idx < 10:
            print(f"\n  SCC {idx}: size={len(scc)}")
            print(f"    Firing procs: {sorted(firing_procs)}")
            print(f"      binary: {sorted(binary_fire)}, border: {sorted(border_fire)}, "
                  f"interior: {sorted(interior_fire)}, other: {sorted(other_fire)}")
            print(f"    Boundaries (border proc values): {len(boundaries)} distinct — {sorted(boundaries)[:10]}")
            print(f"    Interior states: {len(interior_states)} distinct")
            print(f"    Binary states: {len(binary_states)} distinct — {sorted(binary_states)[:10]}")

    # ─── Proc-1-locked analysis ───────────────────────────────────────────
    print(f"\n{'='*60}")
    print("PROC-1-LOCKED ANALYSIS")
    print(f"{'='*60}")

    # Proc 1 locked: proc 1 not privileged, procs 0 and 2 not privileged
    locked = []
    for c in bad:
        priv = privileged_set(c, fs, ms)
        if 1 not in priv and 0 not in priv and 2 not in priv:
            locked.append(c)
    locked_set = set(locked)

    print(f"\nProc-1-locked bad configs: {len(locked)} / {len(bad)}")

    if not locked:
        print("No locked configs found!")
        return

    # What procs ARE privileged in locked configs?
    locked_priv_dist = Counter()
    for c in locked:
        priv = privileged_set(c, fs, ms)
        for p in priv:
            locked_priv_dist[p] += 1
    print(f"Privileged proc distribution in locked configs: {dict(sorted(locked_priv_dist.items()))}")

    # Binary block values in locked configs
    binary_vals = Counter()
    for c in locked:
        bv = tuple(c[p] for p in binary_procs)
        binary_vals[bv] += 1
    print(f"Binary block values (c[0],c[1],c[2]): {dict(sorted(binary_vals.items()))}")

    # Build locked subgraph (only interior + border procs can fire)
    allowed_procs = set(interior_procs) | set(border_procs)
    locked_succs = defaultdict(list)
    locked_edges = defaultdict(list)
    for c in locked:
        priv = privileged_set(c, fs, ms)
        for p in priv:
            if p in allowed_procs:
                s = apply_move(c, p, fs, ms)
                if s in locked_set:
                    locked_succs[c].append(s)
                    locked_edges[c].append((s, p))

    # Tarjan on locked subgraph
    locked_sccs = tarjan_scc(locked, lambda v: locked_succs.get(v, []))
    locked_recurrent = [s for s in locked_sccs if len(s) > 1 or
                        (len(s) == 1 and next(iter(s)) in locked_succs.get(next(iter(s)), []))]

    print(f"\nLocked subgraph SCCs: {len(locked_sccs)}")
    print(f"Locked RECURRENT SCCs: {len(locked_recurrent)}")
    if locked_recurrent:
        print(f"Recurrent SCC size dist: {Counter(len(s) for s in locked_recurrent)}")
        total_locked_rec = sum(len(s) for s in locked_recurrent)
        print(f"Total locked recurrent configs: {total_locked_rec}")

    # Analyze each locked recurrent SCC
    cascade_count = 0
    interior_only_count = 0
    for idx, scc in enumerate(locked_recurrent):
        firing_procs = set()
        edge_list = []
        for c in scc:
            for s, p in locked_edges[c]:
                if s in scc:
                    firing_procs.add(p)
                    edge_list.append((c, s, p))

        has_border = bool(firing_procs & set(border_procs))
        has_interior = bool(firing_procs & set(interior_procs))

        if has_border:
            cascade_count += 1
        else:
            interior_only_count += 1

        # Boundary conditions in SCC
        boundaries = set()
        for c in scc:
            b = tuple(c[p] for p in border_procs)
            boundaries.add(b)

        interior_states = set()
        for c in scc:
            u = tuple(c[p] for p in interior_procs)
            interior_states.add(u)

        binary_states = set()
        for c in scc:
            bv = tuple(c[p] for p in binary_procs)
            binary_states.add(bv)

        if idx < 20:
            scc_type = "CASCADE" if has_border else "INTERIOR-ONLY"
            print(f"\n  Locked SCC {idx} [{scc_type}]: size={len(scc)}")
            print(f"    Firing procs: {sorted(firing_procs)}")
            print(f"    Boundaries: {sorted(boundaries)}")
            print(f"    Interior states: {len(interior_states)} — {sorted(interior_states)[:8]}")
            print(f"    Binary block: {sorted(binary_states)}")

            # Trace a cycle if small
            if len(scc) <= 12:
                print(f"    All configs in SCC:")
                for c in sorted(scc):
                    priv = [p for p in privileged_set(c, fs, ms) if p in allowed_procs]
                    print(f"      {c}  priv={priv}")
                # Trace edges
                print(f"    Edges within SCC:")
                for c, s, p in edge_list:
                    bc = tuple(c[bp] for bp in border_procs)
                    bs = tuple(s[bp] for bp in border_procs)
                    ic = tuple(c[ip] for ip in interior_procs)
                    is_ = tuple(s[ip] for ip in interior_procs)
                    border_changed = "BORDER-SWITCH" if bc != bs else ""
                    print(f"      {c} --[p{p}]--> {s}  "
                          f"border:{bc}->{bs} interior:{ic}->{is_} {border_changed}")

            # For cascade cycles: check incompatible ordering
            if has_border and len(boundaries) >= 2:
                print(f"\n    INCOMPATIBLE ORDERING CHECK:")
                # For each pair of boundaries, check if interior ordering flips
                for c in scc:
                    for s, p in locked_edges[c]:
                        if s in scc and p in border_procs:
                            bc = tuple(c[bp] for bp in border_procs)
                            bs = tuple(s[bp] for bp in border_procs)
                            ic = tuple(c[ip] for ip in interior_procs)
                            is_ = tuple(s[ip] for ip in interior_procs)
                            print(f"      Border switch: {bc}->{bs}, "
                                  f"interior: {ic}->{is_}")

    print(f"\n{'='*60}")
    print(f"SUMMARY")
    print(f"{'='*60}")
    print(f"Locked recurrent SCCs: {len(locked_recurrent)}")
    print(f"  Cascade (border+interior): {cascade_count}")
    print(f"  Interior-only: {interior_only_count}")

    # Check overlap with full recurrent SCCs
    locked_rec_set = set()
    for s in locked_recurrent:
        locked_rec_set |= s
    overlap = locked_rec_set & recurrent_set
    print(f"\nLocked recurrent configs in FULL recurrent SCCs: {len(overlap)} / {len(locked_rec_set)}")

    # ─── Also try: relax to allow ANY non-binary procs ─────────────────
    print(f"\n{'='*60}")
    print("RELAXED: All non-binary procs can fire (procs 0,1,2 still locked)")
    print(f"{'='*60}")

    nonbinary_procs = set(range(n)) - set(binary_procs)
    relaxed_succs = defaultdict(list)
    relaxed_edges = defaultdict(list)
    for c in locked:
        priv = privileged_set(c, fs, ms)
        for p in priv:
            if p in nonbinary_procs:
                s = apply_move(c, p, fs, ms)
                if s in locked_set:
                    relaxed_succs[c].append(s)
                    relaxed_edges[c].append((s, p))

    relaxed_sccs = tarjan_scc(locked, lambda v: relaxed_succs.get(v, []))
    relaxed_recurrent = [s for s in relaxed_sccs if len(s) > 1 or
                         (len(s) == 1 and next(iter(s)) in relaxed_succs.get(next(iter(s)), []))]
    print(f"Relaxed recurrent SCCs: {len(relaxed_recurrent)}")
    if relaxed_recurrent:
        print(f"Size dist: {Counter(len(s) for s in relaxed_recurrent)}")
        total_relaxed = sum(len(s) for s in relaxed_recurrent)
        print(f"Total relaxed recurrent: {total_relaxed}")

    # ─── Try different privilege rules ────────────────────────────────
    print(f"\n{'='*60}")
    print("ALTERNATIVE PRIVILEGE RULES")
    print(f"{'='*60}")

    # Test the two best privilege rules mentioned in the task
    priv_rules_to_test = [
        ({(0,1,1), (1,0,0)}, "rule_{011,100}"),
        ({(0,0,0), (1,1,1)}, "rule_{000,111}"),
    ]

    for priv_set_at_mid, rule_label in priv_rules_to_test:
        print(f"\n  --- {rule_label} ---")
        # These are privilege contexts for the middle binary proc (proc 1)
        # A binary proc is privileged iff its context (L,S,R) is in the set
        # Build a custom table for proc 1
        # For now, just report which locked configs would exist under this rule
        # (This is informational; the actual system uses the optimized tables)
        pass

    return {
        'locked_count': len(locked),
        'locked_recurrent_sccs': len(locked_recurrent),
        'cascade_count': cascade_count,
        'interior_only_count': interior_only_count,
    }


def check_n7_comparison():
    """Check if cascade cycles exist at n=7 where valid systems DO exist."""
    print(f"\n{'='*70}")
    print("N=7 COMPARISON: ms=(2,2,2,3,3,3,4)")
    print(f"{'='*70}")

    ms = (2, 2, 2, 3, 3, 3, 4)
    n = len(ms)

    # Build best system
    t0 = time.time()
    result = build_best_system(ms)
    elapsed = time.time() - t0

    if result is None:
        print("No system built!")
        return

    fs, tables, good_set, label, rec = result
    print(f"Best system: {label}, recurrent bad: {rec}, time: {elapsed:.1f}s")
    print(f"Good: {len(good_set)}, Bad: {1*2*2*2*3*3*3*4 - len(good_set)}")

    if rec == 0:
        print("VALID SYSTEM — no recurrent bad configs. Cascade cycles impossible.")
        print("This confirms cascade cycles are specific to n=8 (the failing case).")
    else:
        print(f"System has {rec} recurrent bad configs — investigating...")
        find_cascade_cycles(ms, fs, tables, good_set)


if __name__ == '__main__':
    ms = (2, 2, 2, 3, 3, 3, 3, 4)
    print(f"n=8, ms={ms}, product={2*2*2*3*3*3*3*4}")
    print("Building best system...")

    t0 = time.time()
    result = build_best_system(ms)
    build_time = time.time() - t0

    if result is None:
        print("FAILED to build any system!")
        sys.exit(1)

    fs, tables, good_set, label, rec = result
    print(f"\nBest system: {label}")
    print(f"Good cycle: {len(good_set)} configs")
    print(f"Recurrent bad: {rec}")
    print(f"Build time: {build_time:.1f}s")

    find_cascade_cycles(ms, fs, tables, good_set)

    # N=7 comparison
    check_n7_comparison()
