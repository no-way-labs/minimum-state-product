#!/usr/bin/env python3
"""n9_targeted_search.py — Phase 2: constraint-guided search for (3,3,3) table.

Key insight: setting f(L,S,R) = S for unconstrained triples maximizes
single-priv configs. Only 6 triples are liveness-constrained (f ≠ S),
giving 2^6 = 64 minimal candidates. If those fail, gradually add
privileged entries.

Falls back to Z3-based search if structural approaches fail.
"""

import sys
import time
from itertools import product as cartesian
from collections import Counter, defaultdict

# ── verifier ─────────────────────────────────────────────────────────

def verify(name, state_counts, rules, verbose=True):
    n = len(state_counts)
    P = 1
    for m in state_counts:
        P *= m
    configs = list(cartesian(*(range(m) for m in state_counts)))

    def privileged(cfg):
        priv = []
        for i in range(n):
            L = cfg[(i-1)%n]; S = cfg[i]; R = cfg[(i+1)%n]
            if rules[i][(L,S,R)] != S:
                priv.append(i)
        return priv

    def move(cfg, proc):
        L = cfg[(proc-1)%n]; S = cfg[proc]; R = cfg[(proc+1)%n]
        new_S = rules[proc][(L,S,R)]
        lst = list(cfg); lst[proc] = new_S
        return tuple(lst)

    for cfg in configs:
        if not privileged(cfg):
            if verbose: print(f"  FAIL liveness: {cfg}")
            return False

    single_priv = {}
    for cfg in configs:
        priv = privileged(cfg)
        if len(priv) == 1:
            nxt = move(cfg, priv[0])
            single_priv[cfg] = (nxt, priv[0])

    good_cycle = None
    visited_global = set()
    for start in single_priv:
        if start in visited_global:
            continue
        path = []; movers = []; visited = set(); cur = start
        while cur in single_priv and cur not in visited:
            visited.add(cur); visited_global.add(cur)
            path.append(cur)
            nxt, mover = single_priv[cur]
            movers.append(mover); cur = nxt
        if cur == start and len(path) > 0:
            good_cycle = path; good_movers = movers; break

    if good_cycle is None:
        if verbose: print(f"  FAIL: no good cycle (single_priv={len(single_priv)})")
        return False

    good_set = set(good_cycle)

    bad_set = set(configs) - good_set
    changed = True
    while changed:
        changed = False
        to_remove = set()
        for cfg in bad_set:
            priv = privileged(cfg)
            all_exit = True
            for p in priv:
                nxt = move(cfg, p)
                if nxt in bad_set:
                    all_exit = False; break
            if all_exit: to_remove.add(cfg)
        if to_remove:
            bad_set -= to_remove; changed = True

    if bad_set:
        if verbose: print(f"  FAIL convergence: {len(bad_set)} bad in cycles")
        return False

    movers_seen = set(good_movers)
    if movers_seen != set(range(n)):
        if verbose:
            missing = set(range(n)) - movers_seen
            print(f"  FAIL fairness: {missing} never move")
        return False

    if verbose:
        print(f"  PASS  product={P}  cycle={len(good_cycle)}  "
              f"configs={len(configs)}  bad={len(configs)-len(good_cycle)}")
    return True


# ── n=8 witness ──────────────────────────────────────────────────────

def witness_n8():
    return (2, 2, 3, 4, 3, 3, 2, 3), (
        {(0,0,0):1,(0,0,1):0,(0,1,0):1,(0,1,1):1,(1,0,0):0,(1,0,1):0,(1,1,0):1,(1,1,1):1,(2,0,0):0,(2,0,1):0,(2,1,0):0,(2,1,1):0},
        {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):0,(0,1,2):0,(1,0,0):1,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):0,(1,1,2):1},
        {(0,0,0):0,(0,0,1):1,(0,0,2):0,(0,0,3):0,(0,1,0):2,(0,1,1):1,(0,1,2):0,(0,1,3):0,(0,2,0):2,(0,2,1):1,(0,2,2):2,(0,2,3):1,(1,0,0):1,(1,0,1):0,(1,0,2):2,(1,0,3):0,(1,1,0):1,(1,1,1):0,(1,1,2):2,(1,1,3):0,(1,2,0):2,(1,2,1):0,(1,2,2):2,(1,2,3):0},
        {(0,0,0):0,(0,0,1):0,(0,0,2):3,(0,1,0):3,(0,1,1):1,(0,1,2):1,(0,2,0):2,(0,2,1):0,(0,2,2):0,(0,3,0):3,(0,3,1):0,(0,3,2):1,(1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):2,(1,1,1):3,(1,1,2):0,(1,2,0):2,(1,2,1):0,(1,2,2):0,(1,3,0):0,(1,3,1):3,(1,3,2):0,(2,0,0):1,(2,0,1):2,(2,0,2):0,(2,1,0):1,(2,1,1):0,(2,1,2):0,(2,2,0):0,(2,2,1):2,(2,2,2):2,(2,3,0):0,(2,3,1):0,(2,3,2):1},
        {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):1,(0,1,1):0,(0,1,2):0,(0,2,0):0,(0,2,1):0,(0,2,2):0,(1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):1,(1,2,0):0,(1,2,1):1,(1,2,2):1,(2,0,0):0,(2,0,1):0,(2,0,2):0,(2,1,0):2,(2,1,1):0,(2,1,2):0,(2,2,0):2,(2,2,1):0,(2,2,2):0,(3,0,0):1,(3,0,1):2,(3,0,2):0,(3,1,0):1,(3,1,1):1,(3,1,2):1,(3,2,0):0,(3,2,1):2,(3,2,2):0},
        {(0,0,0):0,(0,0,1):0,(0,1,0):1,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):0,(1,0,1):0,(1,1,0):2,(1,1,1):0,(1,2,0):2,(1,2,1):2,(2,0,0):1,(2,0,1):0,(2,1,0):1,(2,1,1):1,(2,2,0):0,(2,2,1):0},
        {(0,0,0):0,(0,0,1):0,(0,0,2):1,(0,1,0):0,(0,1,1):0,(0,1,2):1,(1,0,0):0,(1,0,1):0,(1,0,2):1,(1,1,0):0,(1,1,1):1,(1,1,2):1,(2,0,0):1,(2,0,1):0,(2,0,2):0,(2,1,0):1,(2,1,1):0,(2,1,2):0},
        {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):2,(0,2,0):2,(0,2,1):2,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(1,2,0):1,(1,2,1):2},
    )


def build_n9(p5_table):
    """Build n=9 ring (2,2,3,4,3,T,3,2,3) from n=8 + P5 table."""
    _, r8 = witness_n8()
    return (2,2,3,4,3,3,3,2,3), [r8[0],r8[1],r8[2],r8[3],r8[4], p5_table, r8[5],r8[6],r8[7]]


# ── constraint analysis ──────────────────────────────────────────────

def analyze_constraints():
    """Compute fixed-privilege stats for each P5 triple."""
    sc9 = (2,2,3,4,3,3,3,2,3)
    _, r8 = witness_n8()
    rules_fixed = [r8[0],r8[1],r8[2],r8[3],r8[4], None, r8[5],r8[6],r8[7]]

    # For each config, compute fixed privilege count and P5 triple
    triple_stats = defaultdict(lambda: {'fp0': [], 'fp1': [], 'fp2plus': []})
    all_configs = list(cartesian(*(range(m) for m in sc9)))

    for cfg in all_configs:
        fp = []
        for i in range(9):
            if i == 5: continue
            L = cfg[(i-1)%9]; S = cfg[i]; R = cfg[(i+1)%9]
            if rules_fixed[i][(L,S,R)] != S:
                fp.append(i)

        L5 = cfg[4]; S5 = cfg[5]; R5 = cfg[6]
        triple = (L5, S5, R5)
        if len(fp) == 0:
            triple_stats[triple]['fp0'].append(cfg)
        elif len(fp) == 1:
            triple_stats[triple]['fp1'].append((cfg, fp[0]))
        else:
            triple_stats[triple]['fp2plus'].append(cfg)

    return triple_stats, all_configs


def main():
    print("=" * 70)
    print("n=9 Targeted Search: Constraint Analysis + Minimal Candidates")
    print("=" * 70)

    triple_stats, all_configs = analyze_constraints()

    # Classify triples
    constrained = []   # must have f ≠ S
    unconstrained = [] # can have f = S
    for triple in sorted(triple_stats.keys()):
        s = triple_stats[triple]
        if len(s['fp0']) > 0:
            constrained.append(triple)
        else:
            unconstrained.append(triple)

    print(f"\nConstrained triples (must have f ≠ S): {len(constrained)}")
    for t in constrained:
        s = triple_stats[t]
        print(f"  ({t[0]},{t[1]},{t[2]}): {len(s['fp0'])} need-P5 configs, "
              f"{len(s['fp1'])} single-fixed, {len(s['fp2plus'])} multi-fixed")
    print(f"\nUnconstrained triples: {len(unconstrained)}")

    # Check P5 state coverage in constrained triples
    constrained_S = set(t[1] for t in constrained)
    print(f"\nP5 states in constrained triples: {sorted(constrained_S)}")
    if constrained_S == {0,1,2}:
        print("All 3 P5 states covered — P5 can cycle through all states ✓")
    else:
        print(f"MISSING states {set(range(3)) - constrained_S} — P5 may not cycle properly")

    # ── Phase A: 64 minimal candidates ──
    print(f"\n{'='*70}")
    print(f"Phase A: 64 minimal candidates (f=S for unconstrained, 2^6 for constrained)")
    print(f"{'='*70}")

    # For each constrained triple (L,S,R), the 2 options for f are the values ≠ S
    triple_options = {}
    for t in constrained:
        S = t[1]
        triple_options[t] = [v for v in range(3) if v != S]

    best_result = None
    t0 = time.time()

    for trial in range(64):
        # Build table: unconstrained entries = S, constrained = choice
        table = {}
        bits = trial
        for t in constrained:
            opts = triple_options[t]
            choice = opts[bits & 1]
            bits >>= 1
            for R in range(3):
                # Only set for the specific R in the triple
                pass
            table[t] = choice

        # Build full 27-entry table
        full_table = {}
        for L in range(3):
            for S in range(3):
                for R in range(3):
                    t = (L,S,R)
                    if t in table:
                        full_table[t] = table[t]
                    else:
                        full_table[t] = S  # unprivileged

        sc9, rules9 = build_n9(full_table)
        result = verify(f"minimal-{trial}", sc9, rules9, verbose=False)
        if result:
            elapsed = time.time() - t0
            print(f"\n*** SUCCESS at trial {trial}! ({elapsed:.2f}s) ***")
            print(f"Table: {full_table}")
            verify(f"n=9 WITNESS", sc9, rules9, verbose=True)
            return full_table

    elapsed = time.time() - t0
    print(f"Phase A: 0/64 passed ({elapsed:.2f}s)")

    # ── Diagnostic: check WHY minimal fails ──
    print(f"\n{'='*70}")
    print("Diagnostic: failure modes for minimal candidates")
    print(f"{'='*70}")

    # Check a few candidates with verbose
    for trial in [0, 1, 7, 63]:
        table = {}
        bits = trial
        for t in constrained:
            opts = triple_options[t]
            choice = opts[bits & 1]
            bits >>= 1
            table[t] = choice
        full_table = {}
        for L in range(3):
            for S in range(3):
                for R in range(3):
                    t = (L,S,R)
                    full_table[t] = table.get(t, S)

        sc9, rules9 = build_n9(full_table)
        print(f"\nTrial {trial}:")
        verify(f"minimal-{trial}", sc9, rules9, verbose=True)

    # ── Phase B: Extend with 1-2 extra privileged triples ──
    print(f"\n{'='*70}")
    print("Phase B: Add 1 extra privileged triple")
    print(f"{'='*70}")
    t0 = time.time()
    total_tried = 0
    for extra_t in unconstrained:
        extra_S = extra_t[1]
        for extra_v in [v for v in range(3) if v != extra_S]:
            for trial in range(64):
                table = {}
                bits = trial
                for t in constrained:
                    opts = triple_options[t]
                    choice = opts[bits & 1]
                    bits >>= 1
                    table[t] = choice
                table[extra_t] = extra_v

                full_table = {}
                for L in range(3):
                    for S in range(3):
                        for R in range(3):
                            t = (L,S,R)
                            full_table[t] = table.get(t, S)

                sc9, rules9 = build_n9(full_table)
                total_tried += 1
                result = verify(f"ext1-{total_tried}", sc9, rules9, verbose=False)
                if result:
                    elapsed = time.time() - t0
                    print(f"\n*** SUCCESS! Extra triple {extra_t}={extra_v}, "
                          f"trial {trial} ({elapsed:.2f}s, {total_tried} tried) ***")
                    verify(f"n=9 WITNESS", sc9, rules9, verbose=True)
                    print(f"\nFull P5 table:")
                    for L in range(3):
                        for S in range(3):
                            row = [full_table[(L,S,R)] for R in range(3)]
                            print(f"  f({L},{S},*) = {row}")
                    return full_table

    elapsed = time.time() - t0
    print(f"Phase B: 0/{total_tried} passed ({elapsed:.2f}s)")

    # ── Phase C: Add 2 extra privileged triples ──
    print(f"\n{'='*70}")
    print("Phase C: Add 2 extra privileged triples")
    print(f"{'='*70}")
    t0 = time.time()
    total_tried = 0

    for i, t1 in enumerate(unconstrained):
        for t2 in unconstrained[i+1:]:
            for v1 in [v for v in range(3) if v != t1[1]]:
                for v2 in [v for v in range(3) if v != t2[1]]:
                    for trial in range(64):
                        table = {}
                        bits = trial
                        for t in constrained:
                            opts = triple_options[t]
                            choice = opts[bits & 1]
                            bits >>= 1
                            table[t] = choice
                        table[t1] = v1
                        table[t2] = v2

                        full_table = {}
                        for L in range(3):
                            for S in range(3):
                                for R in range(3):
                                    t = (L,S,R)
                                    full_table[t] = table.get(t, S)

                        sc9, rules9 = build_n9(full_table)
                        total_tried += 1
                        result = verify(f"ext2-{total_tried}", sc9, rules9, verbose=False)
                        if result:
                            elapsed = time.time() - t0
                            print(f"\n*** SUCCESS! Extras {t1}={v1}, {t2}={v2}, "
                                  f"trial {trial} ({elapsed:.2f}s, {total_tried} tried) ***")
                            verify(f"n=9 WITNESS", sc9, rules9, verbose=True)
                            print(f"\nFull P5 table:")
                            for L in range(3):
                                for S in range(3):
                                    row = [full_table[(L,S,R)] for R in range(3)]
                                    print(f"  f({L},{S},*) = {row}")
                            return full_table

    elapsed = time.time() - t0
    print(f"Phase C: 0/{total_tried} passed ({elapsed:.2f}s)")

    # ── Phase D: Z3-based search ──
    print(f"\n{'='*70}")
    print("Phase D: Z3-based search over all 27 entries")
    print(f"{'='*70}")
    try:
        return z3_search()
    except Exception as e:
        print(f"Z3 search failed: {e}")
        return None


def z3_search():
    """Use Z3 to find a P5 table satisfying liveness + good cycle existence."""
    import z3

    sc9 = (2,2,3,4,3,3,3,2,3)
    _, r8 = witness_n8()
    rules_fixed = [r8[0],r8[1],r8[2],r8[3],r8[4], None, r8[5],r8[6],r8[7]]

    # Create Z3 variables for P5's 27 table entries
    f = {}
    for L in range(3):
        for S in range(3):
            for R in range(3):
                f[(L,S,R)] = z3.Int(f'f_{L}_{S}_{R}')

    solver = z3.Solver()
    solver.set("timeout", 300000)  # 5 minutes

    # Range constraints
    for key, var in f.items():
        solver.add(var >= 0, var < 3)

    # Liveness constraints
    all_configs = list(cartesian(*(range(m) for m in sc9)))
    n_liveness = 0
    for cfg in all_configs:
        fp = []
        for i in range(9):
            if i == 5: continue
            Li = cfg[(i-1)%9]; Si = cfg[i]; Ri = cfg[(i+1)%9]
            if rules_fixed[i][(Li,Si,Ri)] != Si:
                fp.append(i)
        if len(fp) == 0:
            # P5 must be privileged
            L5 = cfg[4]; S5 = cfg[5]; R5 = cfg[6]
            solver.add(f[(L5,S5,R5)] != S5)
            n_liveness += 1

    print(f"  Added {n_liveness} liveness constraints")

    # Structural constraint: the system must have a good cycle of length >= 10
    # that visits all 9 processors.
    # This is hard to encode directly. Instead, we'll use an iterative approach:
    # 1. Find any satisfying assignment
    # 2. Build the system and check with verify()
    # 3. If it fails, add constraints to exclude this assignment and retry

    max_iterations = 10000
    found = 0
    t0 = time.time()

    for iteration in range(max_iterations):
        result = solver.check()
        if result == z3.unsat:
            print(f"  Z3: UNSAT after {iteration} iterations")
            break
        if result == z3.unknown:
            print(f"  Z3: UNKNOWN (timeout?) after {iteration} iterations")
            break

        model = solver.model()
        # Extract table
        table = {}
        for key, var in f.items():
            table[key] = model[var].as_long()

        sc9_full, rules9 = build_n9(table)
        ok = verify(f"z3-{iteration}", sc9_full, rules9, verbose=False)

        if ok:
            found += 1
            elapsed = time.time() - t0
            print(f"\n*** Z3 SUCCESS at iteration {iteration}! ({elapsed:.2f}s) ***")
            verify(f"n=9 WITNESS", sc9_full, rules9, verbose=True)
            print(f"\nFull P5 table:")
            for L in range(3):
                for S in range(3):
                    row = [table[(L,S,R)] for R in range(3)]
                    print(f"  f({L},{S},*) = {row}")
            return table

        # Add constraint to exclude this exact table
        exclude = z3.Or([f[key] != table[key] for key in f])
        solver.add(exclude)

        if iteration % 100 == 0 and iteration > 0:
            elapsed = time.time() - t0
            print(f"  Z3: {iteration} iterations, {elapsed:.1f}s")

    elapsed = time.time() - t0
    print(f"  Z3: exhausted {max_iterations} iterations, no valid witness ({elapsed:.1f}s)")
    return None


if __name__ == "__main__":
    result = main()
    if result is None:
        print("\nNo valid n=9 witness found.")
    else:
        print("\nWitness found successfully!")
