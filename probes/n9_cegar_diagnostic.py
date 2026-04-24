#!/usr/bin/env python3
"""
N=9 CEGAR Diagnostic: Determine if frozen-P0-P6 orientation is infeasible.

Key question: When the Z3 search fails, are the cycles composed entirely
of P0-P6 moves (fixed procs)? If so, no P7/P8 assignment can help.
"""

from itertools import product as iproduct
from collections import Counter, defaultdict
import time


# ═══════════════════════════════════════════════════════════════════
# N=8 WITNESS
# ═══════════════════════════════════════════════════════════════════

def witness_n8():
    ms = (2, 2, 3, 4, 3, 3, 2, 3)
    rules = [
        {(0,0,0):1,(0,0,1):0,(0,1,0):1,(0,1,1):1,(1,0,0):0,(1,0,1):0,(1,1,0):1,(1,1,1):1,(2,0,0):0,(2,0,1):0,(2,1,0):0,(2,1,1):0},
        {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):0,(0,1,2):0,(1,0,0):1,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):0,(1,1,2):1},
        {(0,0,0):0,(0,0,1):1,(0,0,2):0,(0,0,3):0,(0,1,0):2,(0,1,1):1,(0,1,2):0,(0,1,3):0,(0,2,0):2,(0,2,1):1,(0,2,2):2,(0,2,3):1,(1,0,0):1,(1,0,1):0,(1,0,2):2,(1,0,3):0,(1,1,0):1,(1,1,1):0,(1,1,2):2,(1,1,3):0,(1,2,0):2,(1,2,1):0,(1,2,2):2,(1,2,3):0},
        {(0,0,0):0,(0,0,1):0,(0,0,2):3,(0,1,0):3,(0,1,1):1,(0,1,2):1,(0,2,0):2,(0,2,1):0,(0,2,2):0,(0,3,0):3,(0,3,1):0,(0,3,2):1,(1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):2,(1,1,1):3,(1,1,2):0,(1,2,0):2,(1,2,1):0,(1,2,2):0,(1,3,0):0,(1,3,1):3,(1,3,2):0,(2,0,0):1,(2,0,1):2,(2,0,2):0,(2,1,0):1,(2,1,1):0,(2,1,2):0,(2,2,0):0,(2,2,1):2,(2,2,2):2,(2,3,0):0,(2,3,1):0,(2,3,2):1},
        {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):1,(0,1,1):0,(0,1,2):0,(0,2,0):0,(0,2,1):0,(0,2,2):0,(1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):1,(1,2,0):0,(1,2,1):1,(1,2,2):1,(2,0,0):0,(2,0,1):0,(2,0,2):0,(2,1,0):2,(2,1,1):0,(2,1,2):0,(2,2,0):2,(2,2,1):0,(2,2,2):0,(3,0,0):1,(3,0,1):2,(3,0,2):0,(3,1,0):1,(3,1,1):1,(3,1,2):1,(3,2,0):0,(3,2,1):2,(3,2,2):0},
        {(0,0,0):0,(0,0,1):0,(0,1,0):1,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):0,(1,0,1):0,(1,1,0):2,(1,1,1):0,(1,2,0):2,(1,2,1):2,(2,0,0):1,(2,0,1):0,(2,1,0):1,(2,1,1):1,(2,2,0):0,(2,2,1):0},
        {(0,0,0):0,(0,0,1):0,(0,0,2):1,(0,1,0):0,(0,1,1):0,(0,1,2):1,(1,0,0):0,(1,0,1):0,(1,0,2):1,(1,1,0):0,(1,1,1):1,(1,1,2):1,(2,0,0):1,(2,0,1):0,(2,0,2):0,(2,1,0):1,(2,1,1):0,(2,1,2):0},
        {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):2,(0,2,0):2,(0,2,1):2,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(1,2,0):1,(1,2,1):2},
    ]
    return ms, rules


# ═══════════════════════════════════════════════════════════════════
# VERIFICATION
# ═══════════════════════════════════════════════════════════════════

def privileged_procs(cfg, rules, n):
    priv = []
    for i in range(n):
        L, S, R = cfg[(i-1)%n], cfg[i], cfg[(i+1)%n]
        if rules[i][(L,S,R)] != S:
            priv.append(i)
    return priv


def move(cfg, proc, rules, n):
    L, S, R = cfg[(proc-1)%n], cfg[proc], cfg[(proc+1)%n]
    new_S = rules[proc][(L,S,R)]
    lst = list(cfg)
    lst[proc] = new_S
    return tuple(lst)


def find_cycles(ms, rules):
    """Find all cycles in the illegitimate transition graph.
    Returns list of (cycle_configs, cycle_movers)."""
    n = len(ms)
    configs = list(iproduct(*(range(m) for m in ms)))

    # Find good cycle (single-privilege configs)
    single_priv = {}
    for cfg in configs:
        priv = privileged_procs(cfg, rules, n)
        if len(priv) == 1:
            nxt = move(cfg, priv[0], rules, n)
            single_priv[cfg] = (nxt, priv[0])

    good_set = set()
    for start in single_priv:
        if start in good_set:
            continue
        path = []
        visited = set()
        cur = start
        while cur in single_priv and cur not in visited:
            visited.add(cur)
            path.append(cur)
            cur, _ = single_priv[cur]
        if cur == start and len(path) > 0:
            good_set.update(path)
            break

    # Find cycles in non-good configs
    # Build transition graph: for each non-good config, list all possible successors
    non_good = [c for c in configs if c not in good_set]
    non_good_set = set(non_good)

    # Iteratively remove configs that can only reach good_set
    bad_set = set(non_good_set)
    changed = True
    while changed:
        changed = False
        to_remove = set()
        for cfg in bad_set:
            priv = privileged_procs(cfg, rules, n)
            if not priv:
                continue  # deadlock — stays in bad_set
            all_exit = True
            for p in priv:
                nxt = move(cfg, p, rules, n)
                if nxt in bad_set:
                    all_exit = False
                    break
            if all_exit:
                to_remove.add(cfg)
        if to_remove:
            bad_set -= to_remove
            changed = True

    if not bad_set:
        return [], good_set

    # Trace a cycle from the bad_set
    cycles = []
    visited_global = set()
    for start in bad_set:
        if start in visited_global:
            continue
        # Follow a path that stays in bad_set
        path = [start]
        path_movers = []
        visited = {start}
        cur = start
        while True:
            priv = privileged_procs(cur, rules, n)
            # Find a move that stays in bad_set
            next_cfg = None
            next_mover = None
            for p in priv:
                nxt = move(cur, p, rules, n)
                if nxt in bad_set:
                    next_cfg = nxt
                    next_mover = p
                    break
            if next_cfg is None:
                break  # shouldn't happen
            if next_cfg in visited:
                # Found a cycle
                cycle_start = path.index(next_cfg)
                cycle_configs = path[cycle_start:]
                path_movers.append(next_mover)
                cycle_movers = path_movers[cycle_start:]
                cycles.append((cycle_configs, cycle_movers))
                visited_global.update(cycle_configs)
                break
            path.append(next_cfg)
            path_movers.append(next_mover)
            visited.add(next_cfg)
            cur = next_cfg

    return cycles, good_set


def verify_full(ms, rules, verbose=False):
    """Full verification. Returns (pass, info_dict)."""
    n = len(ms)
    configs = list(iproduct(*(range(m) for m in ms)))

    # Liveness
    for cfg in configs:
        if not privileged_procs(cfg, rules, n):
            return False, {'fail': 'liveness', 'cfg': cfg}

    # Find good cycle
    single_priv = {}
    for cfg in configs:
        priv = privileged_procs(cfg, rules, n)
        if len(priv) == 1:
            nxt = move(cfg, priv[0], rules, n)
            single_priv[cfg] = (nxt, priv[0])

    good_cycle = None
    good_movers = None
    for start in single_priv:
        path = []
        movers_list = []
        visited = set()
        cur = start
        while cur in single_priv and cur not in visited:
            visited.add(cur)
            path.append(cur)
            nxt, m = single_priv[cur]
            movers_list.append(m)
            cur = nxt
        if cur == start and len(path) > 0:
            good_cycle = path
            good_movers = movers_list
            break

    if good_cycle is None:
        return False, {'fail': 'no_good_cycle', 'single_priv': len(single_priv)}

    # Fairness
    movers_seen = set(good_movers)
    if movers_seen != set(range(n)):
        return False, {'fail': 'fairness', 'missing': set(range(n)) - movers_seen}

    # Convergence
    good_set = set(good_cycle)
    bad_set = set(configs) - good_set
    changed = True
    while changed:
        changed = False
        to_remove = set()
        for cfg in bad_set:
            priv = privileged_procs(cfg, rules, n)
            all_exit = True
            for p in priv:
                nxt = move(cfg, p, rules, n)
                if nxt in bad_set:
                    all_exit = False
                    break
            if all_exit:
                to_remove.add(cfg)
        if to_remove:
            bad_set -= to_remove
            changed = True

    if bad_set:
        return False, {'fail': 'convergence', 'bad_count': len(bad_set), 'bad_set': bad_set}

    product = 1
    for m in ms:
        product *= m
    return True, {'cycle_len': len(good_cycle), 'product': product}


# ═══════════════════════════════════════════════════════════════════
# DIAGNOSTIC: Are cycles fixable by P7/P8?
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("DIAGNOSTIC: Cycle structure with frozen P0-P6")
print("=" * 70)
print()

ms8, rules8 = witness_n8()
ms9 = (2, 2, 3, 4, 3, 3, 2, 3, 3)
n9 = 9

# Build a candidate n=9 system (relay P8, P7 extended with f(L,S,2)=f(L,S,1))
rules9 = [None] * 9
for i in range(7):
    rules9[i] = dict(rules8[i])
rules9[7] = dict(rules8[7])
for L in range(2):
    for S in range(3):
        rules9[7][(L, S, 2)] = rules8[7].get((L, S, 1), S)
rules9[8] = {}
for L in range(3):
    for S in range(3):
        for R in range(2):
            rules9[8][(L, S, R)] = L  # relay

t0 = time.time()
passed, info = verify_full(ms9, rules9)
print(f"Relay candidate: {'PASS' if passed else 'FAIL'} — {info.get('fail', 'OK')}")

if not passed and info['fail'] == 'convergence':
    bad_count = info['bad_count']
    bad_set = info['bad_set']
    print(f"  {bad_count} configs in cycles")

    # Find actual cycles and analyze movers
    cycles, good_set = find_cycles(ms9, rules9)
    print(f"  Found {len(cycles)} cycle(s)")

    for ci, (cyc_cfgs, cyc_movers) in enumerate(cycles[:10]):
        mover_set = set(cyc_movers)
        has_p7 = 7 in mover_set
        has_p8 = 8 in mover_set
        fixed_only = mover_set.issubset(set(range(7)))
        print(f"\n  Cycle {ci}: length={len(cyc_cfgs)}, movers={sorted(mover_set)}")
        print(f"    P7 involved: {has_p7}, P8 involved: {has_p8}")
        print(f"    FIXED-ONLY (unfixable): {fixed_only}")

        # Show first few configs
        for k in range(min(5, len(cyc_cfgs))):
            cfg = cyc_cfgs[k]
            m = cyc_movers[k]
            priv = privileged_procs(cfg, rules9, n9)
            print(f"    step {k}: {cfg}  mover=P{m}  priv={priv}")

    # Count total bad configs by which procs move
    print(f"\n  Analyzing ALL {bad_count} bad configs:")
    p7p8_reachable = 0
    fixed_only_count = 0
    for cfg in bad_set:
        priv = privileged_procs(cfg, rules9, n9)
        if any(p >= 7 for p in priv):
            p7p8_reachable += 1
        # Check if ANY move leads out of bad_set
        exits = False
        for p in priv:
            nxt = move(cfg, p, rules9, n9)
            if nxt not in bad_set:
                exits = True
                break
        if not exits:
            # All moves stay in bad_set
            movers_staying = [p for p in priv if move(cfg, p, rules9, n9) in bad_set]
            if all(p < 7 for p in movers_staying):
                fixed_only_count += 1

    print(f"    P7/P8 privileged at some bad config: {p7p8_reachable}/{bad_count}")
    print(f"    Configs where only fixed procs keep it trapped: {fixed_only_count}/{bad_count}")

elif not passed and info['fail'] == 'liveness':
    print(f"  Deadlocked config: {info['cfg']}")

print(f"\n  Elapsed: {time.time()-t0:.1f}s")

# ═══════════════════════════════════════════════════════════════════
# Now try: is there ANY P7/P8 assignment where convergence works?
# Use proper CEGAR with cycle-breaking constraints
# ═══════════════════════════════════════════════════════════════════

print()
print("=" * 70)
print("CEGAR WITH CYCLE-BREAKING CONSTRAINTS")
print("=" * 70)
print()

try:
    import z3

    solver = z3.Solver()
    solver.set("timeout", 300000)  # 5 min per check

    # Variables: 6 entries for P7(L,S,2) + 18 entries for P8
    p7_vars = {}
    for L in range(2):
        for S in range(3):
            var = z3.Int(f'p7_{L}_{S}_2')
            solver.add(var >= 0, var < 3)
            p7_vars[(L, S, 2)] = var

    p8_vars = {}
    for L in range(3):
        for S in range(3):
            for R in range(2):
                var = z3.Int(f'p8_{L}_{S}_{R}')
                solver.add(var >= 0, var < 3)
                p8_vars[(L, S, R)] = var

    # Helper: get transition value for proc i at config cfg
    def get_trans(i, cfg):
        """Return Z3 expression for f_i(L,S,R) at config cfg."""
        L, S, R = cfg[(i-1)%9], cfg[i], cfg[(i+1)%9]
        if i < 7:
            return z3.IntVal(rules8[i][(L,S,R)])
        elif i == 7:
            if R < 2:
                return z3.IntVal(rules8[7][(L,S,R)])
            else:
                return p7_vars[(L,S,2)]
        else:  # i == 8
            return p8_vars[(L,S,R)]

    # Helper: is proc i privileged at cfg?
    def is_priv(i, cfg):
        """Return Z3 boolean for whether proc i is privileged at cfg."""
        S = cfg[i]
        return get_trans(i, cfg) != z3.IntVal(S)

    # Liveness constraints: every config has at least one privileged proc
    all_configs9 = list(iproduct(*(range(m) for m in ms9)))
    liveness_count = 0
    for cfg in all_configs9:
        # Check fixed procs first
        fixed_priv = False
        for i in range(7):
            L, S, R = cfg[(i-1)%9], cfg[i], cfg[(i+1)%9]
            if rules8[i][(L,S,R)] != S:
                fixed_priv = True
                break
        if fixed_priv:
            continue

        # Check P7 with old entries
        L7, S7, R7 = cfg[6], cfg[7], cfg[8]
        if R7 < 2 and rules8[7][(L7, S7, R7)] != S7:
            continue

        # Need P7_new or P8 to provide privilege
        disj = []
        if R7 == 2:
            disj.append(p7_vars[(L7, S7, 2)] != z3.IntVal(S7))
        L8, S8, R8 = cfg[7], cfg[8], cfg[0]
        disj.append(p8_vars[(L8, S8, R8)] != z3.IntVal(S8))

        if disj:
            solver.add(z3.Or(*disj))
            liveness_count += 1

    print(f"Liveness constraints: {liveness_count}")

    # CEGAR loop with cycle-breaking
    max_iter = 5000
    t0 = time.time()
    cycle_constraints = 0
    found = False

    for iteration in range(max_iter):
        result = solver.check()
        if result == z3.unsat:
            elapsed = time.time() - t0
            print(f"\nUNSAT after {iteration} iterations, {cycle_constraints} cycle constraints ({elapsed:.1f}s)")
            print("PROVED: No P7/P8 assignment works with frozen P0-P6.")
            break
        if result == z3.unknown:
            elapsed = time.time() - t0
            print(f"\nUNKNOWN after {iteration} iterations ({elapsed:.1f}s)")
            break

        model = solver.model()

        # Extract rules
        rules9_z3 = [None] * 9
        for i in range(7):
            rules9_z3[i] = dict(rules8[i])
        rules9_z3[7] = dict(rules8[7])
        for key, var in p7_vars.items():
            val = model.eval(var, model_completion=True)
            rules9_z3[7][key] = val.as_long()
        rules9_z3[8] = {}
        for key, var in p8_vars.items():
            val = model.eval(var, model_completion=True)
            rules9_z3[8][key] = val.as_long()

        # Verify
        passed, info = verify_full(ms9, rules9_z3)
        if passed:
            elapsed = time.time() - t0
            print(f"\n*** WITNESS FOUND at iteration {iteration}! ({elapsed:.1f}s) ***")
            print(f"Product: {info['product']}, Cycle: {info['cycle_len']}")
            print(f"\nP7 extension (R=2):")
            for key in sorted(p7_vars):
                print(f"  f7{key} = {rules9_z3[7][key]}")
            print(f"\nP8 table:")
            for key in sorted(p8_vars):
                print(f"  f8{key} = {rules9_z3[8][key]}")
            print(f"\nFull rules for n=9:")
            for i in range(9):
                print(f"  P{i}: {dict(sorted(rules9_z3[i].items()))}")
            found = True
            break

        # Failed — find WHY and add targeted constraint
        if info['fail'] == 'convergence':
            # Find cycles and add cycle-breaking constraints
            cycles, good_set = find_cycles(ms9, rules9_z3)

            for cyc_cfgs, cyc_movers in cycles[:3]:  # Add constraints for first 3 cycles
                # For each step in the cycle, add a constraint that the
                # transition at that step should NOT produce the cycle value
                # But only for steps involving P7_new or P8 (variable entries)
                breakable_steps = []
                for k in range(len(cyc_cfgs)):
                    cfg = cyc_cfgs[k]
                    mover = cyc_movers[k]
                    cfg_next = cyc_cfgs[(k+1) % len(cyc_cfgs)]

                    if mover == 7:
                        L, S, R = cfg[6], cfg[7], cfg[8]
                        if R == 2:  # Variable entry
                            # Constraint: f7(L,S,2) != cfg_next[7]
                            breakable_steps.append(
                                p7_vars[(L,S,2)] != z3.IntVal(cfg_next[7])
                            )
                    elif mover == 8:
                        L, S, R = cfg[7], cfg[8], cfg[0]
                        # Constraint: f8(L,S,R) != cfg_next[8]
                        breakable_steps.append(
                            p8_vars[(L,S,R)] != z3.IntVal(cfg_next[8])
                        )

                if breakable_steps:
                    # At least one variable step must break
                    solver.add(z3.Or(*breakable_steps))
                    cycle_constraints += 1
                else:
                    # Cycle involves ONLY fixed procs — unfixable!
                    # But wait, maybe the good_set is different with different P7/P8
                    # The cycle existence depends on the good_set, which depends on P7/P8
                    # So we can't immediately declare infeasible
                    # Instead, exclude this exact assignment
                    exclude = z3.Or(
                        *[p7_vars[k] != z3.IntVal(rules9_z3[7][k]) for k in p7_vars],
                        *[p8_vars[k] != z3.IntVal(rules9_z3[8][k]) for k in p8_vars]
                    )
                    solver.add(exclude)
                    cycle_constraints += 1

        elif info['fail'] == 'liveness':
            # Shouldn't happen (liveness is pre-constrained), but exclude
            cfg = info['cfg']
            disj = []
            L7, S7, R7 = cfg[6], cfg[7], cfg[8]
            if R7 == 2:
                disj.append(p7_vars[(L7, S7, 2)] != z3.IntVal(S7))
            L8, S8, R8 = cfg[7], cfg[8], cfg[0]
            disj.append(p8_vars[(L8, S8, R8)] != z3.IntVal(S8))
            if disj:
                solver.add(z3.Or(*disj))
            cycle_constraints += 1

        elif info['fail'] == 'no_good_cycle':
            # Exclude this assignment
            exclude = z3.Or(
                *[p7_vars[k] != z3.IntVal(rules9_z3[7][k]) for k in p7_vars],
                *[p8_vars[k] != z3.IntVal(rules9_z3[8][k]) for k in p8_vars]
            )
            solver.add(exclude)
            cycle_constraints += 1

        elif info['fail'] == 'fairness':
            # Exclude
            exclude = z3.Or(
                *[p7_vars[k] != z3.IntVal(rules9_z3[7][k]) for k in p7_vars],
                *[p8_vars[k] != z3.IntVal(rules9_z3[8][k]) for k in p8_vars]
            )
            solver.add(exclude)
            cycle_constraints += 1

        if iteration % 50 == 0 and iteration > 0:
            elapsed = time.time() - t0
            print(f"  iter={iteration}, cycle_constraints={cycle_constraints}, {elapsed:.1f}s, fail={info.get('fail','?')}")

    if not found and result != z3.unsat:
        elapsed = time.time() - t0
        print(f"\nExhausted {max_iter} iterations, {cycle_constraints} constraints ({elapsed:.1f}s)")

except ImportError:
    print("Z3 not available — skipping CEGAR search")


# ═══════════════════════════════════════════════════════════════════
# PART 2: Try with P0 also free (P0's L neighbor state count = 3 in both)
# ═══════════════════════════════════════════════════════════════════

print()
print("=" * 70)
print("EXTENDED SEARCH: P0 + P7_new + P8 all free (36 variables)")
print("=" * 70)
print()

try:
    import z3

    solver2 = z3.Solver()
    solver2.set("timeout", 300000)

    # P0 variables: 12 entries (L=3, S=2, R=2)
    p0_vars = {}
    for L in range(3):  # P8 (was P7, same count)
        for S in range(2):  # P0
            for R in range(2):  # P1
                var = z3.Int(f'p0_{L}_{S}_{R}')
                solver2.add(var >= 0, var < 2)
                p0_vars[(L, S, R)] = var

    # P7 new entries: 6
    p7_vars2 = {}
    for L in range(2):
        for S in range(3):
            var = z3.Int(f'p7_{L}_{S}_2')
            solver2.add(var >= 0, var < 3)
            p7_vars2[(L, S, 2)] = var

    # P8: 18 entries
    p8_vars2 = {}
    for L in range(3):
        for S in range(3):
            for R in range(2):
                var = z3.Int(f'p8_{L}_{S}_{R}')
                solver2.add(var >= 0, var < 3)
                p8_vars2[(L, S, R)] = var

    def get_trans2(i, cfg):
        L, S, R = cfg[(i-1)%9], cfg[i], cfg[(i+1)%9]
        if i == 0:
            return p0_vars[(L,S,R)]
        elif 1 <= i <= 6:
            return z3.IntVal(rules8[i][(L,S,R)])
        elif i == 7:
            if R < 2:
                return z3.IntVal(rules8[7][(L,S,R)])
            else:
                return p7_vars2[(L,S,2)]
        else:  # i == 8
            return p8_vars2[(L,S,R)]

    # Liveness
    liveness_count2 = 0
    for cfg in all_configs9:
        # Check fixed procs (P1-P6)
        fixed_priv = False
        for i in range(1, 7):
            L, S, R = cfg[(i-1)%9], cfg[i], cfg[(i+1)%9]
            if rules8[i][(L,S,R)] != S:
                fixed_priv = True
                break
        if fixed_priv:
            continue

        # Check P7 old entries
        L7, S7, R7 = cfg[6], cfg[7], cfg[8]
        if R7 < 2 and rules8[7][(L7, S7, R7)] != S7:
            continue

        # Need P0, P7_new, or P8
        disj = []
        # P0
        L0, S0, R0 = cfg[8], cfg[0], cfg[1]
        disj.append(p0_vars[(L0, S0, R0)] != z3.IntVal(S0))
        # P7 new
        if R7 == 2:
            disj.append(p7_vars2[(L7, S7, 2)] != z3.IntVal(S7))
        # P8
        L8, S8, R8 = cfg[7], cfg[8], cfg[0]
        disj.append(p8_vars2[(L8, S8, R8)] != z3.IntVal(S8))

        solver2.add(z3.Or(*disj))
        liveness_count2 += 1

    print(f"Liveness constraints: {liveness_count2}")

    # Quick test: just find first satisfying assignment and check
    max_iter2 = 3000
    t0 = time.time()
    cycle_constraints2 = 0
    found2 = False

    for iteration in range(max_iter2):
        result = solver2.check()
        if result == z3.unsat:
            elapsed = time.time() - t0
            print(f"\nUNSAT after {iteration} iters, {cycle_constraints2} constraints ({elapsed:.1f}s)")
            print("PROVED: No P0/P7_new/P8 assignment works with frozen P1-P6.")
            break
        if result == z3.unknown:
            elapsed = time.time() - t0
            print(f"\nUNKNOWN after {iteration} iters ({elapsed:.1f}s)")
            break

        model = solver2.model()

        # Extract
        rules9_z3 = [None] * 9
        rules9_z3[0] = {}
        for key, var in p0_vars.items():
            val = model.eval(var, model_completion=True)
            rules9_z3[0][key] = val.as_long()
        for i in range(1, 7):
            rules9_z3[i] = dict(rules8[i])
        rules9_z3[7] = dict(rules8[7])
        for key, var in p7_vars2.items():
            val = model.eval(var, model_completion=True)
            rules9_z3[7][key] = val.as_long()
        rules9_z3[8] = {}
        for key, var in p8_vars2.items():
            val = model.eval(var, model_completion=True)
            rules9_z3[8][key] = val.as_long()

        passed, info = verify_full(ms9, rules9_z3)
        if passed:
            elapsed = time.time() - t0
            print(f"\n*** WITNESS FOUND at iteration {iteration}! ({elapsed:.1f}s) ***")
            print(f"Product: {info['product']}, Cycle: {info['cycle_len']}")
            print(f"\nFull rules:")
            for i in range(9):
                print(f"  P{i}: {dict(sorted(rules9_z3[i].items()))}")
            found2 = True
            break

        # Add cycle-breaking constraints
        if info['fail'] == 'convergence':
            cycles, _ = find_cycles(ms9, rules9_z3)
            for cyc_cfgs, cyc_movers in cycles[:3]:
                breakable = []
                for k in range(len(cyc_cfgs)):
                    cfg = cyc_cfgs[k]
                    mover = cyc_movers[k]
                    cfg_next = cyc_cfgs[(k+1) % len(cyc_cfgs)]

                    if mover == 0:
                        L, S, R = cfg[8], cfg[0], cfg[1]
                        breakable.append(p0_vars[(L,S,R)] != z3.IntVal(cfg_next[0]))
                    elif mover == 7:
                        L, S, R = cfg[6], cfg[7], cfg[8]
                        if R == 2:
                            breakable.append(p7_vars2[(L,S,2)] != z3.IntVal(cfg_next[7]))
                    elif mover == 8:
                        L, S, R = cfg[7], cfg[8], cfg[0]
                        breakable.append(p8_vars2[(L,S,R)] != z3.IntVal(cfg_next[8]))

                if breakable:
                    solver2.add(z3.Or(*breakable))
                    cycle_constraints2 += 1
                else:
                    # Only fixed movers — exclude assignment
                    all_vars = list(p0_vars.items()) + list(p7_vars2.items()) + list(p8_vars2.items())
                    exclude = z3.Or(*[v != z3.IntVal(
                        rules9_z3[0 if 'p0' in str(v) else (7 if 'p7' in str(v) else 8)].get(k, 0)
                    ) for k, v in all_vars])
                    solver2.add(exclude)
                    cycle_constraints2 += 1
        else:
            # Non-convergence failure — exclude
            all_var_vals = []
            for k, v in p0_vars.items():
                all_var_vals.append(v != z3.IntVal(rules9_z3[0][k]))
            for k, v in p7_vars2.items():
                all_var_vals.append(v != z3.IntVal(rules9_z3[7][k]))
            for k, v in p8_vars2.items():
                all_var_vals.append(v != z3.IntVal(rules9_z3[8][k]))
            solver2.add(z3.Or(*all_var_vals))
            cycle_constraints2 += 1

        if iteration % 50 == 0 and iteration > 0:
            elapsed = time.time() - t0
            print(f"  iter={iteration}, constraints={cycle_constraints2}, {elapsed:.1f}s, fail={info.get('fail','?')}")

    if not found2 and result != z3.unsat:
        elapsed = time.time() - t0
        print(f"\nExhausted {max_iter2} iters, {cycle_constraints2} constraints ({elapsed:.1f}s)")

except ImportError:
    print("Z3 not available")

print()
print("=" * 70)
print("DIAGNOSTIC COMPLETE")
print("=" * 70)
