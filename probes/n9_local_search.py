#!/usr/bin/env python3
"""
N=9 Local Search: Find witness for ms=(2,2,3,4,3,3,2,3,3) with product 7776.

Strategy: Random restart local search. Start from n=8 witness with random
P7/P8, allow all processors to be modified during repair.
"""

import random
import time
from itertools import product as iproduct
from collections import Counter

random.seed(42)

ms9 = (2, 2, 3, 4, 3, 3, 2, 3, 3)
n9 = 9
PRODUCT = 7776

# Precompute all configs
ALL_CONFIGS = list(iproduct(*(range(m) for m in ms9)))
assert len(ALL_CONFIGS) == PRODUCT

# N=8 witness for seeding
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
# FAST VERIFICATION
# ═══════════════════════════════════════════════════════════════════

def privileged(cfg, rules):
    priv = []
    for i in range(n9):
        L, S, R = cfg[(i-1)%n9], cfg[i], cfg[(i+1)%n9]
        if rules[i][(L,S,R)] != S:
            priv.append(i)
    return priv


def do_move(cfg, proc, rules):
    L, S, R = cfg[(proc-1)%n9], cfg[proc], cfg[(proc+1)%n9]
    new_S = rules[proc][(L,S,R)]
    lst = list(cfg)
    lst[proc] = new_S
    return tuple(lst)


def verify_fast(rules):
    """Fast verification. Returns (pass, fail_type, fail_info)."""
    # Liveness
    for cfg in ALL_CONFIGS:
        if not privileged(cfg, rules):
            return False, 'liveness', cfg

    # Find good cycle
    single_priv = {}
    for cfg in ALL_CONFIGS:
        priv = privileged(cfg, rules)
        if len(priv) == 1:
            nxt = do_move(cfg, priv[0], rules)
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
        return False, 'no_good_cycle', len(single_priv)

    # Fairness
    movers_seen = set(good_movers)
    if movers_seen != set(range(n9)):
        return False, 'fairness', set(range(n9)) - movers_seen

    # Convergence
    good_set = set(good_cycle)
    bad_set = set(ALL_CONFIGS) - good_set
    changed = True
    while changed:
        changed = False
        to_remove = set()
        for cfg in bad_set:
            priv = privileged(cfg, rules)
            all_exit = True
            for p in priv:
                nxt = do_move(cfg, p, rules)
                if nxt in bad_set:
                    all_exit = False
                    break
            if all_exit:
                to_remove.add(cfg)
        if to_remove:
            bad_set -= to_remove
            changed = True

    if bad_set:
        return False, 'convergence', len(bad_set)

    return True, 'pass', len(good_cycle)


def count_deadlocks(rules):
    """Count configs with no privileged processor."""
    count = 0
    for cfg in ALL_CONFIGS:
        if not privileged(cfg, rules):
            count += 1
    return count


def score_system(rules):
    """Score a candidate system. Higher is better.
    Returns (score, details) where score prioritizes:
    1. No deadlocks (liveness)
    2. Good cycle exists
    3. All procs move in cycle (fairness)
    4. No convergence cycles
    """
    deadlocks = 0
    for cfg in ALL_CONFIGS:
        if not privileged(cfg, rules):
            deadlocks += 1
    if deadlocks > 0:
        return -10000 + (PRODUCT - deadlocks), f"deadlocks={deadlocks}"

    # Good cycle
    single_priv = {}
    for cfg in ALL_CONFIGS:
        priv = privileged(cfg, rules)
        if len(priv) == 1:
            nxt = do_move(cfg, priv[0], rules)
            single_priv[cfg] = (nxt, priv[0])

    best_cycle_len = 0
    best_movers = set()
    visited_global = set()
    for start in single_priv:
        if start in visited_global:
            continue
        path = []
        movers_list = []
        visited = set()
        cur = start
        while cur in single_priv and cur not in visited:
            visited.add(cur)
            visited_global.add(cur)
            path.append(cur)
            nxt, m = single_priv[cur]
            movers_list.append(m)
            cur = nxt
        if cur == start and len(path) > best_cycle_len:
            best_cycle_len = len(path)
            best_movers = set(movers_list)

    if best_cycle_len == 0:
        return -5000 + len(single_priv), f"no_cycle, sp={len(single_priv)}"

    fairness_score = len(best_movers)  # out of 9
    if fairness_score < n9:
        return -1000 + fairness_score * 100 + best_cycle_len, \
               f"fairness={fairness_score}/9, cycle={best_cycle_len}"

    # Check convergence
    good_set = set()
    for start in single_priv:
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

    bad_set = set(ALL_CONFIGS) - good_set
    changed = True
    while changed:
        changed = False
        to_remove = set()
        for cfg in bad_set:
            priv = privileged(cfg, rules)
            all_exit = True
            for p in priv:
                nxt = do_move(cfg, p, rules)
                if nxt in bad_set:
                    all_exit = False
                    break
            if all_exit:
                to_remove.add(cfg)
        if to_remove:
            bad_set -= to_remove
            changed = True

    if bad_set:
        return PRODUCT - len(bad_set), f"convergence_bad={len(bad_set)}"

    return PRODUCT + best_cycle_len, f"PASS! cycle={best_cycle_len}"


# ═══════════════════════════════════════════════════════════════════
# INITIALIZATION STRATEGIES
# ═══════════════════════════════════════════════════════════════════

def random_rules():
    """Generate completely random transition functions."""
    rules = []
    for i in range(n9):
        L_size = ms9[(i-1)%n9]
        S_size = ms9[i]
        R_size = ms9[(i+1)%n9]
        d = {}
        for L in range(L_size):
            for S in range(S_size):
                for R in range(R_size):
                    d[(L,S,R)] = random.randint(0, S_size - 1)
        rules.append(d)
    return rules


def seed_from_n8():
    """Seed from n=8 witness with random P7 extension + random P8."""
    _, rules8 = witness_n8()
    rules = [None] * 9

    # P0: keep from n=8 (L neighbor goes from P7(3) to P8(3) — same domain)
    rules[0] = dict(rules8[0])

    # P1-P6: keep from n=8
    for i in range(1, 7):
        rules[i] = dict(rules8[i])

    # P7: keep old entries, random new (R=2)
    rules[7] = dict(rules8[7])
    for L in range(ms9[6]):  # P6: 2 states
        for S in range(ms9[7]):  # P7: 3 states
            rules[7][(L, S, 2)] = random.randint(0, 2)

    # P8: random
    rules[8] = {}
    for L in range(ms9[7]):  # P7: 3 states
        for S in range(ms9[8]):  # P8: 3 states
            for R in range(ms9[0]):  # P0: 2 states
                rules[8][(L, S, R)] = random.randint(0, 2)

    return rules


def perturb_rules(rules, num_changes=1, allowed_procs=None):
    """Make random changes to transition functions."""
    new_rules = [dict(r) for r in rules]
    for _ in range(num_changes):
        if allowed_procs is None:
            proc = random.randint(0, n9 - 1)
        else:
            proc = random.choice(allowed_procs)

        L_size = ms9[(proc-1)%n9]
        S_size = ms9[proc]
        R_size = ms9[(proc+1)%n9]

        L = random.randint(0, L_size - 1)
        S = random.randint(0, S_size - 1)
        R = random.randint(0, R_size - 1)

        old_val = new_rules[proc][(L, S, R)]
        # Choose a different value
        new_val = random.randint(0, S_size - 1)
        while new_val == old_val and S_size > 1:
            new_val = random.randint(0, S_size - 1)
        new_rules[proc][(L, S, R)] = new_val

    return new_rules


# ═══════════════════════════════════════════════════════════════════
# LOCAL SEARCH — HILL CLIMBING WITH RESTARTS
# ═══════════════════════════════════════════════════════════════════

def local_search(init_rules, max_steps=5000, verbose=False):
    """Hill-climbing local search. Returns best rules found."""
    rules = [dict(r) for r in init_rules]
    score, detail = score_system(rules)
    best_score = score
    best_rules = [dict(r) for r in rules]

    stale = 0
    for step in range(max_steps):
        # Adaptive perturbation: more changes when stuck
        num_changes = 1 if stale < 50 else (2 if stale < 200 else 3)

        # Try perturbation
        new_rules = perturb_rules(rules, num_changes)
        new_score, new_detail = score_system(new_rules)

        if new_score > score:
            rules = new_rules
            score = new_score
            stale = 0
            if score > best_score:
                best_score = score
                best_rules = [dict(r) for r in rules]
                if verbose:
                    print(f"  step {step}: score={score}, {new_detail}")
                if 'PASS' in new_detail:
                    return best_rules, best_score, new_detail
        elif new_score == score:
            # Sideways move (sometimes accept)
            if random.random() < 0.3:
                rules = new_rules
                stale += 1
            else:
                stale += 1
        else:
            # Worse — occasional accept (simulated annealing style)
            temp = max(0.01, 1.0 - step / max_steps)
            delta = score - new_score
            if delta < 100 and random.random() < temp * 0.1:
                rules = new_rules
                score = new_score
            stale += 1

    return best_rules, best_score, "no_pass"


# ═══════════════════════════════════════════════════════════════════
# TARGETED REPAIR SEARCH
# ═══════════════════════════════════════════════════════════════════

def targeted_repair(init_rules, max_steps=10000, verbose=False):
    """Repair-based search: find a violation, fix it."""
    rules = [dict(r) for r in init_rules]

    for step in range(max_steps):
        # Check liveness first
        deadlock = None
        for cfg in ALL_CONFIGS:
            if not privileged(cfg, rules):
                deadlock = cfg
                break

        if deadlock is not None:
            # Fix: make some proc privileged at this config
            proc = random.randint(0, n9 - 1)
            L, S, R = deadlock[(proc-1)%n9], deadlock[proc], deadlock[(proc+1)%n9]
            # Set f(L,S,R) to something ≠ S
            new_val = random.randint(0, ms9[proc] - 1)
            while new_val == S:
                new_val = random.randint(0, ms9[proc] - 1)
            rules[proc][(L, S, R)] = new_val
            continue

        # Check good cycle
        single_priv = {}
        for cfg in ALL_CONFIGS:
            priv = privileged(cfg, rules)
            if len(priv) == 1:
                nxt = do_move(cfg, priv[0], rules)
                single_priv[cfg] = (nxt, priv[0])

        good_cycle = None
        good_movers = None
        visited_global = set()
        for start in single_priv:
            if start in visited_global:
                continue
            path = []
            movers_list = []
            visited = set()
            cur = start
            while cur in single_priv and cur not in visited:
                visited.add(cur)
                visited_global.add(cur)
                path.append(cur)
                nxt, m = single_priv[cur]
                movers_list.append(m)
                cur = nxt
            if cur == start and len(path) > 0:
                good_cycle = path
                good_movers = movers_list
                break

        if good_cycle is None:
            # No good cycle — perturb randomly
            rules = perturb_rules(rules, 2)
            continue

        # Check fairness
        movers_seen = set(good_movers)
        if movers_seen != set(range(n9)):
            missing = set(range(n9)) - movers_seen
            # Try to make a missing proc move in some single-priv config
            # by modifying another proc to remove its privilege there
            rules = perturb_rules(rules, 1)
            continue

        # Check convergence
        good_set = set(good_cycle)
        bad_set = set(ALL_CONFIGS) - good_set
        changed = True
        while changed:
            changed = False
            to_remove = set()
            for cfg in bad_set:
                priv = privileged(cfg, rules)
                all_exit = True
                for p in priv:
                    nxt = do_move(cfg, p, rules)
                    if nxt in bad_set:
                        all_exit = False
                        break
                if all_exit:
                    to_remove.add(cfg)
            if to_remove:
                bad_set -= to_remove
                changed = True

        if not bad_set:
            return rules, 'PASS', len(good_cycle)

        # Bad configs exist — try to break a cycle
        # Pick a random bad config and modify a transition to push it out
        bad_cfg = random.choice(list(bad_set))
        priv = privileged(bad_cfg, rules)
        if priv:
            proc = random.choice(priv)
            nxt = do_move(bad_cfg, proc, rules)
            if nxt in bad_set:
                # This move keeps us in bad_set. Change the transition.
                L, S, R = bad_cfg[(proc-1)%n9], bad_cfg[proc], bad_cfg[(proc+1)%n9]
                new_val = random.randint(0, ms9[proc] - 1)
                rules[proc][(L, S, R)] = new_val
        else:
            rules = perturb_rules(rules, 1)

        if step % 1000 == 0 and step > 0 and verbose:
            print(f"  step {step}: bad_set={len(bad_set)}, "
                  f"cycle={len(good_cycle) if good_cycle else 0}, "
                  f"fair={len(movers_seen)}/9")

    return rules, 'exhausted', 0


# ═══════════════════════════════════════════════════════════════════
# MAIN SEARCH
# ═══════════════════════════════════════════════════════════════════

print("=" * 70)
print("N=9 LOCAL SEARCH")
print(f"ms={ms9}, product={PRODUCT}")
print("=" * 70)
print()

t0 = time.time()
best_overall_score = -float('inf')
best_overall_rules = None

NUM_RESTARTS = 200
STEPS_PER_RESTART = 3000

# Phase 1: Seeded from n=8, hill climbing
print("Phase 1: Hill climbing from n=8 seeds")
print("-" * 40)
for restart in range(NUM_RESTARTS):
    if restart % 2 == 0:
        init = seed_from_n8()
    else:
        init = random_rules()

    rules, score, detail = local_search(init, max_steps=STEPS_PER_RESTART, verbose=False)

    if score > best_overall_score:
        best_overall_score = score
        best_overall_rules = rules
        print(f"  restart {restart}: NEW BEST score={score}, {detail}")

    if 'PASS' in detail:
        elapsed = time.time() - t0
        print(f"\n*** WITNESS FOUND at restart {restart}! ({elapsed:.1f}s) ***")
        print(f"Detail: {detail}")
        # Print full rules
        for i in range(n9):
            print(f"  P{i}({ms9[i]}): {dict(sorted(rules[i].items()))}")
        # Full verification
        passed, fail_type, fail_info = verify_fast(rules)
        print(f"\nFull verification: {'PASS' if passed else 'FAIL'} ({fail_type}: {fail_info})")
        break

    if restart % 20 == 0 and restart > 0:
        elapsed = time.time() - t0
        print(f"  [{restart}/{NUM_RESTARTS}] best={best_overall_score}, {elapsed:.1f}s")

else:
    elapsed = time.time() - t0
    print(f"\nPhase 1 done. Best score: {best_overall_score} ({elapsed:.1f}s)")

# Phase 2: Targeted repair from best candidate
print()
print("Phase 2: Targeted repair search")
print("-" * 40)

for restart in range(100):
    if restart % 3 == 0 and best_overall_rules:
        # Start from best found so far + small perturbation
        init = perturb_rules(best_overall_rules, num_changes=5)
    elif restart % 3 == 1:
        init = seed_from_n8()
    else:
        init = random_rules()

    rules, status, cycle_len = targeted_repair(init, max_steps=10000, verbose=(restart % 10 == 0))

    if status == 'PASS':
        elapsed = time.time() - t0
        print(f"\n*** WITNESS FOUND at restart {restart}! ({elapsed:.1f}s) ***")
        print(f"Cycle length: {cycle_len}")
        for i in range(n9):
            print(f"  P{i}({ms9[i]}): {dict(sorted(rules[i].items()))}")
        # Full verification
        passed, fail_type, fail_info = verify_fast(rules)
        print(f"\nFull verification: {'PASS' if passed else 'FAIL'} ({fail_type}: {fail_info})")
        break

    if restart % 10 == 0:
        elapsed = time.time() - t0
        print(f"  [{restart}/100] {elapsed:.1f}s")

else:
    elapsed = time.time() - t0
    print(f"\nPhase 2 done. No witness found. ({elapsed:.1f}s)")

print()
print(f"Total time: {time.time()-t0:.1f}s")
print("=" * 70)
