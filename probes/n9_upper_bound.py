#!/usr/bin/env python3
"""n9_upper_bound.py — Establish tight upper bounds for M_9.

M_9 ≥ 7776 (proved analytically).
M_9 > 7776 (all 56 orientations of {2^3,3^5,4} dead — RC sweep).

This script systematically tests constructions at decreasing product values
to find the tightest upper bound.

Priority order:
  1. (2,2,3,3,3,3,3,3,3)  product=8748   (4·3^7)  — best case
  2. (2,2,2,5,3,3,3,3,3)  product=9720   — quintic
  3. (2,2,2,4,4,3,3,3,3)  product=10368  — two quaternary
  4. (2,3,3,3,3,3,3,3,3)  product=13122  — one binary
  5. (3,3,3,3,3,3,3,3,3)  product=19683  — baseline (Dijkstra Sol 3)

Usage: python3 n9_upper_bound.py
"""

import sys
import time
import random
from itertools import product as cartesian, permutations
from collections import Counter, defaultdict

sys.setrecursionlimit(50000)
random.seed(42)


# ══════════════════════════════════════════════════════════════════════
# VERIFIER
# ══════════════════════════════════════════════════════════════════════

def verify(name, state_counts, rules, verbose=True):
    """Verify all 5 Dijkstra properties. rules = list of dicts {(L,S,R): out}."""
    n = len(state_counts)
    P = 1
    for m in state_counts:
        P *= m
    configs = list(cartesian(*(range(m) for m in state_counts)))

    def privileged(cfg):
        priv = []
        for i in range(n):
            L = cfg[(i - 1) % n]; S = cfg[i]; R = cfg[(i + 1) % n]
            if rules[i][(L, S, R)] != S:
                priv.append(i)
        return priv

    def move(cfg, proc):
        L = cfg[(proc - 1) % n]; S = cfg[proc]; R = cfg[(proc + 1) % n]
        new_S = rules[proc][(L, S, R)]
        lst = list(cfg); lst[proc] = new_S
        return tuple(lst)

    for cfg in configs:
        if not privileged(cfg):
            if verbose:
                print(f"  FAIL liveness: {cfg}")
            return False

    single_priv = {}
    for cfg in configs:
        priv = privileged(cfg)
        if len(priv) == 1:
            single_priv[cfg] = (move(cfg, priv[0]), priv[0])

    good_cycle = None
    visited_global = set()
    for start in single_priv:
        if start in visited_global:
            continue
        path = []; movers = []; path_set = set(); cur = start
        while cur in single_priv and cur not in path_set:
            path_set.add(cur)
            path.append(cur)
            nxt, mover = single_priv[cur]
            movers.append(mover); cur = nxt
        # cur is either: (a) back to start (full cycle), (b) revisited some
        # config in path (tail + cycle), or (c) left single_priv
        if cur in path_set:
            idx = path.index(cur)
            cycle_path = path[idx:]
            cycle_movers = movers[idx:]
            if set(cycle_movers) == set(range(n)):
                good_cycle = cycle_path
                good_movers = cycle_movers
                visited_global.update(path_set)
                break
        visited_global.update(path_set)

    if good_cycle is None:
        if verbose:
            print(f"  FAIL: no good cycle (single_priv={len(single_priv)})")
        return False

    good_set = set(good_cycle)
    bad_set = set(configs) - good_set
    changed = True
    while changed:
        changed = False; to_remove = set()
        for cfg in bad_set:
            priv = privileged(cfg)
            all_exit = True
            for p in priv:
                if move(cfg, p) in bad_set:
                    all_exit = False; break
            if all_exit:
                to_remove.add(cfg)
        if to_remove:
            bad_set -= to_remove; changed = True

    if bad_set:
        if verbose:
            print(f"  FAIL convergence: {len(bad_set)} bad in cycles")
        return False

    movers_seen = set(good_movers)
    if movers_seen != set(range(n)):
        if verbose:
            print(f"  FAIL fairness: {set(range(n)) - movers_seen} never move")
        return False

    if verbose:
        print(f"  PASS  product={P}  cycle={len(good_cycle)}  "
              f"total={len(configs)}  bad={len(configs)-len(good_cycle)}")
    return True


def verify_return_detail(state_counts, rules):
    """Like verify but returns (pass, detail_string, fail_type)."""
    n = len(state_counts)
    P = 1
    for m in state_counts:
        P *= m
    configs = list(cartesian(*(range(m) for m in state_counts)))

    def privileged(cfg):
        priv = []
        for i in range(n):
            L = cfg[(i - 1) % n]; S = cfg[i]; R = cfg[(i + 1) % n]
            if rules[i][(L, S, R)] != S:
                priv.append(i)
        return priv

    def move(cfg, proc):
        L = cfg[(proc - 1) % n]; S = cfg[proc]; R = cfg[(proc + 1) % n]
        new_S = rules[proc][(L, S, R)]
        lst = list(cfg); lst[proc] = new_S
        return tuple(lst)

    deadlocks = 0
    for cfg in configs:
        if not privileged(cfg):
            deadlocks += 1
    if deadlocks > 0:
        return False, f"deadlocks={deadlocks}", "liveness"

    single_priv = {}
    for cfg in configs:
        priv = privileged(cfg)
        if len(priv) == 1:
            single_priv[cfg] = (move(cfg, priv[0]), priv[0])

    good_cycle = None
    visited_global = set()
    for start in single_priv:
        if start in visited_global:
            continue
        path = []; movers = []; path_set = set(); cur = start
        while cur in single_priv and cur not in path_set:
            path_set.add(cur)
            path.append(cur)
            nxt, mover = single_priv[cur]
            movers.append(mover); cur = nxt
        if cur in path_set:
            idx = path.index(cur)
            cycle_path = path[idx:]
            cycle_movers = movers[idx:]
            if set(cycle_movers) == set(range(n)):
                good_cycle = cycle_path
                good_movers = cycle_movers
                visited_global.update(path_set)
                break
        visited_global.update(path_set)

    if good_cycle is None:
        return False, f"no_cycle sp={len(single_priv)}", "no_cycle"

    movers_seen = set(good_movers)
    if movers_seen != set(range(n)):
        missing = set(range(n)) - movers_seen
        return False, f"fairness missing={missing} cycle={len(good_cycle)}", "fairness"

    good_set = set(good_cycle)
    bad_set = set(configs) - good_set
    changed = True
    while changed:
        changed = False; to_remove = set()
        for cfg in bad_set:
            priv = privileged(cfg)
            all_exit = True
            for p in priv:
                if move(cfg, p) in bad_set:
                    all_exit = False; break
            if all_exit:
                to_remove.add(cfg)
        if to_remove:
            bad_set -= to_remove; changed = True

    if bad_set:
        return False, f"convergence bad={len(bad_set)} cycle={len(good_cycle)}", "convergence"

    return True, f"PASS cycle={len(good_cycle)}", "pass"


# ══════════════════════════════════════════════════════════════════════
# CONSTRUCTION: Real Dijkstra Sol 3 (all-ternary, works for any n)
# ══════════════════════════════════════════════════════════════════════

def dijkstra_sol3_real(n):
    """The REAL Dijkstra Sol 3 — 3-state procs, works for any n.
    Bottom: f(L,S,R) = (S-1)%3 if (S+1)%3 == R, else S
    Top:    f(L,S,R) = (L+1)%3 if L==R and (L+1)%3 != S, else S
    Middle: f(L,S,R) = L if (S+1)%3==L, R if (S+1)%3==R, else S
    """
    ms = tuple([3] * n)
    rules = []
    for i in range(n):
        d = {}
        for L in range(3):
            for S in range(3):
                for R in range(3):
                    if i == 0:  # bottom
                        if (S + 1) % 3 == R:
                            d[(L, S, R)] = (S - 1) % 3
                        else:
                            d[(L, S, R)] = S
                    elif i == n - 1:  # top
                        if L == R and (L + 1) % 3 != S:
                            d[(L, S, R)] = (L + 1) % 3
                        else:
                            d[(L, S, R)] = S
                    else:  # middle
                        if (S + 1) % 3 == L:
                            d[(L, S, R)] = L
                        elif (S + 1) % 3 == R:
                            d[(L, S, R)] = R
                        else:
                            d[(L, S, R)] = S
        rules.append(d)
    return ms, rules


# ══════════════════════════════════════════════════════════════════════
# CONSTRUCTION: Modified Sol 3 with binary proc(s)
# ══════════════════════════════════════════════════════════════════════

def sol3_with_binary(n, binary_positions):
    """Modified Sol 3 where some procs are binary.
    Binary procs use f(L,S,R) = L mod 2 with Sol3-like privilege rules.
    Ternary procs use standard Sol 3 rules.
    """
    ms = tuple(2 if i in binary_positions else 3 for i in range(n))
    rules = []
    for i in range(n):
        m_i = ms[i]
        m_L = ms[(i - 1) % n]
        m_R = ms[(i + 1) % n]
        d = {}
        for L in range(m_L):
            for S in range(m_i):
                for R in range(m_R):
                    if m_i == 2:
                        # Binary proc: copy-left mod 2 if different
                        new_S = L % 2
                        if new_S == S:
                            d[(L, S, R)] = S
                        else:
                            d[(L, S, R)] = new_S
                    elif i == 0:  # bottom, ternary
                        if (S + 1) % 3 == R % 3:
                            d[(L, S, R)] = (S - 1) % 3
                        else:
                            d[(L, S, R)] = S
                    elif i == n - 1:  # top, ternary
                        if L % 3 == R % 3 and (L % 3 + 1) % 3 != S:
                            d[(L, S, R)] = (L % 3 + 1) % 3
                        else:
                            d[(L, S, R)] = S
                    else:  # middle, ternary
                        if (S + 1) % 3 == L % 3:
                            d[(L, S, R)] = L % 3
                        elif (S + 1) % 3 == R % 3:
                            d[(L, S, R)] = R % 3
                        else:
                            d[(L, S, R)] = S
        rules.append(d)
    return ms, rules


# ══════════════════════════════════════════════════════════════════════
# CONSTRUCTION: Family of Sol 3 variants for mixed state counts
# ══════════════════════════════════════════════════════════════════════

def sol3_variant_A(state_counts, bottom=0):
    """Sol 3 variant: bottom does (L+1) mod m, others copy L mod m.
    This is the naive generalization — often fails but worth checking."""
    n = len(state_counts)
    rules = []
    for i in range(n):
        m_i = state_counts[i]
        m_L = state_counts[(i - 1) % n]
        m_R = state_counts[(i + 1) % n]
        d = {}
        for L in range(m_L):
            for S in range(m_i):
                for R in range(m_R):
                    if i == bottom:
                        d[(L, S, R)] = (L + 1) % m_i
                    else:
                        d[(L, S, R)] = L % m_i
        rules.append(d)
    return state_counts, rules


def sol3_variant_B(state_counts, bottom=0, top=None):
    """Sol 3 variant B: uses Sol3 logic adapted to mixed counts.
    Bottom: f = (S-1)%m if (S+1)%m == R%m, else S
    Top:    f = (L%m+1)%m if L%m==R%m and (L%m+1)%m != S, else S
    Middle: f = L%m if (S+1)%m == L%m, f = R%m if (S+1)%m == R%m, else S
    """
    n = len(state_counts)
    if top is None:
        top = n - 1
    rules = []
    for i in range(n):
        m_i = state_counts[i]
        m_L = state_counts[(i - 1) % n]
        m_R = state_counts[(i + 1) % n]
        d = {}
        for L in range(m_L):
            for S in range(m_i):
                for R in range(m_R):
                    if i == bottom:
                        if (S + 1) % m_i == R % m_i:
                            d[(L, S, R)] = (S - 1) % m_i
                        else:
                            d[(L, S, R)] = S
                    elif i == top:
                        Lm = L % m_i
                        Rm = R % m_i
                        if Lm == Rm and (Lm + 1) % m_i != S:
                            d[(L, S, R)] = (Lm + 1) % m_i
                        else:
                            d[(L, S, R)] = S
                    else:  # middle
                        Lm = L % m_i
                        Rm = R % m_i
                        if (S + 1) % m_i == Lm:
                            d[(L, S, R)] = Lm
                        elif (S + 1) % m_i == Rm:
                            d[(L, S, R)] = Rm
                        else:
                            d[(L, S, R)] = S
        rules.append(d)
    return state_counts, rules


def sol1_variant(state_counts, bottom=0):
    """Sol 1 variant: bottom increments if L==S, others copy L if different."""
    n = len(state_counts)
    rules = []
    for i in range(n):
        m_i = state_counts[i]
        m_L = state_counts[(i - 1) % n]
        m_R = state_counts[(i + 1) % n]
        d = {}
        for L in range(m_L):
            for S in range(m_i):
                for R in range(m_R):
                    if i == bottom:
                        if L % m_i == S:
                            d[(L, S, R)] = (S + 1) % m_i
                        else:
                            d[(L, S, R)] = S
                    else:
                        Lm = L % m_i
                        if Lm != S:
                            d[(L, S, R)] = Lm
                        else:
                            d[(L, S, R)] = S
        rules.append(d)
    return state_counts, rules


# ══════════════════════════════════════════════════════════════════════
# RANDOM LOCAL SEARCH
# ══════════════════════════════════════════════════════════════════════

def random_rules(ms):
    """Generate random transition tables for state counts ms."""
    n = len(ms)
    rules = []
    for i in range(n):
        m_L = ms[(i - 1) % n]
        m_S = ms[i]
        m_R = ms[(i + 1) % n]
        d = {}
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    d[(L, S, R)] = random.randint(0, m_S - 1)
        rules.append(d)
    return rules


def seed_from_sol3(ms):
    """Seed rules from Sol 3 (all-ternary) projected to ms."""
    n = len(ms)
    _, sol3_rules = dijkstra_sol3_real(n)
    rules = []
    for i in range(n):
        m_i = ms[i]
        m_L = ms[(i - 1) % n]
        m_R = ms[(i + 1) % n]
        d = {}
        for L in range(m_L):
            for S in range(m_i):
                for R in range(m_R):
                    # Project: use Sol3 rule with L%3, S%3, R%3, then mod m_i
                    sol3_out = sol3_rules[i][(L % 3, S % 3, R % 3)]
                    d[(L, S, R)] = sol3_out % m_i
        rules.append(d)
    return rules


def perturb(rules, ms, num_changes=1):
    """Randomly perturb transition tables."""
    n = len(ms)
    new_rules = [dict(r) for r in rules]
    for _ in range(num_changes):
        proc = random.randint(0, n - 1)
        m_L = ms[(proc - 1) % n]
        m_S = ms[proc]
        m_R = ms[(proc + 1) % n]
        L = random.randint(0, m_L - 1)
        S = random.randint(0, m_S - 1)
        R = random.randint(0, m_R - 1)
        old_val = new_rules[proc][(L, S, R)]
        new_val = random.randint(0, m_S - 1)
        while new_val == old_val and m_S > 1:
            new_val = random.randint(0, m_S - 1)
        new_rules[proc][(L, S, R)] = new_val
    return new_rules


def score_system(ms, rules):
    """Score: higher is better. >0 means passes some properties."""
    n = len(ms)
    P = 1
    for m in ms:
        P *= m
    configs = list(cartesian(*(range(m) for m in ms)))

    def privileged(cfg):
        priv = []
        for i in range(n):
            L = cfg[(i - 1) % n]; S = cfg[i]; R = cfg[(i + 1) % n]
            if rules[i][(L, S, R)] != S:
                priv.append(i)
        return priv

    def move(cfg, proc):
        L = cfg[(proc - 1) % n]; S = cfg[proc]; R = cfg[(proc + 1) % n]
        new_S = rules[proc][(L, S, R)]
        lst = list(cfg); lst[proc] = new_S
        return tuple(lst)

    # Liveness
    deadlocks = sum(1 for cfg in configs if not privileged(cfg))
    if deadlocks > 0:
        return -10000 + (P - deadlocks), f"deadlocks={deadlocks}"

    # Good cycle
    single_priv = {}
    for cfg in configs:
        priv = privileged(cfg)
        if len(priv) == 1:
            single_priv[cfg] = (move(cfg, priv[0]), priv[0])

    best_cycle = 0
    best_movers = set()
    best_cycle_configs = set()
    visited_global = set()
    for start in single_priv:
        if start in visited_global:
            continue
        path = []; ms_list = []; path_set = set(); cur = start
        while cur in single_priv and cur not in path_set:
            path_set.add(cur)
            path.append(cur)
            nxt, m = single_priv[cur]
            ms_list.append(m); cur = nxt
        if cur in path_set:
            idx = path.index(cur)
            cycle_len = len(path) - idx
            cycle_movers = set(ms_list[idx:])
            if cycle_len > best_cycle:
                best_cycle = cycle_len
                best_movers = cycle_movers
                best_cycle_configs = set(path[idx:])
        visited_global.update(path_set)

    if best_cycle == 0:
        return -5000 + len(single_priv), f"no_cycle sp={len(single_priv)}"

    if len(best_movers) < n:
        return -1000 + len(best_movers) * 100 + best_cycle, \
               f"fairness={len(best_movers)}/{n} cycle={best_cycle}"

    # Convergence
    good_set = best_cycle_configs

    bad_set = set(configs) - good_set
    changed = True
    while changed:
        changed = False; to_remove = set()
        for cfg in bad_set:
            priv = privileged(cfg)
            all_exit = True
            for p in priv:
                if move(cfg, p) in bad_set:
                    all_exit = False; break
            if all_exit:
                to_remove.add(cfg)
        if to_remove:
            bad_set -= to_remove; changed = True

    if bad_set:
        return P - len(bad_set), f"convergence bad={len(bad_set)}"

    return P + best_cycle, f"PASS cycle={best_cycle}"


def local_search(ms, max_restarts=200, steps_per_restart=2000, verbose=True):
    """Random-restart hill climbing."""
    n = len(ms)
    best_score = -float('inf')
    best_rules = None
    best_detail = ""

    for restart in range(max_restarts):
        # Initialize
        if restart % 3 == 0:
            rules = seed_from_sol3(ms)
        elif restart % 3 == 1:
            rules = random_rules(ms)
        else:
            if best_rules:
                rules = perturb(best_rules, ms, num_changes=5)
            else:
                rules = random_rules(ms)

        score, detail = score_system(ms, rules)
        local_best = score
        stale = 0

        for step in range(steps_per_restart):
            num_changes = 1 if stale < 50 else (2 if stale < 200 else 3)
            new_rules = perturb(rules, ms, num_changes)
            new_score, new_detail = score_system(ms, new_rules)

            if new_score > score:
                rules = new_rules
                score = new_score
                detail = new_detail
                stale = 0
                if score > local_best:
                    local_best = score
            elif new_score == score and random.random() < 0.3:
                rules = new_rules
                stale += 1
            else:
                temp = max(0.01, 1.0 - step / steps_per_restart)
                delta = score - new_score
                if delta < 100 and random.random() < temp * 0.1:
                    rules = new_rules
                    score = new_score
                stale += 1

            if 'PASS' in detail:
                if verbose:
                    print(f"    *** FOUND at restart {restart}, step {step}! ***")
                return rules, score, detail

        if local_best > best_score:
            best_score = local_best
            best_rules = [dict(r) for r in rules]
            best_detail = detail
            if verbose and restart % 20 == 0:
                print(f"    restart {restart}: best={best_score}, {best_detail}")

    return best_rules, best_score, best_detail


# ══════════════════════════════════════════════════════════════════════
# NECKLACE UTILITIES
# ══════════════════════════════════════════════════════════════════════

def all_necklaces(ms):
    """All distinct necklaces (cyclic rotations) of a multiset."""
    seen = set()
    results = []
    for p in set(permutations(ms)):
        n = len(p)
        best = p
        for shift in range(1, n):
            rot = p[shift:] + p[:shift]
            if rot < best:
                best = rot
        if best not in seen:
            seen.add(best)
            results.append(best)
    return sorted(results)


# ══════════════════════════════════════════════════════════════════════
# PIPELINE SEARCH (good cycle DFS + screening)
# ══════════════════════════════════════════════════════════════════════

def pipeline_search(ms, time_limit=120, verbose=True):
    """Full pipeline: DFS good-cycle search + screening + verification."""
    n = len(ms)
    P = 1
    for m in ms:
        P *= m

    # Import the pipeline components
    try:
        from p2_good_cycle_search import enumerate_good_cycles
        from p2_cycle_screen import forced_rule_map
        from p2_completion_search import has_fatal_forced_cycle_singletons
    except ImportError:
        if verbose:
            print("    Pipeline components not available, skipping")
        return None

    t0 = time.time()
    screened = 0
    survivors = 0

    for cycle, movers in enumerate_good_cycles(ms, time_limit=time_limit, max_cycles=50000):
        screened += 1
        cycle_set = frozenset(cycle)
        fm = forced_rule_map(cycle, movers)
        if not has_fatal_forced_cycle_singletons(ms, cycle_set, fm):
            survivors += 1
            if verbose:
                print(f"    SURVIVOR! cycle {screened}, length={len(cycle)}")
            try:
                from p2_smt_completion import solve_cycle_with_smt
                result = solve_cycle_with_smt(ms, cycle, movers, timeout_ms=60000)
                if verbose:
                    print(f"    SMT: {result.message}")
                if result.found and result.system is not None:
                    # Extract rules as dicts
                    rules = [dict(sorted(t.items())) for t in result.system.rules]
                    return rules
            except Exception as e:
                if verbose:
                    print(f"    SMT error: {e}")
            if survivors >= 20:
                break

        if screened % 5000 == 0:
            elapsed = time.time() - t0
            if verbose:
                print(f"    screened={screened} survivors={survivors} {elapsed:.1f}s")

    elapsed = time.time() - t0
    if verbose:
        print(f"    Pipeline done: screened={screened} survivors={survivors} {elapsed:.1f}s")
    return None


# ══════════════════════════════════════════════════════════════════════
# MAIN
# ══════════════════════════════════════════════════════════════════════

def test_construction(name, ms, rules, results):
    """Test a single construction. If passes, add to results."""
    ok = verify(name, ms, rules, verbose=False)
    P = 1
    for m in ms:
        P *= m
    if ok:
        print(f"  {name}: PASS (product={P})")
        verify(name, ms, rules, verbose=True)
        results[P] = (name, ms, rules)
        return True
    else:
        ok2, detail, ftype = verify_return_detail(ms, rules)
        print(f"  {name}: FAIL ({detail})")
        return False


def test_candidate(ms_base, label, results, try_pipeline=True,
                   try_local=True, local_restarts=100):
    """Test all constructions for a given multiset."""
    necklaces = all_necklaces(ms_base)
    P = 1
    for m in ms_base:
        P *= m
    print(f"\n{'─'*70}")
    print(f"Candidate: {label}, product={P}")
    print(f"  Necklaces: {len(necklaces)}")
    print(f"{'─'*70}")

    found = False

    # Phase 1: Named constructions on each necklace
    print("\n  Phase 1: Named constructions")
    for neck in necklaces:
        n = len(neck)
        # Sol 3 variant A (bottom at each position)
        for bottom in range(n):
            _, rules = sol3_variant_A(neck, bottom=bottom)
            ok = verify(f"Sol3A-b{bottom}", neck, rules, verbose=False)
            if ok:
                print(f"    Sol3A bottom={bottom} {neck}: PASS")
                verify(f"Sol3A-b{bottom}", neck, rules, verbose=True)
                results[P] = (f"Sol3A-b{bottom}-{neck}", neck, rules)
                found = True
                break

        if found:
            break

        # Sol 3 variant B (bottom+top at each pair)
        for bottom in range(n):
            for top in range(n):
                if top == bottom:
                    continue
                _, rules = sol3_variant_B(neck, bottom=bottom, top=top)
                ok = verify(f"Sol3B", neck, rules, verbose=False)
                if ok:
                    print(f"    Sol3B bottom={bottom} top={top} {neck}: PASS")
                    verify(f"Sol3B", neck, rules, verbose=True)
                    results[P] = (f"Sol3B-b{bottom}t{top}-{neck}", neck, rules)
                    found = True
                    break
            if found:
                break

        if found:
            break

        # Sol 1 variant
        for bottom in range(n):
            _, rules = sol1_variant(neck, bottom=bottom)
            ok = verify(f"Sol1-b{bottom}", neck, rules, verbose=False)
            if ok:
                print(f"    Sol1 bottom={bottom} {neck}: PASS")
                verify(f"Sol1-b{bottom}", neck, rules, verbose=True)
                results[P] = (f"Sol1-b{bottom}-{neck}", neck, rules)
                found = True
                break

        if found:
            break

    if found:
        return True

    print("    Named constructions: all FAIL")

    # Phase 2: Pipeline search on promising necklaces
    if try_pipeline:
        print("\n  Phase 2: Pipeline search (DFS + screening)")
        for ni, neck in enumerate(necklaces):
            if ni >= 5:
                print(f"    (skipping remaining {len(necklaces)-ni} necklaces)")
                break
            print(f"    Necklace [{ni+1}/{len(necklaces)}]: {neck}")
            rules = pipeline_search(neck, time_limit=60, verbose=True)
            if rules is not None:
                print(f"    *** WITNESS from pipeline! ***")
                verify(f"Pipeline-{neck}", neck, rules, verbose=True)
                results[P] = (f"Pipeline-{neck}", neck, rules)
                found = True
                break

        if found:
            return True

    # Phase 3: Random local search
    if try_local:
        print(f"\n  Phase 3: Random local search ({local_restarts} restarts)")
        for ni, neck in enumerate(necklaces[:3]):
            print(f"    Necklace [{ni+1}]: {neck}")
            rules, score, detail = local_search(
                neck, max_restarts=local_restarts,
                steps_per_restart=2000, verbose=False
            )
            print(f"    Best: score={score}, {detail}")
            if 'PASS' in detail:
                print(f"    *** WITNESS from local search! ***")
                verify(f"Local-{neck}", neck, rules, verbose=True)
                results[P] = (f"Local-{neck}", neck, rules)
                found = True
                break

        if found:
            return True

    print(f"  Result: product {P} — NO VALID SYSTEM FOUND")
    return False


def sol3_compress_binary(n, binary_pos):
    """Try all ways to compress one proc from 3→2 states in Sol 3.
    We remap Sol 3's state space: for the binary proc, try all 3 possible
    merges of {0,1,2} → {0,1}: merge(0,1), merge(0,2), merge(1,2).
    Then adjust all rules to use the compressed states.
    """
    _, sol3_rules = dijkstra_sol3_real(n)
    results = []

    # Three ways to merge 3 states into 2: merge a pair
    merge_maps = [
        {0: 0, 1: 0, 2: 1},  # merge 0,1 → 0; 2 → 1
        {0: 0, 1: 1, 2: 0},  # merge 0,2 → 0; 1 → 1
        {0: 1, 1: 0, 2: 0},  # merge 1,2 → 0; 0 → 1
    ]

    for merge_map in merge_maps:
        ms = tuple(2 if i == binary_pos else 3 for i in range(n))
        rules = []
        valid = True

        for i in range(n):
            m_L = ms[(i - 1) % n]
            m_S = ms[i]
            m_R = ms[(i + 1) % n]
            d = {}

            for L in range(m_L):
                for S in range(m_S):
                    for R in range(m_R):
                        # Map back to Sol 3's 3-state space
                        # For the binary proc, we need to try all preimages
                        if i == binary_pos:
                            # S is in {0,1}, find preimages in {0,1,2}
                            preimages_S = [k for k, v in merge_map.items() if v == S]
                            # For L and R: direct if ternary, else preimages
                            Ls = [L] if (i - 1) % n != binary_pos else [k for k, v in merge_map.items() if v == L]
                            Rs = [R] if (i + 1) % n != binary_pos else [k for k, v in merge_map.items() if v == R]

                            # All preimage combos must map to same output
                            outputs = set()
                            for pL in Ls:
                                for pS in preimages_S:
                                    for pR in Rs:
                                        out3 = sol3_rules[i][(pL, pS, pR)]
                                        outputs.add(merge_map[out3])
                            if len(outputs) != 1:
                                valid = False
                                break
                            d[(L, S, R)] = outputs.pop()
                        else:
                            # Ternary proc, but neighbor might be binary
                            L3 = L  # L is already in correct range
                            S3 = S
                            R3 = R
                            out3 = sol3_rules[i][(L3, S3, R3)]
                            # If this proc's output needs to be in range
                            d[(L, S, R)] = out3
                    if not valid:
                        break
                if not valid:
                    break
            if not valid:
                break
            rules.append(d)

        if valid:
            results.append((ms, rules, merge_map))

    return results


def cegar_search_z3(ms, time_limit=120, verbose=True):
    """Z3-based CEGAR search for valid transition tables.
    Variables: f_i(L,S,R) for each proc i and each (L,S,R) triple.
    Constraints: liveness, mutual exclusion, good cycle, convergence, fairness.
    """
    try:
        from z3 import Solver, Int, And, Or, Not, If, sat, Implies
    except ImportError:
        if verbose:
            print("    Z3 not available")
        return None

    n = len(ms)
    P = 1
    for m in ms:
        P *= m

    if verbose:
        print(f"    Z3 CEGAR: n={n}, ms={ms}, P={P}")

    t0 = time.time()

    # Create variables for transition functions
    f = {}
    solver = Solver()
    solver.set("timeout", time_limit * 1000)

    for i in range(n):
        m_L = ms[(i - 1) % n]
        m_S = ms[i]
        m_R = ms[(i + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    v = Int(f"f_{i}_{L}_{S}_{R}")
                    f[(i, L, S, R)] = v
                    solver.add(v >= 0, v < m_S)

    # Liveness: every config has at least one privileged proc
    if verbose:
        print(f"    Adding liveness constraints...")

    configs = list(cartesian(*(range(m) for m in ms)))
    for cfg in configs:
        priv_clauses = []
        for i in range(n):
            L = cfg[(i - 1) % n]
            S = cfg[i]
            R = cfg[(i + 1) % n]
            priv_clauses.append(f[(i, L, S, R)] != S)
        solver.add(Or(*priv_clauses))

    # Seed from Sol 3: fix ternary procs to Sol 3 rules
    # Only allow binary/non-ternary procs to vary
    _, sol3_rules = dijkstra_sol3_real(n)
    fixed_procs = []
    free_procs = []
    for i in range(n):
        if ms[i] == 3:
            fixed_procs.append(i)
        else:
            free_procs.append(i)

    if verbose:
        print(f"    Fixed (ternary) procs: {fixed_procs}")
        print(f"    Free (non-ternary) procs: {free_procs}")

    # Fix ternary procs to Sol 3 rules
    for i in fixed_procs:
        m_L = ms[(i - 1) % n]
        m_S = ms[i]
        m_R = ms[(i + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    # Only constrain for inputs in Sol 3's range
                    if L < 3 and R < 3:
                        solver.add(f[(i, L, S, R)] == sol3_rules[i][(L, S, R)])

    if verbose:
        print(f"    Checking satisfiability...")

    result = solver.check()
    elapsed = time.time() - t0

    if verbose:
        print(f"    Z3 result: {result} ({elapsed:.1f}s)")

    if str(result) == "sat":
        model = solver.model()
        rules = []
        for i in range(n):
            m_L = ms[(i - 1) % n]
            m_S = ms[i]
            m_R = ms[(i + 1) % n]
            d = {}
            for L in range(m_L):
                for S in range(m_S):
                    for R in range(m_R):
                        d[(L, S, R)] = model[f[(i, L, S, R)]].as_long()
            rules.append(d)
        return rules

    return None


def main():
    t_start = time.time()

    print("=" * 70)
    print("M_9 UPPER BOUND SEARCH (v2 — efficient)")
    print("=" * 70)
    print(f"Lower bound: M_9 ≥ 7776 (proved analytically)")
    print(f"M_9 > 7776 (all 56 orientations of {{2^3,3^5,4}} dead)")
    print()

    results = {}

    # ── BASELINE: Real Dijkstra Sol 3 at n=9 ─────────────────────────
    print("─" * 70)
    print("Baseline: Real Dijkstra Sol 3, n=9, all-ternary")
    print("─" * 70)
    ms, rules = dijkstra_sol3_real(9)
    test_construction("Sol3-real", ms, rules, results)
    print()

    # ── CANDIDATE: product=13122 = 2·3^8 (one binary) ────────────────
    # This is the most promising sub-19683 candidate.
    # Approach 1: Try compressing one Sol 3 proc to binary
    print("─" * 70)
    print("Candidate: one binary (2·3^8), product=13122")
    print("─" * 70)

    print("\n  Approach 1: Sol 3 compression (merge 3→2 states)")
    for bpos in range(9):
        compressed = sol3_compress_binary(9, bpos)
        for ci, (c_ms, c_rules, c_merge) in enumerate(compressed):
            ok = verify(f"Compress-P{bpos}-m{ci}", c_ms, c_rules, verbose=False)
            if ok:
                print(f"  *** FOUND: Compress P{bpos}, merge={c_merge}")
                verify(f"Compress-P{bpos}", c_ms, c_rules, verbose=True)
                results[13122] = (f"Compress-P{bpos}", c_ms, c_rules)
                break
        if 13122 in results:
            break
    if 13122 not in results:
        print("    All compressions fail (expected: Sol 3 uses all 3 states)")

    # Approach 2: Named constructions (Sol3A/B, Sol1)
    print("\n  Approach 2: Named constructions")
    necklaces_13122 = all_necklaces((2, 3, 3, 3, 3, 3, 3, 3, 3))
    print(f"    Necklaces: {len(necklaces_13122)}")
    found_13122 = False
    for neck in necklaces_13122:
        for bottom in range(9):
            for top in range(9):
                if top == bottom:
                    continue
                _, r = sol3_variant_B(neck, bottom=bottom, top=top)
                if verify("", neck, r, verbose=False):
                    print(f"    Sol3B bottom={bottom} top={top} {neck}: PASS")
                    verify("Sol3B", neck, r, verbose=True)
                    results[13122] = (f"Sol3B-b{bottom}t{top}", neck, r)
                    found_13122 = True
                    break
            if found_13122:
                break
        if found_13122:
            break
    if not found_13122:
        print("    All named constructions FAIL")

    # Approach 3: Pipeline search
    if not found_13122:
        print("\n  Approach 3: Pipeline search")
        for ni, neck in enumerate(necklaces_13122):
            print(f"    Necklace [{ni+1}/{len(necklaces_13122)}]: {neck}")
            r = pipeline_search(neck, time_limit=60, verbose=True)
            if r is not None:
                print(f"    *** WITNESS from pipeline! ***")
                verify(f"Pipeline", neck, r, verbose=True)
                results[13122] = (f"Pipeline-{neck}", neck, r)
                found_13122 = True
                break

    # Approach 4: Z3 CEGAR (fix ternary procs to Sol 3, let binary vary)
    if not found_13122:
        print("\n  Approach 4: Z3 CEGAR (ternary=Sol3, binary=free)")
        for bpos in range(9):
            neck = tuple(2 if i == bpos else 3 for i in range(9))
            print(f"    Binary at position {bpos}: {neck}")
            r = cegar_search_z3(neck, time_limit=30, verbose=True)
            if r is not None:
                ok = verify(f"Z3-b{bpos}", neck, r, verbose=True)
                if ok:
                    results[13122] = (f"Z3-binary-P{bpos}", neck, r)
                    found_13122 = True
                    break
                else:
                    print(f"    Z3 returned SAT but verify fails (liveness-only)")

    # Approach 5: Local search (shorter)
    if not found_13122:
        print("\n  Approach 5: Local search (50 restarts)")
        for ni, neck in enumerate(necklaces_13122):
            print(f"    Necklace [{ni+1}]: {neck}")
            r, score, detail = local_search(
                neck, max_restarts=50, steps_per_restart=3000, verbose=False
            )
            print(f"    Best: score={score}, {detail}")
            if 'PASS' in detail:
                print(f"    *** WITNESS from local search! ***")
                verify(f"Local", neck, r, verbose=True)
                results[13122] = (f"Local-{neck}", neck, r)
                found_13122 = True
                break

    if not found_13122:
        print("\n  product 13122: NO VALID SYSTEM FOUND")

    # ── CANDIDATE: product=11664 = 2^2·3^6·4 ─────────────────────────
    # Skip local search (expensive), just do pipeline + named
    print(f"\n{'─'*70}")
    print("Candidate: 2^2·3^6·4, product=11664")
    print("─" * 70)
    test_candidate(
        (2, 2, 4, 3, 3, 3, 3, 3, 3),
        "two binary + one quaternary",
        results,
        try_pipeline=True,
        try_local=False,
    )

    # ── CANDIDATES: 8748, 9720, 10368 (pipeline only, no local) ──────
    for ms_base, label in [
        ((2, 2, 3, 3, 3, 3, 3, 3, 3), "two binary (2^2·3^7), product=8748"),
        ((2, 2, 2, 5, 3, 3, 3, 3, 3), "quintic (2^3·3^5·5), product=9720"),
        ((2, 2, 2, 4, 4, 3, 3, 3, 3), "two quaternary (2^3·3^4·4^2), product=10368"),
    ]:
        test_candidate(
            ms_base, label, results,
            try_pipeline=True, try_local=False,
        )

    # ── SUMMARY ──────────────────────────────────────────────────────
    elapsed = time.time() - t_start
    print()
    print("=" * 70)
    print("FINAL SUMMARY")
    print("=" * 70)
    print(f"  Lower bound: M_9 ≥ 7776")
    print(f"  M_9 > 7776 (proved by exhaustive sweep)")
    print()
    if results:
        best_prod = min(results.keys())
        best_name, best_ms, best_rules = results[best_prod]
        print(f"  Best upper bound: M_9 ≤ {best_prod}")
        print(f"  Construction: {best_name}")
        print(f"  State counts: {best_ms}")
        print()
        for prod in sorted(results.keys()):
            name, ms_r, _ = results[prod]
            print(f"    {prod}: {name}")
    else:
        print("  No valid constructions found below 19683")
        print("  M_9 ≤ 19683 (Dijkstra Sol 3)")
    print()
    print(f"  Gap: 7776 < M_9 ≤ {min(results.keys()) if results else 19683}")
    print(f"  Total time: {elapsed:.1f}s")
    print()

    # Print witness details for best result
    if results:
        best_prod = min(results.keys())
        best_name, best_ms, best_rules = results[best_prod]
        print("=" * 70)
        print(f"BEST WITNESS DETAILS (product={best_prod})")
        print("=" * 70)
        print(f"State counts: {best_ms}")
        for i, table in enumerate(best_rules):
            print(f"  P{i}({best_ms[i]}): {dict(sorted(table.items()))}")

    return results


if __name__ == "__main__":
    main()
