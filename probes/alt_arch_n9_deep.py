#!/usr/bin/env python3
"""alt_arch_n9_deep.py — Deeper follow-up searches for n=9 alternative architectures.

Phase A: Short-cycle search for multiset A orientations (max_depth=30)
Phase B: Longer probes for multiset B (60s each)
Phase C: Full SMT formulation for one promising orientation
"""

import sys
import os
import time
from itertools import product as cartesian
from collections import Counter

sys.path.insert(0, os.path.dirname(__file__))

from p2_good_cycle_search import (
    enumerate_good_cycles, search_good_cycle, local_context,
    transition_cache
)
from p2_completion_search import has_fatal_forced_cycle_singletons
from p2_cycle_screen import forced_rule_map
from p2_ring import verify_system, RingSystem
from p2_smt_completion import solve_cycle_with_smt

import z3


def prod(sc):
    p = 1
    for m in sc:
        p *= m
    return p


# ═══════════════════════════════════════════════════════════════
# Phase A: Short-cycle search for multiset A
# ═══════════════════════════════════════════════════════════════

def phase_a():
    """Search for SHORT good cycles (max_depth=30) on A orientations."""
    print("=" * 70)
    print("PHASE A: Short-cycle search (max_depth=30) for multiset A")
    print("=" * 70)

    # Orientations that found cycles in Phase 1 or had high node counts
    orientations = [
        (2, 2, 3, 6, 3, 3, 2, 3, 2),  # A2: found cycle len=78
        (2, 2, 2, 3, 2, 3, 6, 3, 3),  # sweep: found cycle len=78
        (2, 3, 2, 3, 6, 3, 2, 3, 2),  # A1: 422K nodes, no cycle in 10s
        (6, 2, 3, 2, 3, 2, 3, 3, 2),  # A3: 478K nodes
        (2, 3, 6, 3, 2, 3, 2, 3, 2),  # A4: 616K nodes
    ]

    for sc in orientations:
        sc_str = ','.join(map(str, sc))
        print(f"\n  ({sc_str}) max_depth=30, time=60s")
        t0 = time.time()

        screened = survivors = 0
        cycle_lengths = []

        for cycle, movers in enumerate_good_cycles(
            sc, time_limit=60.0, max_cycles=5000, max_depth=30
        ):
            screened += 1
            cycle_lengths.append(len(cycle))

            cycle_set = frozenset(cycle)
            try:
                fm = forced_rule_map(cycle, movers)
            except ValueError:
                continue

            if has_fatal_forced_cycle_singletons(sc, cycle_set, fm):
                continue

            survivors += 1
            print(f"    SURVIVOR: len={len(cycle)} movers={movers}")

            result = solve_cycle_with_smt(sc, cycle, movers, timeout_ms=60000)
            print(f"    SMT: {result.message} ({result.elapsed:.1f}s)")
            if result.found and result.system is not None:
                print(f"    *** WITNESS FOUND! ***")
                return result.system

            if survivors >= 10:
                break

        elapsed = time.time() - t0
        if cycle_lengths:
            print(f"    screened={screened} survivors={survivors} "
                  f"lengths={min(cycle_lengths)}-{max(cycle_lengths)} "
                  f"({elapsed:.1f}s)")
        else:
            print(f"    No cycles found with max_depth=30 ({elapsed:.1f}s)")

    return None


# ═══════════════════════════════════════════════════════════════
# Phase B: Longer probes for multiset B
# ═══════════════════════════════════════════════════════════════

def phase_b():
    """Run 60s probes on B orientations to see if cycles exist at all."""
    print(f"\n{'=' * 70}")
    print("PHASE B: Longer probes (60s) for multiset B")
    print("=" * 70)

    orientations = [
        (2, 3, 2, 3, 2, 9, 2, 3, 2),
        (9, 2, 3, 2, 2, 3, 2, 3, 2),
        (2, 2, 3, 9, 2, 3, 2, 3, 2),
        (2, 3, 2, 9, 2, 3, 2, 2, 3),
        (2, 3, 2, 2, 9, 2, 3, 2, 3),
    ]

    for sc in orientations:
        sc_str = ','.join(map(str, sc))
        p = prod(sc)
        print(f"\n  ({sc_str}) product={p}")
        t0 = time.time()
        result = search_good_cycle(sc, time_limit=60.0)
        elapsed = time.time() - t0
        if result.cycle is not None:
            print(f"    FOUND: length={len(result.cycle)} "
                  f"({result.stats.nodes} nodes, {elapsed:.1f}s)")
            # Try screening + SMT
            cycle_set = frozenset(result.cycle)
            try:
                fm = forced_rule_map(result.cycle, result.movers)
                fatal = has_fatal_forced_cycle_singletons(sc, cycle_set, fm)
                print(f"    Screening: {'FATAL' if fatal else 'SURVIVES'}")
                if not fatal:
                    smt = solve_cycle_with_smt(
                        sc, result.cycle, result.movers, timeout_ms=120000
                    )
                    print(f"    SMT: {smt.message} ({smt.elapsed:.1f}s)")
                    if smt.found and smt.system is not None:
                        print(f"    *** WITNESS! ***")
                        return smt.system
            except ValueError as e:
                print(f"    Screen error: {e}")
        else:
            print(f"    NONE: {result.stats.nodes} nodes, {elapsed:.1f}s")

    return None


# ═══════════════════════════════════════════════════════════════
# Phase C: Full SMT formulation
# ═══════════════════════════════════════════════════════════════

def full_smt_search(state_counts, cycle_length=18, timeout_s=300):
    """
    Full SMT encoding of all 5 Dijkstra properties.

    Variables:
      - f[i][L][S][R]: rule table entries
      - c[t][j]: configuration at cycle step t, processor j
      - mover[t]: which processor moves at step t
      - rank[cfg_idx]: convergence ranking for off-cycle configs
    """
    n = len(state_counts)
    L = cycle_length
    total_configs = prod(state_counts)

    print(f"\n  Full SMT: n={n}, cycle_len={L}, "
          f"state_counts={state_counts}, configs={total_configs}")

    solver = z3.Solver()
    solver.set("timeout", timeout_s * 1000)

    # ── Rule table variables ──
    f = {}
    for i in range(n):
        m_L = state_counts[(i - 1) % n]
        m_S = state_counts[i]
        m_R = state_counts[(i + 1) % n]
        for l_val in range(m_L):
            for s_val in range(m_S):
                for r_val in range(m_R):
                    var = z3.Int(f'f_{i}_{l_val}_{s_val}_{r_val}')
                    f[(i, l_val, s_val, r_val)] = var
                    solver.add(var >= 0, var < m_S)

    # ── Helper: look up f[i] for variable context ──
    def f_lookup(i, left_var, self_var, right_var):
        """Build if-then-else chain for f[i](left, self, right)."""
        m_L = state_counts[(i - 1) % n]
        m_S = state_counts[i]
        m_R = state_counts[(i + 1) % n]

        # Build list of (condition, value) pairs
        result = f[(i, 0, 0, 0)]  # default (shouldn't matter)
        for l_val in range(m_L):
            for s_val in range(m_S):
                for r_val in range(m_R):
                    cond = z3.And(
                        left_var == l_val,
                        self_var == s_val,
                        right_var == r_val
                    )
                    result = z3.If(cond,
                                   f[(i, l_val, s_val, r_val)],
                                   result)
        return result

    # ── Cycle configuration variables ──
    c = []
    for t in range(L):
        step = []
        for j in range(n):
            var = z3.Int(f'c_{t}_{j}')
            step.append(var)
            solver.add(var >= 0, var < state_counts[j])
        c.append(step)

    # c[0] = (0, 0, ..., 0) WLOG
    for j in range(n):
        solver.add(c[0][j] == 0)

    # All configs in cycle must be distinct
    for t1 in range(L):
        for t2 in range(t1 + 1, L):
            solver.add(z3.Or([c[t1][j] != c[t2][j] for j in range(n)]))

    # ── Mover variables ──
    mover = []
    for t in range(L):
        var = z3.Int(f'mover_{t}')
        mover.append(var)
        solver.add(var >= 0, var < n)

    # Fairness: all processors must appear as mover
    for j in range(n):
        solver.add(z3.Or([mover[t] == j for t in range(L)]))

    # ── Cycle transition constraints ──
    for t in range(L):
        t_next = (t + 1) % L

        for j in range(n):
            left_j = c[t][(j - 1) % n]
            self_j = c[t][j]
            right_j = c[t][(j + 1) % n]
            f_val = f_lookup(j, left_j, self_j, right_j)

            # If j is the mover: c[t+1][j] = f_val and f_val != self_j
            # If j is not the mover: c[t+1][j] = self_j and f_val == self_j
            solver.add(z3.If(
                mover[t] == j,
                z3.And(c[t_next][j] == f_val, f_val != self_j),
                z3.And(c[t_next][j] == self_j, f_val == self_j)
            ))

    # ── Liveness ──
    all_cfgs = list(cartesian(*(range(m) for m in state_counts)))

    # For configs NOT in the cycle, encode liveness
    # (Cycle configs already have exactly one privileged processor)
    # We encode liveness for ALL configs
    for cfg in all_cfgs:
        priv_lits = []
        for j in range(n):
            l_val = cfg[(j - 1) % n]
            s_val = cfg[j]
            r_val = cfg[(j + 1) % n]
            priv_lits.append(f[(j, l_val, s_val, r_val)] != s_val)
        solver.add(z3.Or(priv_lits))

    # ── Convergence (ranking function) ──
    # For each off-cycle config, all moves must decrease rank
    # We use config index as identifier
    cfg_to_idx = {cfg: idx for idx, cfg in enumerate(all_cfgs)}

    # We need a way to determine if a config is in the cycle.
    # Since cycle configs are z3 variables, this is hard to encode directly.
    # Alternative: use a boolean indicator for each config
    in_cycle = []
    for idx, cfg in enumerate(all_cfgs):
        var = z3.Bool(f'in_cycle_{idx}')
        in_cycle.append(var)
        # cfg is in cycle iff it equals some c[t]
        solver.add(var == z3.Or([
            z3.And([c[t][j] == cfg[j] for j in range(n)])
            for t in range(L)
        ]))

    # Exactly L configs are in the cycle
    solver.add(z3.Sum([z3.If(ic, 1, 0) for ic in in_cycle]) == L)

    # Rank variables for off-cycle configs
    rank = []
    for idx in range(len(all_cfgs)):
        var = z3.Int(f'rank_{idx}')
        rank.append(var)
        solver.add(var >= 0, var < total_configs)

    # Convergence: for each off-cycle config, all successors decrease rank
    for idx, cfg in enumerate(all_cfgs):
        for j in range(n):
            l_val = cfg[(j - 1) % n]
            s_val = cfg[j]
            r_val = cfg[(j + 1) % n]
            f_val_var = f[(j, l_val, s_val, r_val)]

            # If this processor is privileged at cfg (f_val != s_val)
            # and cfg is off-cycle, then the successor must have lower rank
            for new_s in range(state_counts[j]):
                if new_s == s_val:
                    continue
                # Successor config
                succ = list(cfg)
                succ[j] = new_s
                succ_tuple = tuple(succ)
                succ_idx = cfg_to_idx[succ_tuple]

                # If f_val == new_s (this is the actual transition)
                # and cfg is off-cycle
                # and successor is off-cycle: rank[succ] < rank[cfg]
                solver.add(z3.Implies(
                    z3.And(
                        f_val_var == new_s,
                        z3.Not(in_cycle[idx])
                    ),
                    z3.If(
                        in_cycle[succ_idx],
                        True,  # successor in cycle: always good
                        rank[succ_idx] < rank[idx]
                    )
                ))

    print(f"  SMT encoding complete. Solving (timeout {timeout_s}s)...")
    t0 = time.time()
    status = solver.check()
    elapsed = time.time() - t0

    if status == z3.sat:
        model = solver.model()
        # Extract rule tables
        rules = []
        for i in range(n):
            table = {}
            m_L = state_counts[(i - 1) % n]
            m_S = state_counts[i]
            m_R = state_counts[(i + 1) % n]
            for l_val in range(m_L):
                for s_val in range(m_S):
                    for r_val in range(m_R):
                        var = f[(i, l_val, s_val, r_val)]
                        table[(l_val, s_val, r_val)] = model.eval(var).as_long()
            rules.append(table)

        system = RingSystem(state_counts=tuple(state_counts), rules=tuple(rules))
        v = verify_system(system)
        print(f"  SAT! Verification: {v.message} ({elapsed:.1f}s)")
        if v.valid:
            print(f"  *** WITNESS FOUND ***")
            return system
        else:
            print(f"  SAT but failed verification.")
            return None

    elif status == z3.unsat:
        print(f"  UNSAT: no valid system exists with cycle length {L} "
              f"({elapsed:.1f}s)")
        return None
    else:
        reason = solver.reason_unknown()
        print(f"  UNKNOWN: {reason} ({elapsed:.1f}s)")
        return None


def phase_c():
    """Full SMT formulation for promising orientations."""
    print(f"\n{'=' * 70}")
    print("PHASE C: Full SMT formulation")
    print("=" * 70)

    # Try the most promising A orientation
    sc = (2, 2, 3, 6, 3, 3, 2, 3, 2)  # A2: found cycles

    for cycle_len in [18, 20, 22, 24]:
        print(f"\n  --- ({','.join(map(str, sc))}) cycle_len={cycle_len} ---")
        witness = full_smt_search(sc, cycle_length=cycle_len, timeout_s=300)
        if witness is not None:
            return witness

    return None


def main():
    # Phase A
    witness = phase_a()
    if witness:
        print("\n*** WITNESS FROM PHASE A ***")
        v = verify_system(witness)
        print(f"  {v.message}")
        print(f"  State counts: {witness.state_counts}, product: {witness.size}")
        return

    # Phase B
    witness = phase_b()
    if witness:
        print("\n*** WITNESS FROM PHASE B ***")
        v = verify_system(witness)
        print(f"  {v.message}")
        return

    # Phase C
    witness = phase_c()
    if witness:
        print("\n*** WITNESS FROM PHASE C ***")
        v = verify_system(witness)
        print(f"  {v.message}")
        return

    print("\n" + "=" * 70)
    print("All phases exhausted. No witness found.")
    print("=" * 70)


if __name__ == "__main__":
    main()
