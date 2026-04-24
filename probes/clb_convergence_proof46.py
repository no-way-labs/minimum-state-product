#!/usr/bin/env python3
"""
CONVERGENCE PROOF 46: Cascade Automaton & Pumping Argument
============================================================

IDEA: The interior cascade is a finite-state transducer operating on
the interior word u[2..n-3]. If the transducer has S effective states,
and we verify DAG for n up to S+4, then NO cycle exists for any n.

The cascade at interior position j sees:
  - Written value at j-1 (propagated from boundary or previous cascade step)
  - Original value at j: u[j]
  - Original value at j+1: u[j+1]

The cascade transition: T_mid(written_prev, u[j], u[j+1]) → out
  If out ≠ u[j] and Δfc ≤ 0: cascade continues with written_value = out
  Otherwise: cascade stops at this direction

CASCADE STATE: (last_written_value, active_direction)
  - last_written ∈ {0, 1, 2}
  - direction ∈ {left_to_right, right_to_left, done}

EFFECTIVE STATES: compute from actual cascade dynamics.

Also: check EXCURSION EDGE as transducer.
For the excursion (src → tgt), the interior mapping is:
  u[2..n-3] → v[2..n-3]
where v is determined by the boundary config + cascade.

Model as: for each boundary type, the mapping u→v at each interior
position depends on a running "state" propagated from one end.
Count the effective states.
"""

import sys
import os
import time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system, T_mid
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict


def delta_fc(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))


def build_excursion_graph_full(n_val):
    """Return excursion edges AND the full cascade paths."""
    ms, fs = build_system(n_val)
    n = n_val
    result = verify_system(ms, fs)
    assert result['valid']
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    anom_edges = []
    dfc_le0_adj = defaultdict(list)
    for c in bad_list:
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            out = fs[i](L, S, R)
            if out != S:
                lst = list(c); lst[i] = out; succ = tuple(lst)
                if succ in bad_set:
                    dfc = delta_fc(L, S, R, out)
                    if dfc <= 0: dfc_le0_adj[c].append(succ)
                    if out != L and out != R: anom_edges.append((c, succ, i, dfc))

    anom_sources = set(c for c, _, _, _ in anom_edges)
    anom_target_map = defaultdict(list)
    for c, succ, i, dfc in anom_edges:
        anom_target_map[succ].append(c)

    exc_edges = set()
    for b in set(s for _, s, _, _ in anom_edges):
        visited = set(); queue = [b]; visited.add(b); head = 0
        while head < len(queue):
            node = queue[head]; head += 1
            if node in anom_sources:
                for src in anom_target_map.get(b, []):
                    exc_edges.add((src, node))
            for nxt in dfc_le0_adj.get(node, []):
                if nxt not in visited:
                    visited.add(nxt); queue.append(nxt)

    return list(exc_edges), ms


def main():
    # ═══════════════════════════════════════════════════════════
    # PART A: Enumerate T_mid cascade transitions
    # ═══════════════════════════════════════════════════════════
    print("=" * 70)
    print("PART A: T_mid Δfc≤0 cascade transitions")
    print("=" * 70)
    print()
    print("For each (L,S,R) with Δfc≤0 firing, the cascade state transition:")
    print("  State = (last_written_value, original_S, original_R)")
    print("  → (new_written_value = output, next_original_S = R, next_original_R = ???)")
    print()

    # The cascade reads the interior word LEFT to RIGHT
    # At position j: state = (prev_written = v[j-1], u[j], u[j+1])
    # T_mid(v[j-1], u[j], u[j+1]) → output
    # If output ≠ u[j] and Δfc ≤ 0: v[j] = output, advance to j+1
    # State becomes: (output, u[j+1], u[j+2])
    # So the "running state" is just the last written value

    # Enumerate all cascade transitions
    print("Left-to-right cascade transitions (last_written, S, R) → output:")
    l2r_transitions = {}
    for lw in range(3):
        for S in range(3):
            for R in range(3):
                out = T_mid[(lw, S, R)]
                dfc = delta_fc(lw, S, R, out)
                if out != S and dfc <= 0:
                    cls = "copy_L" if out == lw else ("copy_R" if out == R else "anom")
                    l2r_transitions[(lw, S, R)] = (out, cls)
                    print(f"  ({lw},{S},{R}) → {out} [{cls}], new_state={out}")

    print(f"\n  Total L→R transitions: {len(l2r_transitions)}")

    # Enumerate effective cascade states
    # State = last_written_value ∈ {0, 1, 2}
    # For each state and each (S,R), the cascade either continues or stops
    print(f"\n  State space: {{0, 1, 2}} = 3 states")
    print(f"\n  Transition table:")
    for lw in range(3):
        continues = 0
        stops = 0
        for S in range(3):
            for R in range(3):
                if (lw, S, R) in l2r_transitions:
                    continues += 1
                else:
                    stops += 1
        print(f"    State {lw}: {continues}/9 continue, {stops}/9 stop")

    # ═══════════════════════════════════════════════════════════
    # Similarly for right-to-left cascade
    # ═══════════════════════════════════════════════════════════
    print(f"\nRight-to-left cascade transitions (L, S, last_written) → output:")
    r2l_transitions = {}
    for L in range(3):
        for S in range(3):
            for rw in range(3):
                out = T_mid[(L, S, rw)]
                dfc = delta_fc(L, S, rw, out)
                if out != S and dfc <= 0:
                    cls = "copy_L" if out == L else ("copy_R" if out == rw else "anom")
                    r2l_transitions[(L, S, rw)] = (out, cls)
                    print(f"  ({L},{S},{rw}) → {out} [{cls}], new_state={out}")

    print(f"\n  Total R→L transitions: {len(r2l_transitions)}")

    # ═══════════════════════════════════════════════════════════
    # PART B: For each zero-edge excursion, trace the cascade state
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("PART B: Cascade state sequences in actual zero-edge excursions")
    print("=" * 70)

    for n_val in [8, 9, 10]:
        t0 = time.time()
        exc_edges, ms = build_excursion_graph_full(n_val)
        n = n_val

        # For zero edges, trace the "comparison state" at each interior position
        # Comparison state at j: (u[j], v[j]) ∈ {0,1,2}²
        # This is the state of the "comparison transducer"
        state_sequences = set()
        n_zero = 0

        for u, v in exc_edges:
            # Check if zero edge
            d21 = sum(j * (int(u[j] == 2 and u[(j+1)%n] == 1) -
                           int(v[j] == 2 and v[(j+1)%n] == 1))
                       for j in range(2, n-2))
            if d21 != 0:
                continue
            n_zero += 1

            # State sequence: (u[j], v[j]) at interior positions
            seq = tuple((u[j], v[j]) for j in range(2, n-2))
            state_sequences.add(seq)

        dt = time.time() - t0
        print(f"\n  n={n_val}: {n_zero} zero-edges ({dt:.1f}s)")
        print(f"  Distinct state sequences: {len(state_sequences)}")

        # Analyze state sequence patterns
        # Each element is (u[j], v[j]) ∈ {0,1,2}²
        # How many distinct elements appear?
        all_states = set()
        for seq in state_sequences:
            for s in seq:
                all_states.add(s)
        print(f"  Distinct (u,v) states: {len(all_states)} = {sorted(all_states)}")

        # Transition analysis: what (u[j],v[j]) → (u[j+1],v[j+1]) transitions occur?
        transitions = set()
        for seq in state_sequences:
            for i in range(len(seq) - 1):
                transitions.add((seq[i], seq[i+1]))
        print(f"  Distinct transitions: {len(transitions)}")

        # State at EACH position (to check if there's a position-independent pattern)
        for pos in [2, 3, n//2, n-4, n-3]:
            if pos < 2 or pos > n-3:
                continue
            pos_states = set()
            for seq in state_sequences:
                idx = pos - 2
                if idx < len(seq):
                    pos_states.add(seq[idx])
            if pos <= 3 or pos >= n-4:
                label = f"pos={pos}"
            else:
                label = f"pos={pos}(mid)"
            print(f"    {label}: {len(pos_states)} states: {sorted(pos_states)}")

    # ═══════════════════════════════════════════════════════════
    # PART C: Pumping analysis — find loops in state sequences
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("PART C: State sequence loop analysis")
    print("=" * 70)
    print("Do state sequences have repeated states (pumping opportunities)?")

    for n_val in [9, 10, 11]:
        t0 = time.time()
        exc_edges, ms = build_excursion_graph_full(n_val)
        n = n_val

        n_zero = 0
        has_repeat = 0
        max_repeat_free = 0
        repeat_states = defaultdict(int)

        for u, v in exc_edges:
            d21 = sum(j * (int(u[j] == 2 and u[(j+1)%n] == 1) -
                           int(v[j] == 2 and v[(j+1)%n] == 1))
                       for j in range(2, n-2))
            if d21 != 0:
                continue
            n_zero += 1

            # Check for repeated (u[j], v[j]) in the interior
            seen = {}
            found_repeat = False
            for j in range(2, n-2):
                state = (u[j], v[j])
                if state in seen:
                    found_repeat = True
                    repeat_states[state] += 1
                    break
                seen[state] = j
            if found_repeat:
                has_repeat += 1
            max_repeat_free = max(max_repeat_free, len(seen))

        dt = time.time() - t0
        print(f"\n  n={n_val}: {n_zero} zero-edges ({dt:.1f}s)")
        print(f"    Has repeated (u,v) state: {has_repeat}/{n_zero} "
              f"({100*has_repeat/n_zero:.1f}%)")
        print(f"    Max repeat-free length: {max_repeat_free} "
              f"(out of {n-4} interior positions)")
        print(f"    Most repeated states: {dict(sorted(repeat_states.items(),\
              key=lambda x: -x[1])[:5])}")


if __name__ == '__main__':
    main()
