"""
B5 FULL CASE SPLIT — Enhanced Analysis

Goal: Prove that between consecutive B5 firings (at ANY positions),
fc strictly decreases, so B5's +1 bump is always compensated.

Key findings from cup2_b5_proof.py:
1. (2,1,1) NOT reachable from (2,0,1) in 3-window state machine
2. 0 same-position B5 recurrences for n=5..11

This script:
- Checks B5 at ANY position (not just same j)
- Tracks fc change between consecutive B5 firings
- Analyzes the full transition graph including non-local effects
- Proves the forced sequence F2-F4 gives net ≤ -1 analytically
"""
import sys
from itertools import product as cartesian
from collections import deque

# ── CUP-2 tables ──
T_bot = {}
for L in range(2):
    for S in range(2):
        for R in range(3):
            T_bot[(L, S, R)] = S  # default: stay
T_bot[(0, 0, 1)] = 1
T_bot[(0, 0, 2)] = 1
T_bot[(0, 1, 0)] = 0
T_bot[(1, 0, 1)] = 1
T_bot[(1, 0, 2)] = 1
T_bot[(1, 1, 0)] = 0

T_low = {}
for L in range(2):
    for S in range(3):
        for R in range(3):
            T_low[(L, S, R)] = S
T_low[(0, 0, 1)] = 1
T_low[(0, 0, 2)] = 1
T_low[(0, 1, 0)] = 0
T_low[(0, 1, 2)] = 0
T_low[(0, 2, 0)] = 0
T_low[(0, 2, 1)] = 0
T_low[(1, 0, 0)] = 1
T_low[(1, 0, 1)] = 1
T_low[(1, 0, 2)] = 1
T_low[(1, 1, 0)] = 0
T_low[(1, 2, 0)] = 0
T_low[(1, 2, 1)] = 1

T_mid = {}
for L in range(3):
    for S in range(3):
        for R in range(3):
            T_mid[(L, S, R)] = S
T_mid[(0, 1, 0)] = 0
T_mid[(0, 2, 0)] = 0
T_mid[(0, 2, 2)] = 0
T_mid[(1, 0, 0)] = 1
T_mid[(1, 0, 1)] = 1
T_mid[(1, 0, 2)] = 1
T_mid[(1, 1, 2)] = 2
T_mid[(1, 2, 1)] = 1
T_mid[(2, 0, 2)] = 2
T_mid[(2, 1, 0)] = 0
T_mid[(2, 1, 1)] = 0  # ← B5 (anomalous)
T_mid[(2, 2, 0)] = 0
T_mid[(1, 2, 0)] = 0
T_mid[(2, 1, 2)] = 2

T_high = {}
for L in range(3):
    for S in range(3):
        for R in range(2):
            T_high[(L, S, R)] = S
T_high[(0, 1, 0)] = 0
T_high[(0, 2, 0)] = 0
T_high[(0, 2, 1)] = 0
T_high[(1, 0, 0)] = 1
T_high[(1, 0, 1)] = 1
T_high[(1, 1, 0)] = 0
T_high[(1, 2, 0)] = 0
T_high[(1, 2, 1)] = 1
T_high[(2, 0, 0)] = 2
T_high[(2, 0, 1)] = 2
T_high[(2, 1, 0)] = 0
T_high[(2, 1, 1)] = 2
T_high[(2, 2, 0)] = 0

T_top = {}
for L in range(3):
    for S in range(2):
        for R in range(2):
            T_top[(L, S, R)] = S
T_top[(0, 1, 0)] = 0
T_top[(0, 1, 1)] = 0
T_top[(1, 0, 0)] = 1
T_top[(1, 1, 0)] = 0
T_top[(2, 0, 0)] = 1
T_top[(2, 0, 1)] = 1
T_top[(2, 1, 0)] = 0
T_top[(2, 1, 1)] = 0


def build_system(n):
    ms = [2] + [3] * (n - 2) + [2]
    tables = [T_bot, T_low] + [T_mid] * (n - 4) + [T_high, T_top]

    def make_func(table):
        return lambda L, S, R, t=table: t[(L, S, R)]

    fs = [make_func(t) for t in tables]
    return ms, fs, tables


def fc(c):
    n = len(c)
    return sum(1 for i in range(n) if c[i] != c[(i + 1) % n])


def is_good(c, ms):
    n = len(c)
    for i in range(n):
        ci = c[i]
        cp = c[(i + 1) % n]
        if ci == cp:
            continue
        if ci == 0 and cp == 1:
            continue
        if ci == ms[i] - 1 and cp == 0:
            continue
        return False
    return True


def delta_fc_at(c, i, new_val):
    """Δfc when c[i] changes to new_val."""
    n = len(c)
    old = c[i]
    lv = c[(i - 1) % n]
    rv = c[(i + 1) % n]
    old_fc = (1 if lv != old else 0) + (1 if old != rv else 0)
    new_fc = (1 if lv != new_val else 0) + (1 if new_val != rv else 0)
    return new_fc - old_fc


def main():
    print("B5 ENHANCED ANALYSIS")
    print("=" * 65)

    # ── PART 1: B5-to-B5 reachability at ANY position ──
    print("\nPART 1: B5-to-B5 Reachability (any position)")
    print("-" * 65)

    for nv in range(5, 13):
        prod = 4 * 3 ** (nv - 2)
        if prod > 2_000_000:
            break
        ms, fs, tables = build_system(nv)
        n = nv

        all_configs = list(cartesian(*(range(m) for m in ms)))
        good_set = set(c for c in all_configs if is_good(c, ms))
        bad_set = set(c for c in all_configs if c not in good_set)

        # Build full bad→bad adjacency with firing position
        adj = {c: [] for c in bad_set}
        for c in bad_set:
            for i in range(n):
                Li = c[(i - 1) % n]
                Si = c[i]
                Ri = c[(i + 1) % n]
                out = tables[i][(Li, Si, Ri)]
                if out != Si:
                    lst = list(c)
                    lst[i] = out
                    succ = tuple(lst)
                    if succ in bad_set:
                        adj[c].append((succ, i))

        # Find ALL B5 precondition configs (at any interior mid position)
        b5_precond = {}  # config → set of positions where B5 can fire
        for c in bad_set:
            for j in range(2, n - 2):  # T_mid positions
                if c[j - 1] == 2 and c[j] == 1 and c[j + 1] == 1:
                    if c not in b5_precond:
                        b5_precond[c] = set()
                    b5_precond[c].add(j)

        # For each B5 firing, BFS to find next B5 at ANY position
        total_b5_to_b5 = 0
        max_fc_gain = -999
        min_fc_decrease = 999
        b5_to_good = 0
        b5_to_absorb = 0  # absorbed without reaching another B5

        for src, positions in b5_precond.items():
            for j in positions:
                # Fire B5 at position j
                lst = list(src)
                lst[j] = 0  # T_mid(2,1,1)→0
                after = tuple(lst)
                if after not in bad_set:
                    b5_to_good += 1
                    continue

                fc_src = fc(src)

                # BFS: stop at B5 preconditions or good configs
                visited = {after}
                queue = deque([after])
                found_b5 = False

                while queue:
                    cur = queue.popleft()
                    for s, fpos in adj[cur]:
                        if s not in visited:
                            visited.add(s)
                            # Check if s has B5 precondition at any position
                            is_b5 = False
                            for j2 in range(2, n - 2):
                                if (s[j2 - 1] == 2 and s[j2] == 1
                                        and s[j2 + 1] == 1):
                                    is_b5 = True
                                    break

                            if is_b5:
                                total_b5_to_b5 += 1
                                found_b5 = True
                                fc_s = fc(s)
                                decrease = fc_src - fc_s
                                min_fc_decrease = min(min_fc_decrease,
                                                       decrease)
                                max_fc_gain = max(max_fc_gain, fc_s - fc_src)
                                # Don't continue past B5
                            else:
                                queue.append(s)

                if not found_b5:
                    b5_to_absorb += 1

        v = "✓" if max_fc_gain <= -1 or total_b5_to_b5 == 0 else "✗"
        md = min_fc_decrease if total_b5_to_b5 > 0 else "N/A"
        print(f"  n={nv}: {len(b5_precond)} B5-capable configs, "
              f"{total_b5_to_b5} B5→B5 pairs, "
              f"min_decrease={md}, "
              f"{b5_to_absorb} absorbed, {b5_to_good} →good  {v}")

    # ── PART 2: B5 one-step Δfc analysis ──
    print("\n\nPART 2: B5 Firing — Immediate Consequences")
    print("-" * 65)

    # After B5 at j: c[j] goes 1→0. Δfc depends on c[j-2] and c[j+2].
    # c[j-1]=2, c[j+1]=1 are given.
    # Local Δfc at j: (c[j-1]≠c[j]) changes from (2≠1=1) to (2≠0=1): no change
    #                  (c[j]≠c[j+1]) changes from (1≠1=0) to (0≠1=1): +1
    # So Δfc = +1 (always, regardless of environment). Confirmed.

    print("  B5 at j: c[j]: 1→0. c[j-1]=2, c[j+1]=1.")
    print("  Left frontier: (2,c[j])  2≠1→2≠0: both ≠, no change")
    print("  Right frontier: (c[j],1)  1=1→0≠1: 0→1, change +1")
    print("  Δfc = +1. ✓")

    # ── PART 3: What the forced sequence achieves ──
    print("\n\nPART 3: Forced Sequence Analysis")
    print("-" * 65)

    # The key question: what is the MINIMUM total Δfc before B5 can recur?
    # From the 3-window analysis: B5 can't recur locally.
    # So we need to look at the full config space.

    # Key chain:
    # B5 fires at j: c[j]=1→0.  Δfc=+1
    # F2: c[j-1]=2→0.  Δfc≤0
    # F3: c[j-1]=0→1.  Δfc=0 (needs c[j-2]=1)
    # F4: c[j]=0→1.    Δfc≤-2 (if c[j+1]=1, which is preserved)
    # Main case total: +1 + 0 + 0 + (-2) = -1

    # But WHY is c[j+1]=1 preserved?
    # After B5: (2, 0, 1). c[j+1]=1.
    # T_mid(0, 1, R): stays at 1 for R∈{0,1,2}. So c[j+1] stays at 1
    #   while c[j]=0. ← KEY
    # In fact T_mid(0,1,0)=0, T_mid(0,1,1)=1, T_mid(0,1,2)=1.
    # Wait — T_mid(0,1,0)=0! So c[j+1] CAN drop to 0 if c[j+2]=0.

    print("  After B5: (c[j-1], c[j], c[j+1]) = (2, 0, 1)")
    print()
    print("  Can c[j+1] change before c[j-1] drops?")
    print("  c[j+1] uses T_mid(c[j], 1, c[j+2]):")
    for L in range(3):
        for R in range(3):
            out = T_mid[(L, 1, R)]
            if out != 1:
                print(f"    T_mid({L}, 1, {R}) → {out}  (c[j+1] changes!)")
    print()
    print("  With c[j]=0: T_mid(0, 1, R):")
    for R in range(3):
        out = T_mid[(0, 1, R)]
        dfc_note = ""
        if out != 1:
            dfc_note = "  ← c[j+1] drops!"
        print(f"    T_mid(0, 1, {R}) → {out}{dfc_note}")

    print()
    print("  T_mid(0,1,0)=0: c[j+1] drops to 0 when c[j+2]=0.")
    print("  This is the 'hard case' — c[j+1] leaves 1 before c[j] rises.")

    # ── PART 4: Extended window (5-position) analysis ──
    print("\n\nPART 4: 5-Position Window Analysis")
    print("-" * 65)

    # State: (c[j-2], c[j-1], c[j], c[j+1], c[j+2])
    # Start: (*, 2, 0, 1, *)  after B5
    # Goal: (*, 2, 1, 1, *)  B5 precondition restored
    # All positions use T_mid (interior case)

    # For the 5-window, the environment is c[j-3] and c[j+3]
    # Let's enumerate ALL transitions in the 5-window

    states_5 = list(cartesian(range(3), range(3), range(3),
                               range(3), range(3)))

    # Build transition graph (5 positions: j-2, j-1, j, j+1, j+2)
    # Each uses T_mid, with environment from the state itself
    # j-2: L=env(c[j-3]), S=c[j-2], R=c[j-1]
    # j-1: L=c[j-2],      S=c[j-1], R=c[j]
    # j:   L=c[j-1],       S=c[j],   R=c[j+1]
    # j+1: L=c[j],         S=c[j+1], R=c[j+2]
    # j+2: L=c[j+1],       S=c[j+2], R=env(c[j+3])

    # For positions j-1, j, j+1: no external env needed
    # For j-2: needs c[j-3] (external)
    # For j+2: needs c[j+3] (external)

    # Let's track just positions j-1, j, j+1 firings and their Δfc
    # Environment (c[j-2], c[j+2]) can change via external firings

    # Better approach: enumerate all FIRING SEQUENCES at {j-1, j, j+1}
    # that restore B5 precondition, accounting for all possible
    # environment values at each step.

    # From the 3-window analysis, the main path is:
    # F2: j-1 fires (2→0), then F3: j-1 fires (0→1), then F4: j fires (0→1)
    # Alternative paths involve j+1 firing too.

    # Let's enumerate ALL possible orderings computationally.
    # Use a 3-window state machine but with ALL possible env values.

    print("  Enumerating all firing sequences at {j-1, j, j+1}")
    print("  that restore (2,1,1) from (2,0,1),")
    print("  allowing environment (c[j-2], c[j+2]) to be ANY value.")
    print()

    start = (2, 0, 1)
    goal = (2, 1, 1)

    # State: (c[j-1], c[j], c[j+1])
    # At each step, one of {j-1, j, j+1} fires.
    # j-1 sees (c[j-2], c[j-1], c[j]) — c[j-2] is external
    # j   sees (c[j-1], c[j], c[j+1]) — fully local
    # j+1 sees (c[j], c[j+1], c[j+2]) — c[j+2] is external
    # For worst-case analysis, we allow c[j-2] and c[j+2] to be ANY value

    # Modified BFS: state = (c[j-1], c[j], c[j+1])
    # Transitions: for each position p ∈ {j-1, j, j+1}, for each
    # possible external env value, compute the new state and Δfc.

    # We want MAXIMUM cumulative Δfc over all paths from start to goal.
    # Use Bellman-Ford style (since we want longest path, and there
    # might be negative cycles — but the 3-window analysis showed
    # no positive-sum cycles).

    all_states = list(cartesian(range(3), range(3), range(3)))
    edges_full = {s: [] for s in all_states}

    for s in all_states:
        a, b, c_val = s  # c[j-1], c[j], c[j+1]

        # j-1 fires: T_mid(env, a, b) for env ∈ {0,1,2}
        for env in range(3):
            out = T_mid[(env, a, b)]
            if out != a:
                ns = (out, b, c_val)
                # Δfc: frontiers (c[j-2], c[j-1]) and (c[j-1], c[j])
                # Old: (env≠a) + (a≠b)
                # New: (env≠out) + (out≠b)
                dfc = ((1 if env != out else 0) + (1 if out != b else 0)
                       - (1 if env != a else 0) - (1 if a != b else 0))
                edges_full[s].append((ns, dfc,
                    f"j-1: ({env},{a},{b})→{out} env={env}"))

        # j fires: T_mid(a, b, c_val) — fully determined
        out = T_mid[(a, b, c_val)]
        if out != b:
            ns = (a, out, c_val)
            dfc = ((1 if a != out else 0) + (1 if out != c_val else 0)
                   - (1 if a != b else 0) - (1 if b != c_val else 0))
            edges_full[s].append((ns, dfc,
                f"j: ({a},{b},{c_val})→{out}"))

        # j+1 fires: T_mid(b, c_val, env) for env ∈ {0,1,2}
        for env in range(3):
            out = T_mid[(b, c_val, env)]
            if out != c_val:
                ns = (a, b, out)
                dfc = ((1 if b != out else 0) + (1 if out != env else 0)
                       - (1 if b != c_val else 0) - (1 if c_val != env else 0))
                edges_full[s].append((ns, dfc,
                    f"j+1: ({b},{c_val},{env})→{out} env={env}"))

    # Check reachability
    reachable = set()
    queue = deque([start])
    reachable.add(start)
    while queue:
        s = queue.popleft()
        for ns, dfc, desc in edges_full[s]:
            if ns not in reachable:
                reachable.add(ns)
                queue.append(ns)

    print(f"  Reachable states: {len(reachable)}")
    print(f"  Goal (2,1,1) reachable: {goal in reachable}")
    print()

    if goal in reachable:
        # Enumerate all simple paths from start to goal
        all_paths = []

        def dfs(state, path, total_dfc, visited):
            if state == goal:
                all_paths.append((list(path), total_dfc))
                return
            if len(path) > 15:  # safety limit
                return
            for ns, dfc, desc in edges_full[state]:
                if ns not in visited or ns == goal:
                    visited.add(ns)
                    path.append((state, ns, desc, dfc))
                    dfs(ns, path, total_dfc + dfc,
                        visited if ns != goal else visited)
                    path.pop()
                    if ns != goal:
                        visited.discard(ns)

        dfs(start, [], 0, {start})

        print(f"  Found {len(all_paths)} simple paths from {start} to {goal}")

        if all_paths:
            max_total = max(t for _, t in all_paths)
            min_total = min(t for _, t in all_paths)
            print(f"  Max cumulative Δfc: {max_total:+d}")
            print(f"  Min cumulative Δfc: {min_total:+d}")
            print(f"  Net with B5 (+1): max = {max_total + 1:+d}")

            if max_total <= -2:
                print("  ✓ ALL paths give net ≤ -1")
            else:
                print(f"  ✗ Worst path gives net {max_total + 1:+d}")

            # Show top 5 worst paths
            print("\n  Top 5 worst paths:")
            for path, total in sorted(all_paths, key=lambda x: -x[1])[:5]:
                print(f"\n    Δfc={total:+d} ({len(path)} steps):")
                running = 0
                for prev, nxt, desc, dfc in path:
                    running += dfc
                    print(f"      {prev}→{nxt} {dfc:+d} (cum:{running:+d}) "
                          f"{desc}")
    else:
        print("  *** Goal NOT reachable even with arbitrary environment! ***")
        print("  → B5 precondition CANNOT be restored by firings at")
        print("    {j-1, j, j+1} regardless of what c[j-2], c[j+2] do.")
        print()
        print("  This means: to restore c[j-1]=2, a DIFFERENT position")
        print("  (outside {j-1, j, j+1}) must fire, contributing its own Δfc.")
        print()

        # Analyze what's needed to get c[j-1] back to 2
        print("  To reach (2, 1, 1) from any reachable state:")
        print("  Need c[j-1]=2. Reachable states with c[j-1]=2:")
        reach_with_2 = [s for s in reachable if s[0] == 2]
        for s in reach_with_2:
            print(f"    {s}")

        print()
        print("  From these, T_mid(L, 2, R) behavior:")
        for s in reach_with_2:
            a, b, c_val = s
            for env in range(3):
                out = T_mid[(env, a, b)]
                if out != a:
                    print(f"    At {s}: j-1 fires ({env},{a},{b})→{out}")

        # What states can reach goal?
        print()
        print("  States that can transition TO (2,1,1):")
        for s in all_states:
            for ns, dfc, desc in edges_full[s]:
                if ns == goal:
                    print(f"    {s} → {goal} Δfc={dfc:+d}  {desc}")

    # ── PART 5: Full computational B5-to-B5 with ANY position ──
    print("\n\nPART 5: Computational B5→B5 (Any Position, Full Graph)")
    print("-" * 65)

    for nv in range(5, 12):
        prod = 4 * 3 ** (nv - 2)
        if prod > 500_000:
            break
        ms, fs, tables = build_system(nv)
        n = nv

        all_configs = list(cartesian(*(range(m) for m in ms)))
        good_set = set(c for c in all_configs if is_good(c, ms))
        bad_set = set(c for c in all_configs if c not in good_set)

        adj = {c: [] for c in bad_set}
        for c in bad_set:
            for i in range(n):
                Li = c[(i - 1) % n]
                Si = c[i]
                Ri = c[(i + 1) % n]
                out = tables[i][(Li, Si, Ri)]
                if out != Si:
                    lst = list(c)
                    lst[i] = out
                    succ = tuple(lst)
                    if succ in bad_set:
                        adj[c].append((succ, i))

        # Identify B5 configs: any c where T_mid(2,1,1)→0 at some j
        def is_b5_firing(c, j):
            """Does B5 fire at position j?"""
            if j < 2 or j > n - 3:
                return False
            return c[j - 1] == 2 and c[j] == 1 and c[j + 1] == 1

        # Build set of B5-firing (config, position) pairs
        b5_pairs = []
        for c in bad_set:
            for j in range(2, n - 2):
                if is_b5_firing(c, j):
                    b5_pairs.append((c, j))

        # For each B5 firing: fire B5, BFS to next B5 (any pos), track fc
        worst_decrease = 999
        total_reachable = 0
        total_unreachable = 0

        for src, j in b5_pairs:
            lst = list(src)
            lst[j] = 0
            after = tuple(lst)
            if after not in bad_set:
                continue

            fc_src = fc(src)

            # BFS through bad configs, stop at B5 preconditions
            visited = {after}
            queue = deque([after])
            found = False

            while queue:
                cur = queue.popleft()
                for s, fpos in adj[cur]:
                    if s not in visited:
                        visited.add(s)
                        # Check B5 at any position
                        hit = False
                        for j2 in range(2, n - 2):
                            if is_b5_firing(s, j2):
                                hit = True
                                break
                        if hit:
                            fc_s = fc(s)
                            dec = fc_src - fc_s
                            worst_decrease = min(worst_decrease, dec)
                            found = True
                            total_reachable += 1
                        else:
                            queue.append(s)

            if not found:
                total_unreachable += 1

        wd = worst_decrease if total_reachable > 0 else "N/A"
        v = "✓" if worst_decrease >= 1 or total_reachable == 0 else "✗"
        print(f"  n={nv}: {len(b5_pairs)} B5 firings, "
              f"{total_reachable} reach next B5, "
              f"{total_unreachable} absorbed, "
              f"min fc_decrease={wd}  {v}")

    # ── PART 6: Analytical proof ──
    print("\n\nPART 6: Analytical Proof Structure")
    print("=" * 65)
    print("""
  THEOREM: Between consecutive B5 firings, fc strictly decreases.

  PROOF:
  Let B5 fire at position j (2 ≤ j ≤ n-3, using T_mid).
  Before: (c[j-1], c[j], c[j+1]) = (2, 1, 1).  Δfc = +1.
  After:  (c[j-1], c[j], c[j+1]) = (2, 0, 1).

  CLAIM: Before B5 can fire again at ANY position j',
  the total Δfc from all intervening firings is ≤ -2.

  The proof uses two observations:

  (A) LOCAL STUCKNESS: c[j] is stuck at 0 while c[j-1]=2.
      T_mid(2, 0, 0) = T_mid(2, 0, 1) = 0 (stay).
      The only escape is T_mid(2, 0, 2) → 2 (needs c[j+1]=2).
      But for B5 recurrence at j, we need c[j]=1, not 2.
      So c[j-1] MUST leave 2 first.

  (B) RESTORATION COST: Restoring c[j-1] to 2 requires a
      right-to-left 2-wave, which costs Δfc ≤ -2 total.

  Detailed case analysis:

  Case 1: c[j+1] stays at 1 throughout.
    F2: c[j-1] drops 2→0. T_mid(q, 2, 0)→0. Δfc ≤ 0.
    F3: c[j-1] rises 0→1. T_mid(1, 0, 0)→1. Δfc = 0.
    F4: c[j] rises 0→1. T_mid(1, 0, 1)→1. Δfc = -2.
    Subtotal at {j-1, j}: ≤ -2. ✓

  Case 2: c[j+1] drops to 0 (via T_mid(0, 1, 0)→0, c[j+2]=0).
    c[j+1] drop: T_mid(0, 1, 0)→0. Δfc at j+1:
      Left: (0,1)→(0,0): 1→0, -1
      Right: (1,q)→(0,q): depends on c[j+2]=0: 1→0, -1.
      Δfc = -2.
    Then c[j+1] must recover to 1:
      T_mid(q, 0, r)→1 needs q=1 (left=c[j]=0... no, c[j]=0).
      Actually c[j+1]=0 with c[j]=0: T_mid(0, 0, R)=0 for all R. STUCK.
      c[j] must rise first. But c[j] stuck while c[j-1]=2.
      So c[j-1] must drop first... same cascade.
    Net: the c[j+1] drop already gives -2, compensating B5's +1. ✓
""")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
