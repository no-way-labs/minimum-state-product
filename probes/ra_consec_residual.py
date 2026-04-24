#!/usr/bin/env python3
"""
Investigation: 3CB residual sorry in Sweep/OddWinding.

Questions:
1. Understand the normalForm counterexample (ms=(3,2,2,2,2,2,2,2,2) at n=9)
2. Does the residual ever occur under sub-threshold + convergence?
3. If so, what mechanism gives EC?
4. If not, proof that dispatch always fires under real hypotheses.

The counterexample mover word is (0,0,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1).
This is a pure CW sweep with extra 0-fires at the start.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))

from itertools import product as cartesian
from collections import defaultdict, Counter
from verifier import all_configs, privileged_set, apply_move, verify_system


# ─── Counterexample analysis ──────────────────────────────────────────

def analyze_counterexample():
    """Analyze the normalForm counterexample from sweep_consec_normalform_route.md"""
    print("=" * 70)
    print("PART 1: Counterexample analysis")
    print("=" * 70)

    # ms = (3,2,2,2,2,2,2,2,2), n=9
    # Mover word: (0,0,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1)
    # Pivot t=0 (the ternary proc), neighbors are proc 8 (left) and proc 1 (right)
    # Both neighbors are binary

    ms = (3, 2, 2, 2, 2, 2, 2, 2, 2)
    n = len(ms)
    mover_word = [0, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0, 8, 7, 6, 5, 4, 3, 2, 1]
    L = len(mover_word)

    print(f"\nms = {ms}")
    print(f"n = {n}")
    print(f"product = {eval('*'.join(str(m) for m in ms))} = 3 * 2^8 = 768")
    print(f"sub-threshold = 4 * 3^(n-2) = 4 * 3^7 = {4 * 3**7}")
    print(f"product < sub-threshold? {768 < 4 * 3**7}")
    print(f"\nMover word length = {L}")
    print(f"Mover word = {mover_word}")

    # Fire counts
    fc = Counter(mover_word)
    print(f"\nFire counts:")
    for p in range(n):
        print(f"  proc {p} (m={ms[p]}): fires {fc[p]} times")

    # Check: is this a sweep?
    # A sweep visits procs in a single direction
    # This visits 0,0,8,7,...,1,0,8,7,...,1 — it's a double CW sweep with extra 0
    print(f"\nIs sweep? The word does CW sweep twice with extra proc-0 fires")

    # The 3 consecutive binary procs: procs 1,2,3 (or any 3 consecutive among 1-8)
    # But the doc says pivot t=0 (ternary), both neighbors binary
    # left(0) = 8 (binary), right(0) = 1 (binary)
    # So the "3 consecutive binary" is procs 8, (0 is ternary in between), but wait...
    # Actually: 3CB means 3 consecutive procs ALL binary.
    # Procs 1-8 are all binary. So ANY 3 consecutive among {1,...,8} are 3CB.
    # e.g. procs 1,2,3 or 6,7,8 etc.

    # The relevant setup for the sorry:
    # 3CB at {i, right(i), right^2(i)} all binary
    # Middle proc right(i) is the pivot
    # For this ms, take i=1, right(i)=2, right^2(i)=3, all binary (m=2)

    # Phases at proc 2 (middle binary):
    # fc(2) = 2 (fires at positions 1 and 10 in 0-indexed: steps where mover=2)
    # Wait, let me recount
    steps_for_2 = [k for k, m in enumerate(mover_word) if m == 2]
    print(f"\n  Steps where proc 2 fires: {steps_for_2}")
    print(f"  fc(2) = {len(steps_for_2)}")

    # Phases at proc 2: gaps between consecutive firings
    # Phase between step steps_for_2[0] and steps_for_2[1]
    if len(steps_for_2) >= 2:
        for idx in range(len(steps_for_2)):
            s1 = steps_for_2[idx]
            s2 = steps_for_2[(idx + 1) % len(steps_for_2)]
            gap_steps = []
            k = (s1 + 1) % L
            while k != s2:
                gap_steps.append(k)
                k = (k + 1) % L
            J = sum(1 for k in gap_steps if mover_word[k] == 1)  # left neighbor fires
            K = sum(1 for k in gap_steps if mover_word[k] == 3)  # right neighbor fires
            print(f"  Phase {idx}: steps {s1}→{s2}, gap length {len(gap_steps)}, J(left)={J}, K(right)={K}")

    # The key question: is this sub-threshold?
    product = 1
    for m in ms:
        product *= m
    threshold = 4 * 3 ** (n - 2)
    print(f"\n  product = {product}")
    print(f"  threshold = {threshold}")
    print(f"  sub-threshold? {product < threshold}")
    print(f"  >>> This is WELL below sub-threshold (768 < 8748)")
    print(f"  BUT: does this mover word come from a VALID system?")
    print(f"  The doc says 'locally consistent' = no mover/nonmover overlap")
    print(f"  But it does NOT say the system converges!")


def check_counterexample_validity():
    """Can we build a valid system from the counterexample mover word?"""
    print("\n" + "=" * 70)
    print("PART 1b: Can the counterexample build a valid system?")
    print("=" * 70)

    ms = (3, 2, 2, 2, 2, 2, 2, 2, 2)
    n = len(ms)
    mover_word = [0, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0, 8, 7, 6, 5, 4, 3, 2, 1]
    L = len(mover_word)

    # Build a good cycle from this mover word
    # Start from all-zeros, apply movers sequentially
    # For a binary proc firing: 0->1 or 1->0 (toggle)
    # For ternary proc 0 firing: we need a transition function

    # Actually we need to determine what config sequence this mover word induces.
    # The mover word says WHO fires, but not what state transitions happen.
    # For binary procs, firing toggles (0<->1 since m=2).
    # For ternary proc 0, firing could go 0->1->2->0 (increment) or any permutation.

    # Let's try: start from all-zeros, binary procs toggle, ternary increments
    config = [0] * n
    cycle = [tuple(config)]

    for step in range(L):
        p = mover_word[step]
        config = list(cycle[-1])
        if ms[p] == 2:
            config[p] = 1 - config[p]  # toggle
        else:
            config[p] = (config[p] + 1) % ms[p]  # increment
        cycle.append(tuple(config))

    # Check if cycle closes
    if cycle[-1] == cycle[0]:
        cycle = cycle[:-1]
        print(f"Cycle closes! Length = {len(cycle)}")
        if len(set(cycle)) == len(cycle):
            print(f"All configs distinct: YES")
        else:
            print(f"WARNING: duplicate configs in cycle")
            dups = [c for c in cycle if cycle.count(c) > 1]
            print(f"  Duplicates: {len(set(dups))}")
    else:
        print(f"Cycle does NOT close: start={cycle[0]}, end={cycle[-1]}")
        # Try decrement for ternary
        config = [0] * n
        cycle = [tuple(config)]
        for step in range(L):
            p = mover_word[step]
            config = list(cycle[-1])
            if ms[p] == 2:
                config[p] = 1 - config[p]
            else:
                config[p] = (config[p] - 1) % ms[p]  # decrement
            cycle.append(tuple(config))
        if cycle[-1] == cycle[0]:
            cycle = cycle[:-1]
            print(f"With decrement: Cycle closes! Length = {len(cycle)}")
        else:
            print(f"With decrement: still doesn't close. end={cycle[-1]}")

    # Try all possible ternary transitions for each firing of proc 0
    # proc 0 fires 3 times (at steps 0, 1, 10 — wait let me recheck)
    steps_for_0 = [k for k, m in enumerate(mover_word) if m == 0]
    print(f"\nProc 0 fires at steps: {steps_for_0}")
    print(f"Proc 0 fires {len(steps_for_0)} times, m_0=3, so needs to return to start")
    print(f"3 fires with m=3: 0->a->b->0 where a,b in {{0,1,2}} and sequence is a permutation cycle")
    print(f"Possible: 0->1->2->0 or 0->2->1->0")

    for ternary_seq in [(1,2,0), (2,1,0)]:
        config = [0] * n
        cycle = [tuple(config)]
        fire_idx_0 = 0
        for step in range(L):
            p = mover_word[step]
            config = list(cycle[-1])
            if p == 0:
                config[p] = ternary_seq[fire_idx_0]
                fire_idx_0 += 1
            else:
                config[p] = 1 - config[p]
            cycle.append(tuple(config))

        if cycle[-1] == cycle[0]:
            cycle = cycle[:-1]
            distinct = len(set(cycle)) == len(cycle)
            print(f"\nTernary seq {ternary_seq}: closes, len={len(cycle)}, distinct={distinct}")

            if distinct:
                # Try to build a valid system
                det = {}
                conflict = False
                for idx in range(len(cycle)):
                    c = cycle[idx]
                    c_next = cycle[(idx + 1) % len(cycle)]
                    mover = mover_word[idx]
                    for proc in range(n):
                        left = c[(proc - 1) % n]
                        self_s = c[proc]
                        right = c[(proc + 1) % n]
                        key = (proc, left, self_s, right)
                        out = c_next[proc]
                        if key in det:
                            if det[key] != out:
                                conflict = True
                                break
                        else:
                            det[key] = out
                    if conflict:
                        break

                if conflict:
                    print(f"  Table conflict — cannot build consistent tables")
                else:
                    print(f"  No table conflict — locally consistent!")
                    print(f"  Determined entries: {len(det)}")
                    total_entries = sum(ms[(p-1)%n] * ms[p] * ms[(p+1)%n] for p in range(n))
                    print(f"  Total possible entries: {total_entries}")
                    print(f"  Free entries: {total_entries - len(det)}")

                    # Now try good-targeting completion
                    # Fill free entries to target non-good configs toward good
                    good_set = set(cycle)

                    # Build full tables
                    tables = [{} for _ in range(n)]
                    for (proc, l, s, r), out in det.items():
                        tables[proc][(l, s, r)] = out

                    # Fill free entries: try identity (non-privileged)
                    for proc in range(n):
                        ml = ms[(proc - 1) % n]
                        ms_p = ms[proc]
                        mr = ms[(proc + 1) % n]
                        for l in range(ml):
                            for s in range(ms_p):
                                for r in range(mr):
                                    if (l, s, r) not in tables[proc]:
                                        # Identity = not privileged
                                        tables[proc][(l, s, r)] = s

                    fs = []
                    for t in tables:
                        def make_f(tbl):
                            def f(l, s, r):
                                return tbl[(l, s, r)]
                            return f
                        fs.append(make_f(t))

                    result = verify_system(ms, fs, verbose=False)
                    print(f"  With identity completion: valid={result['valid']}")
                    if not result['valid']:
                        for name, (ok, msg) in result['properties'].items():
                            if not ok:
                                print(f"    FAIL: {name} — {msg}")

                    # Try good-targeting completion
                    print(f"\n  Trying good-targeting completion...")
                    tables2 = [{} for _ in range(n)]
                    for (proc, l, s, r), out in det.items():
                        tables2[proc][(l, s, r)] = out

                    # For free entries: try to make them privileged and target a good config
                    for proc in range(n):
                        ml = ms[(proc - 1) % n]
                        ms_p = ms[proc]
                        mr = ms[(proc + 1) % n]
                        for l in range(ml):
                            for s in range(ms_p):
                                for r in range(mr):
                                    if (l, s, r) not in tables2[proc]:
                                        # Try each possible output
                                        # Pick one that differs from s (makes privileged)
                                        best = s  # default: identity
                                        for v in range(ms_p):
                                            if v != s:
                                                best = v
                                                break
                                        tables2[proc][(l, s, r)] = best

                    fs2 = []
                    for t in tables2:
                        def make_f(tbl):
                            def f(l, s, r):
                                return tbl[(l, s, r)]
                            return f
                        fs2.append(make_f(t))

                    result2 = verify_system(ms, fs2, verbose=False)
                    print(f"  With privileged completion: valid={result2['valid']}")
                    if not result2['valid']:
                        for name, (ok, msg) in result2['properties'].items():
                            if not ok:
                                print(f"    FAIL: {name} — {msg}")
        else:
            print(f"\nTernary seq {ternary_seq}: doesn't close")


# ─── Enumerate all valid 3CB sub-threshold systems at n=9 ─────────────

def enumerate_3cb_systems_n9():
    """Enumerate sub-threshold multisets with 3CB at n=9."""
    print("\n" + "=" * 70)
    print("PART 2: Sub-threshold 3CB multisets at n=9")
    print("=" * 70)

    n = 9
    threshold = 4 * 3 ** (n - 2)  # 8748
    print(f"n = {n}, threshold = {threshold}")

    # Enumerate multisets with 3 consecutive binary and product < threshold
    # At least 3 procs have m=2, placed consecutively
    # Remaining 6 procs have m >= 2
    # Product = 2^3 * product(rest) < 8748
    # product(rest) < 8748/8 = 1093.5
    # rest: 6 procs, each >= 2, product < 1094

    # But actually: with 3CB the 3 consecutive are binary (m=2)
    # Others can be anything >= 2
    # Product < 8748 means 8 * product(other 6) < 8748
    # product(other 6) < 1093.5

    # All ternary (3^6 = 729) works
    # Can we have a quaternary? 4 * 3^5 = 972 works. 4^2 * 3^4 = 1296 > 1093.5, no.
    # So: either all 6 are ternary, or exactly one is quaternary and rest ternary
    # Check: 5 * 3^5 = 1215 > 1093.5, so max non-ternary is 4

    candidates = []

    # Case 1: all ternary: ms has 3 binary + 6 ternary, product = 8*729 = 5832
    candidates.append(("3b+6t", (2,2,2,3,3,3,3,3,3), 5832))

    # Case 2: one quaternary, 5 ternary: product = 8*4*243 = 7776
    candidates.append(("3b+5t+1q", (2,2,2,3,3,3,3,3,4), 7776))

    # Case 3: 4 binary + 5 ternary: product = 16*243 = 3888
    # But then we have 4 consecutive binary (or 3+1 separated)
    # 4CB is already known impossible, so skip
    # Actually 4 binary with only 3 consecutive is possible (3CB + 1 separate)
    candidates.append(("4b+5t", (2,2,2,2,3,3,3,3,3), 3888))

    # Case 4: 4 binary + 4 ternary + 1 quaternary: product = 16*81*4 = 5184
    candidates.append(("4b+4t+1q", (2,2,2,2,3,3,3,3,4), 5184))

    # Case 5: 5 binary + 4 ternary: product = 32*81 = 2592
    candidates.append(("5b+4t", (2,2,2,2,2,3,3,3,3), 2592))

    for desc, ms_base, prod in candidates:
        print(f"\n{desc}: ms_base={ms_base}, product={prod}, sub-threshold={prod < threshold}")

    return candidates


def build_all_good_cycles(ms):
    """Build all possible good cycles via mixed-sweep construction."""
    n = len(ms)
    cycles = []

    # Try all cyclic orders and targets
    for order_type in ['cw', 'ccw']:
        for start in range(n):
            if order_type == 'cw':
                order = [(start + i) % n for i in range(n)]
            else:
                order = [(start - i) % n for i in range(n)]

            # Target values for non-binary procs
            non_binary = [p for p in range(n) if ms[p] > 2]

            # For each non-binary proc, try target 1 or target ms[p]-1
            from itertools import product as cart
            target_options = []
            for p in non_binary:
                target_options.append(list(range(1, ms[p])))

            if not target_options:
                target_options = [[]]

            for targets in cart(*target_options):
                target_dict = {}
                for i, p in enumerate(non_binary):
                    target_dict[p] = targets[i]

                for return_same in [True, False]:
                    cycle = build_mixed_sweep_from_order(ms, order, target_dict, return_same)
                    if cycle is not None:
                        cycle_key = frozenset(cycle)
                        cycles.append((order, target_dict, return_same, cycle))

    return cycles


def build_mixed_sweep_from_order(ms, order, targets, return_same):
    """Build a mixed-sweep cycle."""
    n = len(ms)
    config = [0] * n
    cycle = [tuple(config)]

    for proc in order:
        config = list(cycle[-1])
        if ms[proc] == 2:
            config[proc] = 1
        else:
            config[proc] = targets.get(proc, 1)
        cycle.append(tuple(config))

    down_order = list(order) if return_same else list(reversed(order))
    for proc in down_order:
        config = list(cycle[-1])
        config[proc] = 0
        cycle.append(tuple(config))

    if cycle[-1] != cycle[0]:
        return None
    cycle = cycle[:-1]
    if len(set(cycle)) != len(cycle):
        return None
    return cycle


def extract_mover_word(cycle):
    """Extract mover word from a good cycle."""
    n = len(cycle[0])
    L = len(cycle)
    movers = []
    for i in range(L):
        c1 = cycle[i]
        c2 = cycle[(i + 1) % L]
        diffs = [p for p in range(n) if c1[p] != c2[p]]
        if len(diffs) != 1:
            return None
        movers.append(diffs[0])
    return movers


def analyze_phases_at_proc(mover_word, proc, left_proc, right_proc):
    """Extract phases at a binary proc."""
    L = len(mover_word)
    fire_steps = [k for k in range(L) if mover_word[k] == proc]

    if len(fire_steps) < 2:
        return []

    phases = []
    for idx in range(len(fire_steps)):
        s1 = fire_steps[idx]
        s2 = fire_steps[(idx + 1) % len(fire_steps)]

        # Collect steps in the gap
        gap_steps = []
        k = (s1 + 1) % L
        while k != s2:
            gap_steps.append(k)
            k = (k + 1) % L

        J = sum(1 for k in gap_steps if mover_word[k] == left_proc)
        K = sum(1 for k in gap_steps if mover_word[k] == right_proc)

        # Check isolation: the step before s2 should not be proc (not consecutive)
        prev_s2 = (s2 - 1) % L
        isolated_at_s2 = (mover_word[prev_s2] != proc)

        # Check parity
        # Count fires of left_proc and right_proc in [s1+1, s2]
        left_fires_prefix_s1 = sum(1 for k in range(s1 + 1) if mover_word[k] == left_proc)
        left_fires_prefix_s2 = sum(1 for k in range(s2 + 1) if mover_word[k] == left_proc) if s2 > s1 else sum(1 for k in range(s2 + 1) if mover_word[k] == left_proc) + sum(1 for k in range(s1 + 1, L) if mover_word[k] == left_proc)
        right_fires_prefix_s1 = sum(1 for k in range(s1 + 1) if mover_word[k] == right_proc)
        right_fires_prefix_s2 = sum(1 for k in range(s2 + 1) if mover_word[k] == right_proc) if s2 > s1 else sum(1 for k in range(s2 + 1) if mover_word[k] == right_proc) + sum(1 for k in range(s1 + 1, L) if mover_word[k] == right_proc)

        left_parity_same = (left_fires_prefix_s1 % 2) == (left_fires_prefix_s2 % 2)
        right_parity_same = (right_fires_prefix_s1 % 2) == (right_fires_prefix_s2 % 2)

        phases.append({
            'idx': idx,
            's1': s1, 's2': s2,
            'gap_len': len(gap_steps),
            'J': J, 'K': K,
            'J+K': J + K,
            'isolated': isolated_at_s2,
            'left_parity_same': left_parity_same,
            'right_parity_same': right_parity_same,
            'parity_ok': left_parity_same and right_parity_same,
            'odd_parity': not (left_parity_same and right_parity_same),
        })

    return phases


def check_entry_conflict(cycle, mover_word):
    """Check if a cycle has entry conflict at any proc."""
    n = len(cycle[0])
    L = len(cycle)

    # For each proc, collect mover triples and non-mover triples
    for proc in range(n):
        mover_triples = set()
        nonmover_triples = set()

        for k in range(L):
            c = cycle[k]
            left = c[(proc - 1) % n]
            self_s = c[proc]
            right = c[(proc + 1) % n]
            triple = (left, self_s, right)

            if mover_word[k] == proc:
                mover_triples.add(triple)
            else:
                nonmover_triples.add(triple)

        overlap = mover_triples & nonmover_triples
        if overlap:
            return True, proc, overlap

    return False, None, None


# ─── Main investigation: enumerate valid systems ────────────────────

def investigate_3cb_n9_small():
    """
    For the smallest 3CB sub-threshold case at n=9:
    ms = (2,2,2,3,3,3,3,3,3), product=5832.

    Build all valid systems via mixed-sweep + good-targeting completion.
    Check: does the residual phase configuration ever occur?
    """
    print("\n" + "=" * 70)
    print("PART 3: Exhaustive check — 3CB sub-threshold systems at n=9")
    print("=" * 70)

    ms_base = [2, 2, 2, 3, 3, 3, 3, 3, 3]
    n = 9
    product = 1
    for m in ms_base:
        product *= m
    threshold = 4 * 3 ** (n - 2)
    print(f"ms = {ms_base}, product = {product}, threshold = {threshold}")
    print(f"sub-threshold: {product < threshold}")

    # The 3CB block is at positions 0,1,2 (all binary)
    # Middle binary = proc 1
    # Left neighbor of proc 1 = proc 0 (binary)
    # Right neighbor of proc 1 = proc 2 (binary)

    # Actually, we need to try all orientations of the 3CB block on the ring.
    # But by symmetry of all-ternary rest, placing 3CB at {0,1,2} is WLOG.

    # Build all sweep-type good cycles
    print(f"\nBuilding sweep-type cycles...")

    valid_count = 0
    total_cycles = 0
    residual_cases = []

    # Generate all cyclic orders
    orders = list(cyclic_orders_gen(n))
    print(f"Number of cyclic orders: {len(orders)}")

    # For each order, build sweep cycle and try completion
    from itertools import product as cart

    ms = tuple(ms_base)
    non_binary = [p for p in range(n) if ms[p] > 2]

    # Target options for ternary procs: 1 or 2
    target_combos = list(cart(*([list(range(1, ms[p])) for p in non_binary])))
    print(f"Non-binary procs: {non_binary}")
    print(f"Target combos: {len(target_combos)}")

    results = []

    for order in orders:
        for targets in target_combos:
            target_dict = {non_binary[i]: targets[i] for i in range(len(non_binary))}
            for return_same in [True, False]:
                cycle = build_mixed_sweep_from_order(ms, order, target_dict, return_same)
                if cycle is None:
                    continue
                total_cycles += 1

                mover_word = extract_mover_word(cycle)
                if mover_word is None:
                    continue

                # Check entry conflict
                has_ec, ec_proc, ec_overlap = check_entry_conflict(cycle, mover_word)

                # Analyze phases at the middle binary of each 3CB block
                # 3CB blocks: any 3 consecutive procs that are all binary
                three_cb_blocks = []
                for i in range(n):
                    if ms[i] == 2 and ms[(i+1)%n] == 2 and ms[(i+2)%n] == 2:
                        three_cb_blocks.append((i, (i+1)%n, (i+2)%n))

                for (i, mid, r) in three_cb_blocks:
                    left_of_mid = i
                    right_of_mid = r
                    phases = analyze_phases_at_proc(mover_word, mid, left_of_mid, right_of_mid)

                    fc_mid = sum(1 for m in mover_word if m == mid)
                    if fc_mid < 2:
                        continue

                    # Check isolation
                    all_isolated = all(p['isolated'] for p in phases)

                    for phase in phases:
                        if (phase['isolated'] and phase['odd_parity'] and
                            phase['J+K'] == 1):
                            # This is the residual case!
                            residual_cases.append({
                                'order': order,
                                'targets': target_dict,
                                'return_same': return_same,
                                'mover_word': mover_word,
                                'has_ec': has_ec,
                                'phase': phase,
                                'mid': mid,
                                'three_cb': (i, mid, r),
                            })

                results.append({
                    'cycle_len': len(cycle),
                    'has_ec': has_ec,
                    'mover_word': mover_word,
                })

    print(f"\nTotal sweep cycles: {total_cycles}")
    print(f"With entry conflict: {sum(1 for r in results if r['has_ec'])}")
    print(f"Without entry conflict: {sum(1 for r in results if not r['has_ec'])}")
    print(f"\nResidual cases (isolated + odd parity + J+K=1): {len(residual_cases)}")

    if residual_cases:
        print("\nResidual case details:")
        for i, rc in enumerate(residual_cases[:20]):
            print(f"  Case {i}: mid={rc['mid']}, 3CB={rc['three_cb']}, "
                  f"phase J={rc['phase']['J']}, K={rc['phase']['K']}, "
                  f"has_ec={rc['has_ec']}")

        # Key question: do ALL residual cases have EC?
        residual_with_ec = sum(1 for rc in residual_cases if rc['has_ec'])
        residual_without_ec = sum(1 for rc in residual_cases if not rc['has_ec'])
        print(f"\n  Residual cases WITH EC: {residual_with_ec}")
        print(f"  Residual cases WITHOUT EC: {residual_without_ec}")

        if residual_without_ec > 0:
            print("\n  *** RESIDUAL WITHOUT EC EXISTS — investigating convergence ***")
            for rc in residual_cases:
                if not rc['has_ec']:
                    print(f"  Mover word: {rc['mover_word']}")
                    print(f"  Phase: {rc['phase']}")
                    break
    else:
        print("\n>>> NO RESIDUAL CASES FOUND!")
        print(">>> The dispatch always fires under these hypotheses.")
        print(">>> Checking: is this because all phases have J+K >= 2, or parity is always even?")

        # Detailed check
        for order in orders[:5]:
            for targets in target_combos[:3]:
                target_dict = {non_binary[i]: targets[i] for i in range(len(non_binary))}
                for return_same in [True, False]:
                    cycle = build_mixed_sweep_from_order(ms, order, target_dict, return_same)
                    if cycle is None:
                        continue
                    mover_word = extract_mover_word(cycle)
                    if mover_word is None:
                        continue

                    for (i, mid, r) in [(0, 1, 2)]:
                        phases = analyze_phases_at_proc(mover_word, mid, i, r)
                        if phases:
                            for p in phases:
                                print(f"  Example phase: J={p['J']}, K={p['K']}, "
                                      f"odd_parity={p['odd_parity']}, isolated={p['isolated']}")
                            break
                    break
                break
            break

    return results, residual_cases


def cyclic_orders_gen(n):
    """Generate distinct cyclic orders (CW and CCW with all rotations)."""
    seen = set()
    for base in (list(range(n)), list(range(n - 1, -1, -1))):
        for shift in range(n):
            order = tuple(base[shift:] + base[:shift])
            if order not in seen:
                seen.add(order)
                yield order


# ─── Exhaustive non-sweep cycle search ────────────────────────────────

def exhaustive_good_cycles_n5():
    """At n=5 with 3CB, enumerate ALL good cycles and check residual."""
    print("\n" + "=" * 70)
    print("PART 4: Exhaustive good cycle search at n=5 (ms=(2,2,2,3,4))")
    print("=" * 70)

    ms = (2, 2, 2, 3, 4)
    n = 5
    product = 1
    for m in ms:
        product *= m
    threshold = 4 * 3 ** (n - 2)
    print(f"ms = {ms}, product = {product}, threshold = {threshold}")
    print(f"sub-threshold: {product < threshold}")
    print(f"Note: product = threshold = 96, so NOT sub-threshold")
    print(f"This is AT the threshold, not below it")

    # Try ms=(2,2,2,3,3) at n=5: product = 72 < 96 = threshold
    ms2 = (2, 2, 2, 3, 3)
    product2 = 1
    for m in ms2:
        product2 *= m
    print(f"\nTrying ms = {ms2}, product = {product2}, threshold = {threshold}")
    print(f"sub-threshold: {product2 < threshold}")

    # Enumerate all valid systems for this ms
    # This is too many to enumerate exhaustively for n=5
    # Instead, use the verifier to check specific constructions

    # Actually n=5 with 3CB and sub-threshold: product < 96
    # ms = (2,2,2,3,3) has product 72 < 96
    # Can we build a valid system?

    ms = ms2
    n = len(ms)

    # Build sweep cycles
    orders = list(cyclic_orders_gen(n))
    non_binary = [p for p in range(n) if ms[p] > 2]

    from itertools import product as cart
    target_combos = list(cart(*([list(range(1, ms[p])) for p in non_binary])))

    total = 0
    valid_systems = 0
    ec_count = 0

    for order in orders:
        for targets in target_combos:
            target_dict = {non_binary[i]: targets[i] for i in range(len(non_binary))}
            for return_same in [True, False]:
                cycle = build_mixed_sweep_from_order(ms, order, target_dict, return_same)
                if cycle is None:
                    continue
                total += 1

                mover_word = extract_mover_word(cycle)
                if mover_word is None:
                    continue

                has_ec, _, _ = check_entry_conflict(cycle, mover_word)
                if has_ec:
                    ec_count += 1
                    continue

                # No EC — try to complete to valid system
                # Build tables from cycle
                det = {}
                conflict = False
                for idx in range(len(cycle)):
                    c = cycle[idx]
                    c_next = cycle[(idx + 1) % len(cycle)]
                    mover = mover_word[idx]
                    for proc in range(n):
                        left = c[(proc - 1) % n]
                        self_s = c[proc]
                        right = c[(proc + 1) % n]
                        key = (proc, left, self_s, right)
                        out = c_next[proc]
                        if key in det:
                            if det[key] != out:
                                conflict = True
                                break
                        else:
                            det[key] = out
                    if conflict:
                        break

                if conflict:
                    continue

                # Good-targeting completion
                tables = [{} for _ in range(n)]
                for (proc, l, s, r), out in det.items():
                    tables[proc][(l, s, r)] = out

                # Fill free: target good by making privileged (change state)
                for proc in range(n):
                    ml = ms[(proc - 1) % n]
                    ms_p = ms[proc]
                    mr = ms[(proc + 1) % n]
                    for l in range(ml):
                        for s in range(ms_p):
                            for r in range(mr):
                                if (l, s, r) not in tables[proc]:
                                    # Try to target a good config
                                    tables[proc][(l, s, r)] = (s + 1) % ms_p

                fs = [lambda l, s, r, t=tables[p]: t[(l, s, r)] for p in range(n)]
                result = verify_system(ms, fs)
                if result['valid']:
                    valid_systems += 1

    print(f"\nTotal sweep cycles: {total}")
    print(f"With EC: {ec_count}")
    print(f"Valid systems: {valid_systems}")


# ─── Main: does the residual actually occur? ──────────────────────────

def investigate_all_mover_words_n9():
    """
    More general: enumerate mover words at n=9 for 3CB sub-threshold,
    not just sweep constructions.
    """
    print("\n" + "=" * 70)
    print("PART 5: General mover word analysis at n=9, 3CB")
    print("=" * 70)

    ms = (2, 2, 2, 3, 3, 3, 3, 3, 3)
    n = 9
    product = 5832
    threshold = 4 * 3**7

    print(f"ms = {ms}, product = {product}, threshold = {threshold}")
    print(f"3CB at procs 0,1,2")
    print(f"Middle binary = proc 1, left=0, right=2")

    # For a good cycle with this ms:
    # - Each proc p fires exactly m_p times (for binary: 2, for ternary: 3)
    # - Actually: fc(p) >= m_p, and fc(p) % m_p = 0 for the cycle to close
    # - Minimum cycle length = lcm scenario, but for sweep: 2n = 18

    # Actually for a fair good cycle:
    # - Each proc fires at least once
    # - For binary (m=2): must fire even number of times (to return to start)
    # - For ternary (m=3): must fire multiple of 3 times
    # - Minimum: each binary fires 2 times, each ternary fires 3 times
    # - Cycle length = 3*2 + 6*3 = 6 + 18 = 24? No...
    # - Wait: cycle length = sum of fire counts = sum(fc(p) for all p)
    # - Minimum: 3*2 + 6*3 = 24

    # For a sweep cycle (CW or CCW): each proc fires exactly once per direction
    # Sweep length = 2n = 18 -- but then binary procs fire 2 and ternary fire 2
    # ternary fires 2 but m=3, so 2 mod 3 != 0 -- cycle doesn't close!
    # So simple sweeps DON'T work for ternary procs

    # For sweep to work: need fc(p) divisible by m_p
    # Binary: fc=2 (OK with 1 CW + 1 CCW)
    # Ternary: need fc divisible by 3
    # In a standard bounce sweep (CW then CCW): fc=2 for all procs
    # But 2 mod 3 != 0 for ternary!
    # So we need modified sweeps. E.g., 3 passes: fc=3 for all.
    # Or non-uniform sweeps.

    # Let me look at what the CLB construction does
    print(f"\nMinimum cycle length analysis:")
    print(f"  Binary procs: 3, minimum fc = 2 each = 6 total fires")
    print(f"  Ternary procs: 6, minimum fc = 3 each = 18 total fires")
    print(f"  Minimum cycle length = 24")

    print(f"\nCLB construction uses endpoint-binary, which avoids 3CB")
    print(f"For 3CB, the known M_5 witness has cycle length 18 (not minimal)")

    # Let me analyze the structure differently.
    # The counterexample uses ms=(3,2,2,2,2,2,2,2,2) with 8 binary procs.
    # With 8 binary: fc = 2 each = 16 fires. Ternary fc = 3. Total = 19 = L.

    # For ms=(2,2,2,3,3,3,3,3,3): 3 binary fc=2=6, 6 ternary fc=3=18, L=24

    # Build a sweep-like cycle:
    # CW sweep: 0,1,2,3,4,5,6,7,8 (length 9, fc=1 each)
    # CCW sweep: 8,7,6,5,4,3,2,1,0 (length 9, fc=1 each)
    # After 2 sweeps: binary fc=2 (good), ternary fc=2 (need 1 more)
    # Add a third sweep for ternary only:
    # 3,4,5,6,7,8 (length 6, ternary fc=3 now)
    # Total length = 9 + 9 + 6 = 24

    # Let me build this explicitly
    sweep1 = list(range(n))  # CW: 0,1,2,...,8
    sweep2 = list(range(n-1, -1, -1))  # CCW: 8,7,...,0
    sweep3 = [p for p in range(3, n)]  # Ternary CW: 3,4,5,6,7,8

    mover_word = sweep1 + sweep2 + sweep3
    L = len(mover_word)

    fc = Counter(mover_word)
    print(f"\nThree-sweep mover word (length {L}):")
    print(f"  Word: {mover_word}")
    for p in range(n):
        print(f"  proc {p} (m={ms[p]}): fc={fc[p]}, fc%m={fc[p]%ms[p]}")

    # Check phases at proc 1 (middle of 3CB {0,1,2})
    phases = analyze_phases_at_proc(mover_word, 1, 0, 2)
    print(f"\nPhases at proc 1 (middle binary):")
    for p in phases:
        dispatch = ""
        if p['J+K'] >= 2:
            dispatch = "DISPATCHED (J+K >= 2)"
        elif not p['odd_parity']:
            dispatch = "DISPATCHED (even parity)"
        elif not p['isolated']:
            dispatch = "DISPATCHED (not isolated)"
        else:
            dispatch = "*** RESIDUAL ***"
        print(f"  Phase {p['idx']}: J={p['J']}, K={p['K']}, J+K={p['J+K']}, "
              f"odd_parity={p['odd_parity']}, isolated={p['isolated']} -> {dispatch}")

    # Now try to build a config sequence and check EC
    # For this mover word, build the cycle starting from all-zeros
    config = [0] * n
    cycle = [tuple(config)]
    for step in range(L):
        p = mover_word[step]
        config = list(cycle[-1])
        if ms[p] == 2:
            config[p] = 1 - config[p]
        else:
            config[p] = (config[p] + 1) % ms[p]
        cycle.append(tuple(config))

    if cycle[-1] == cycle[0]:
        cycle = cycle[:-1]
        print(f"\nCycle closes. Length = {len(cycle)}, distinct = {len(set(cycle)) == len(cycle)}")

        has_ec, ec_proc, ec_overlap = check_entry_conflict(cycle, mover_word)
        print(f"Entry conflict: {has_ec}" + (f" at proc {ec_proc}" if has_ec else ""))
    else:
        print(f"\nCycle doesn't close: start={cycle[0]}, end={cycle[-1]}")


def investigate_general_mover_words():
    """
    Generate random valid mover words for 3CB sub-threshold at n=9
    and check if residual occurs.
    """
    print("\n" + "=" * 70)
    print("PART 6: Random mover word survey")
    print("=" * 70)

    import random
    random.seed(42)

    ms = (2, 2, 2, 3, 3, 3, 3, 3, 3)
    n = 9

    # Generate random valid mover words
    # Constraints: fc(p) % m_p = 0 for all p, fc(p) >= m_p

    num_trials = 10000
    residual_total = 0
    residual_with_ec = 0
    residual_without_ec = 0
    no_residual_count = 0
    cycle_close_count = 0

    for trial in range(num_trials):
        # Build a random mover word
        # Start with minimum fires
        fires = []
        for p in range(n):
            fires.extend([p] * ms[p])

        # Optionally add more fires (with probability)
        if random.random() < 0.3:
            extra = random.randint(1, 6)
            for _ in range(extra):
                p = random.randint(0, n-1)
                fires.extend([p] * ms[p])  # add full m_p fires to keep divisibility

        random.shuffle(fires)
        mover_word = fires
        L = len(mover_word)

        # Check fire count divisibility
        fc = Counter(mover_word)
        ok = all(fc.get(p, 0) % ms[p] == 0 and fc.get(p, 0) >= ms[p] for p in range(n))
        if not ok:
            continue

        # Build cycle
        config = [0] * n
        cycle = [tuple(config)]
        for step in range(L):
            p = mover_word[step]
            config = list(cycle[-1])
            if ms[p] == 2:
                config[p] = 1 - config[p]
            else:
                config[p] = (config[p] + 1) % ms[p]
            cycle.append(tuple(config))

        if cycle[-1] != cycle[0]:
            continue
        cycle = cycle[:-1]
        if len(set(cycle)) != len(cycle):
            continue

        cycle_close_count += 1

        # Check EC
        has_ec, _, _ = check_entry_conflict(cycle, mover_word)

        # Check phases at middle binary procs
        has_residual = False
        for (i, mid, r) in [(0, 1, 2)]:  # 3CB at 0,1,2
            phases = analyze_phases_at_proc(mover_word, mid, i, r)
            for phase in phases:
                if (phase['isolated'] and phase['odd_parity'] and phase['J+K'] == 1):
                    has_residual = True
                    break

        if has_residual:
            residual_total += 1
            if has_ec:
                residual_with_ec += 1
            else:
                residual_without_ec += 1
                if residual_without_ec <= 3:
                    print(f"\n  Residual WITHOUT EC at trial {trial}:")
                    print(f"    Mover word: {mover_word[:30]}... (len {L})")
                    # Check if this can be completed to a valid system
                    det = {}
                    conflict = False
                    for idx in range(len(cycle)):
                        c = cycle[idx]
                        c_next = cycle[(idx + 1) % len(cycle)]
                        mover = mover_word[idx]
                        for proc in range(n):
                            left = c[(proc - 1) % n]
                            self_s = c[proc]
                            right = c[(proc + 1) % n]
                            key = (proc, left, self_s, right)
                            out = c_next[proc]
                            if key in det:
                                if det[key] != out:
                                    conflict = True
                                    break
                            else:
                                det[key] = out
                        if conflict:
                            break
                    print(f"    Table conflict: {conflict}")
        else:
            no_residual_count += 1

    print(f"\nSummary of {num_trials} trials:")
    print(f"  Valid closed cycles: {cycle_close_count}")
    print(f"  No residual (dispatch always fires): {no_residual_count}")
    print(f"  Has residual phase: {residual_total}")
    print(f"    With EC: {residual_with_ec}")
    print(f"    Without EC: {residual_without_ec}")

    if residual_total > 0:
        print(f"\n  EC rate among residual: {residual_with_ec}/{residual_total} = {residual_with_ec/residual_total:.1%}")

    if residual_without_ec > 0:
        print(f"\n  >>> RESIDUAL WITHOUT EC EXISTS — need domino argument")
    else:
        print(f"\n  >>> ALL residual cases have EC — dispatch might not be needed")


def investigate_sweep_specific():
    """
    Focus on SWEEP mover words specifically (since the sorry is in Sweep.lean).
    A sweep visits each proc once per direction.
    """
    print("\n" + "=" * 70)
    print("PART 7: Sweep-specific analysis")
    print("=" * 70)

    ms = (2, 2, 2, 3, 3, 3, 3, 3, 3)
    n = 9

    print(f"ms = {ms}")
    print(f"For a sweep: each proc is mover exactly twice (once each direction)")
    print(f"But fc=2 for ternary means 2 mod 3 ≠ 0 → cycle doesn't close!")
    print(f"So pure sweep is IMPOSSIBLE for this ms.")
    print(f"\nA sweep in the Lean code means gc.isSweep — checking definition...")

    # isSweep in Lean: mover word visits procs in a single consistent direction
    # (either all CW or all CCW), possibly with repeats
    # Actually, let's check what isSweep means more carefully

    # From the Lean codebase, isSweep likely means:
    # The mover word can be decomposed into sweeps (full traversals of the ring)
    # or the movers follow a consistent directional pattern

    # For 3CB with ternary procs:
    # Sweep cycle must have fc(p) = m_p for all p (minimum)
    # Total length = 3*2 + 6*3 = 24
    # The sweep structure: movers go around the ring, each proc fires in order

    # Actually, in the Lean sorry context, the hypotheses include:
    # hsweep : gc.isSweep — which constrains the mover pattern
    # Let me think about what sweep cycles look like with this ms

    # A natural sweep: CW pass fires each proc once, then CCW,
    # but ternary need 3 fires total. So need 3 passes through ternary.
    # One structure: CW all, CCW all, CW ternary-only

    # Let's enumerate various sweep patterns and check
    sweep_patterns = []

    # Pattern 1: CW, CCW, CW(ternary)
    sp1 = list(range(n)) + list(range(n-1,-1,-1)) + list(range(3,n))
    sweep_patterns.append(("CW+CCW+CW_ternary", sp1))

    # Pattern 2: CW, CCW, CCW(ternary)
    sp2 = list(range(n)) + list(range(n-1,-1,-1)) + list(range(n-1,2,-1))
    sweep_patterns.append(("CW+CCW+CCW_ternary", sp2))

    # Pattern 3: CW, CW, CW (3 full CW sweeps) — binary fires 3 (odd, bad)
    # fc(binary) = 3, 3 mod 2 = 1 ≠ 0, skip

    # Pattern 4: CW, CW, CCW, CCW, CW(ternary), CCW(ternary) — 4 passes + 2 ternary
    # binary fc=4, ternary fc=6, too long

    # Pattern 5: interleaved
    sp5 = []
    for p in range(n):
        sp5.append(p)
    for p in range(n-1, -1, -1):
        sp5.append(p)
    # Now binary have fc=2, ternary have fc=2. Need 1 more for ternary.
    # Insert ternary fires
    sp5_ext = list(sp5)
    for p in range(3, n):
        sp5_ext.append(p)
    sweep_patterns.append(("CW+CCW+extra_ternary", sp5_ext))

    for name, mw in sweep_patterns:
        fc = Counter(mw)
        valid_fc = all(fc.get(p, 0) % ms[p] == 0 and fc.get(p, 0) >= ms[p] for p in range(n))

        print(f"\n{name}: length={len(mw)}, valid_fc={valid_fc}")
        if not valid_fc:
            for p in range(n):
                if fc.get(p, 0) % ms[p] != 0:
                    print(f"  proc {p}: fc={fc.get(p,0)}, m={ms[p]}, fc%m={fc.get(p,0)%ms[p]}")
            continue

        # Build cycle
        config = [0] * n
        cycle = [tuple(config)]
        for step in range(len(mw)):
            p = mw[step]
            config = list(cycle[-1])
            if ms[p] == 2:
                config[p] = 1 - config[p]
            else:
                config[p] = (config[p] + 1) % ms[p]
            cycle.append(tuple(config))

        closes = cycle[-1] == cycle[0]
        if closes:
            cycle = cycle[:-1]
            distinct = len(set(cycle)) == len(cycle)
        else:
            distinct = False

        print(f"  closes={closes}, distinct={distinct}")

        if closes and distinct:
            has_ec, ec_proc, _ = check_entry_conflict(cycle, mw)
            print(f"  EC: {has_ec}" + (f" at proc {ec_proc}" if has_ec else ""))

            # Phases at middle binary
            phases = analyze_phases_at_proc(mw, 1, 0, 2)
            print(f"  Phases at proc 1:")
            for p in phases:
                dispatch = "DISPATCHED" if (p['J+K'] >= 2 or not p['odd_parity'] or not p['isolated']) else "RESIDUAL"
                print(f"    J={p['J']}, K={p['K']}, odd={p['odd_parity']}, iso={p['isolated']} -> {dispatch}")


def investigate_domino():
    """
    Test the domino hypothesis: boundary triples propagate across consecutive phases.
    """
    print("\n" + "=" * 70)
    print("PART 8: Domino / cross-phase propagation test")
    print("=" * 70)

    # Use the counterexample mover word to understand cross-phase structure
    ms = (3, 2, 2, 2, 2, 2, 2, 2, 2)
    n = 9
    mover_word = [0, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0, 8, 7, 6, 5, 4, 3, 2, 1]
    L = len(mover_word)

    # Pivot = proc 0 (ternary, sandwiched by binary procs 8 and 1)
    # Wait, the doc says pivot t=0 with both neighbors binary
    # In this ms: proc 0 has m=3 (ternary), procs 1-8 all binary (m=2)
    # But the sorry is about 3CB (3 consecutive binary)
    # 3CB blocks here: any 3 consecutive among procs 1-8 (all binary)
    # e.g., procs 1,2,3 or 6,7,8

    # Actually the doc's counterexample is about NormalFormEC at a ternary pivot
    # The sorry is about 3CB = 3 consecutive binary
    # Let me focus on the 3CB block and the phases at the MIDDLE binary proc

    # With ms=(3,2,2,2,2,2,2,2,2), take 3CB at procs 1,2,3 (all binary)
    # Middle = proc 2, left=1, right=3

    mid = 2
    left_p = 1
    right_p = 3

    phases = analyze_phases_at_proc(mover_word, mid, left_p, right_p)
    print(f"\nms = {ms}")
    print(f"Mover word = {mover_word}")
    print(f"\n3CB block: procs {left_p},{mid},{right_p}")
    print(f"Phases at proc {mid}:")
    for p in phases:
        dispatch = ""
        if p['J+K'] >= 2:
            dispatch = "DISPATCHED (J+K >= 2)"
        elif not p['odd_parity']:
            dispatch = "DISPATCHED (even parity)"
        elif not p['isolated']:
            dispatch = "DISPATCHED (not isolated)"
        else:
            dispatch = "*** RESIDUAL ***"
        print(f"  Phase {p['idx']}: s1={p['s1']}, s2={p['s2']}, J={p['J']}, K={p['K']}, "
              f"odd_parity={p['odd_parity']}, isolated={p['isolated']} -> {dispatch}")

    # Build the cycle and show the config sequence
    print(f"\nConfig sequence (ternary increments):")
    config = [0] * n
    cycle = [tuple(config)]
    for step in range(L):
        p = mover_word[step]
        config = list(cycle[-1])
        if ms[p] == 2:
            config[p] = 1 - config[p]
        else:
            config[p] = (config[p] + 1) % ms[p]
        cycle.append(tuple(config))

    closes = cycle[-1] == cycle[0]
    print(f"Closes: {closes}")

    if closes:
        cycle = cycle[:-1]
        # Show configs with mover highlighted
        for step in range(L):
            c = cycle[step]
            mover = mover_word[step]
            print(f"  step {step:2d}: {c} -> mover={mover}")

        # Show triples at proc 2
        print(f"\nTriples at proc {mid}:")
        for step in range(L):
            c = cycle[step]
            triple = (c[left_p], c[mid], c[right_p])
            role = "MOVER" if mover_word[step] == mid else "non-mover"
            print(f"  step {step:2d}: triple={triple}, role={role}")


def investigate_convergence_constraint():
    """
    Key test: does convergence constrain the residual?
    At sub-threshold + convergence, does the residual ever occur?

    Strategy: for n=5 where we CAN build valid 3CB systems, check if
    residual phases ever appear in the VALID system's good cycle.
    """
    print("\n" + "=" * 70)
    print("PART 9: Convergence constraint — n=5 valid 3CB systems")
    print("=" * 70)

    # n=5, ms=(2,2,2,3,4), product=96 = threshold
    # This is AT threshold, not sub.
    # ms=(2,2,2,3,3), product=72 < 96 = sub-threshold

    # First check: can ms=(2,2,2,3,3) yield a valid system?
    ms = (2, 2, 2, 3, 3)
    n = 5
    product = 72
    threshold = 96

    print(f"ms = {ms}, product = {product}, threshold = {threshold}")
    print(f"sub-threshold: YES")

    # Exhaustive sweep construction
    orders = list(cyclic_orders_gen(n))
    non_binary = [p for p in range(n) if ms[p] > 2]

    from itertools import product as cart
    target_combos = list(cart(*([list(range(1, ms[p])) for p in non_binary])))

    valid_systems = []
    total_cycles = 0

    for order in orders:
        for targets in target_combos:
            target_dict = {non_binary[i]: targets[i] for i in range(len(non_binary))}
            for return_same in [True, False]:
                cycle = build_mixed_sweep_from_order(ms, order, target_dict, return_same)
                if cycle is None:
                    continue

                mover_word = extract_mover_word(cycle)
                if mover_word is None:
                    continue

                total_cycles += 1

                # Check table consistency
                det = {}
                conflict = False
                for idx in range(len(cycle)):
                    c = cycle[idx]
                    c_next = cycle[(idx + 1) % len(cycle)]
                    mover = mover_word[idx]
                    for proc in range(n):
                        left = c[(proc - 1) % n]
                        self_s = c[proc]
                        right = c[(proc + 1) % n]
                        key = (proc, left, self_s, right)
                        out = c_next[proc]
                        if key in det:
                            if det[key] != out:
                                conflict = True
                                break
                        else:
                            det[key] = out
                    if conflict:
                        break

                if conflict:
                    continue

                # Try good-targeting completion
                tables = [{} for _ in range(n)]
                for (proc, l, s, r), out in det.items():
                    tables[proc][(l, s, r)] = out

                for proc in range(n):
                    ml = ms[(proc - 1) % n]
                    ms_p = ms[proc]
                    mr = ms[(proc + 1) % n]
                    for l in range(ml):
                        for s in range(ms_p):
                            for r in range(mr):
                                if (l, s, r) not in tables[proc]:
                                    tables[proc][(l, s, r)] = (s + 1) % ms_p

                fs = []
                for p_idx in range(n):
                    tbl = tables[p_idx]
                    def make_f(t):
                        def f(l, s, r):
                            return t[(l, s, r)]
                        return f
                    fs.append(make_f(tbl))

                result = verify_system(ms, fs)
                if result['valid']:
                    valid_systems.append({
                        'cycle': cycle,
                        'mover_word': mover_word,
                        'tables': tables,
                    })

    print(f"\nTotal cycles: {total_cycles}")
    print(f"Valid systems: {len(valid_systems)}")

    if valid_systems:
        for i, vs in enumerate(valid_systems):
            mw = vs['mover_word']
            cycle = vs['cycle']

            has_ec, _, _ = check_entry_conflict(cycle, mw)

            # Phases at middle binary (proc 1) of 3CB {0,1,2}
            phases = analyze_phases_at_proc(mw, 1, 0, 2)
            residual_phases = [p for p in phases
                              if p['isolated'] and p['odd_parity'] and p['J+K'] == 1]

            print(f"\n  System {i}: mover_word len={len(mw)}, EC={has_ec}")
            print(f"    Phases at proc 1: {len(phases)}")
            for p in phases:
                dispatch = ""
                if p['J+K'] >= 2:
                    dispatch = "DISPATCHED"
                elif not p['odd_parity']:
                    dispatch = "DISPATCHED(parity)"
                elif not p['isolated']:
                    dispatch = "DISPATCHED(non-isolated)"
                else:
                    dispatch = "RESIDUAL"
                print(f"      J={p['J']}, K={p['K']}, odd={p['odd_parity']}, iso={p['isolated']} -> {dispatch}")

            if residual_phases:
                print(f"    *** HAS RESIDUAL PHASES: {len(residual_phases)} ***")
            else:
                print(f"    No residual phases")
    else:
        print(f"\nNo valid systems found with sweep construction")
        print(f"This confirms: 3CB at sub-threshold product cannot build valid systems")
        print(f"(at least not via sweep construction)")


if __name__ == "__main__":
    analyze_counterexample()
    check_counterexample_validity()
    investigate_3cb_n9_small()
    investigate_all_mover_words_n9()
    investigate_sweep_specific()
    investigate_general_mover_words()
    investigate_domino()
    investigate_convergence_constraint()
