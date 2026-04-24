"""
RA12 v2: Deep dive into WHY drainage basin = P even for sub-threshold systems.

Key finding from v1: Sol1-style on ms=(2,2,2,3,3) P=72 has full_basin = 72 = P.
This is DESPITE being sub-threshold (threshold = 108).

But wait — having full basin ≠ being a valid system. The system fails convergence
because of nondeterminism: multi-privilege configs can CHOOSE to cycle.
A daemon can keep them cycling by always picking the "wrong" successor.

So the question becomes: what fraction of the config space has multi-privilege?
And among multi-priv configs, how many are FORCED to cycle (all successors are bad)?

Also: the binary flip never creates a "shadow trap" because it ALWAYS breaks
single-privilege at some step. This is because the transition function at a binary
proc depends on the flipped value — the privilege condition changes.

NEW INVESTIGATION: fiber structure.
- Group configs by their values at non-mover positions ("fiber")
- Each fiber should flow together through the good cycle
- If a fiber is "broken" (doesn't flow together), that constrains the basin
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import itertools
from collections import defaultdict, deque, Counter
from verifier import verify_system, all_configs, privileged_set, apply_move


def build_m5_96_witness():
    ms = [2, 2, 2, 3, 4]
    tables = [
        {(0,0,0):1,(0,0,1):0,(0,1,0):1,(0,1,1):1,
         (1,0,0):0,(1,0,1):0,(1,1,0):0,(1,1,1):0,
         (2,0,0):0,(2,0,1):0,(2,1,0):0,(2,1,1):0,
         (3,0,0):0,(3,0,1):0,(3,1,0):0,(3,1,1):0},
        {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,
         (1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):1},
        {(0,0,0):0,(0,0,1):0,(0,0,2):1,(0,1,0):1,(0,1,1):0,(0,1,2):1,
         (1,0,0):1,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):1,(1,1,2):0},
        {(0,0,0):0,(0,0,1):0,(0,0,2):1,(0,0,3):0,
         (0,1,0):1,(0,1,1):2,(0,1,2):1,(0,1,3):0,
         (0,2,0):0,(0,2,1):2,(0,2,2):2,(0,2,3):2,
         (1,0,0):1,(1,0,1):0,(1,0,2):2,(1,0,3):0,
         (1,1,0):1,(1,1,1):1,(1,1,2):1,(1,1,3):1,
         (1,2,0):2,(1,2,1):0,(1,2,2):2,(1,2,3):1},
        {(0,0,0):0,(0,0,1):0,(0,1,0):2,(0,1,1):1,(0,2,0):2,(0,2,1):2,(0,3,0):0,(0,3,1):1,
         (1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(1,2,0):1,(1,2,1):0,(1,3,0):3,(1,3,1):0,
         (2,0,0):0,(2,0,1):0,(2,1,0):1,(2,1,1):1,(2,2,0):3,(2,2,1):0,(2,3,0):3,(2,3,1):0},
    ]
    fs = []
    for table in tables:
        def make_f(t):
            def f(L, S, R): return t[(L, S, R)]
            return f
        fs.append(make_f(table))
    return ms, fs


def build_dijkstra_sol1(n, K):
    ms = [K] * n
    def f_distinguished(L, S, R):
        if L == S: return (S + 1) % K
        return S
    def f_other(L, S, R):
        if L != S: return L
        return S
    fs = [f_distinguished] + [f_other] * (n - 1)
    return ms, fs


def build_sol1_style(ms):
    """Sol1-style on arbitrary state vector."""
    n = len(ms)
    fs = []
    for i in range(n):
        m = ms[i]
        if i == 0:
            def f(L, S, R, m=m):
                if L == S: return (S + 1) % m
                return S
        else:
            def f(L, S, R, m=m):
                if L != S: return L % m
                return S
        fs.append(f)
    return fs


def deep_analysis(ms, fs, label=""):
    """Multi-privilege and fiber analysis."""
    n = len(ms)
    P = 1
    for m in ms:
        P *= m

    configs = list(all_configs(ms))
    priv_map = {}
    for c in configs:
        priv_map[c] = privileged_set(c, fs, ms)

    # Build full nondeterministic successor graph
    all_succs = defaultdict(set)  # config -> set of (successor, mover)
    for c in configs:
        for p in priv_map[c]:
            s = apply_move(c, p, fs, ms)
            all_succs[c].add((s, p))

    single_priv = {c for c in configs if len(priv_map[c]) == 1}
    multi_priv = {c for c in configs if len(priv_map[c]) > 1}
    dead = {c for c in configs if len(priv_map[c]) == 0}

    print(f"\n{'='*70}")
    print(f"DEEP ANALYSIS: ms={list(ms)}, P={P}  {label}")
    print(f"{'='*70}")
    print(f"  Single-priv: {len(single_priv)} ({100*len(single_priv)/P:.1f}%)")
    print(f"  Multi-priv:  {len(multi_priv)} ({100*len(multi_priv)/P:.1f}%)")
    print(f"  Dead:        {len(dead)}")

    # Privilege count distribution
    priv_counts = Counter(len(priv_map[c]) for c in configs)
    print(f"  Priv count distribution: {dict(sorted(priv_counts.items()))}")

    # Find the good cycle (deterministic on single-priv)
    succ = {}
    for c in single_priv:
        s = apply_move(c, priv_map[c][0], fs, ms)
        succ[c] = (s, priv_map[c][0])

    # Find closed set
    good_candidates = set(single_priv)
    changed = True
    while changed:
        changed = False
        to_remove = set()
        for c in good_candidates:
            s, _ = succ[c]
            if s not in good_candidates:
                to_remove.add(c)
        if to_remove:
            good_candidates -= to_remove
            changed = True

    # Find cycles
    visited = set()
    cycles = []
    for c in good_candidates:
        if c in visited:
            continue
        path = []
        node = c
        path_set = set()
        while node not in visited and node not in path_set:
            path.append(node)
            path_set.add(node)
            node = succ[node][0]
        if node in path_set:
            cycle_start = path.index(node)
            cycle = path[cycle_start:]
            cycles.append(cycle)
        visited.update(path)

    if not cycles:
        print("  No good cycle found!")
        return

    # Pick fair cycle
    fair_cycle = None
    for cycle in cycles:
        movers = set(succ[c][1] for c in cycle)
        if movers == set(range(n)):
            fair_cycle = cycle
            break
    if not fair_cycle:
        fair_cycle = max(cycles, key=len)

    cycle = fair_cycle
    cycle_set = set(cycle)
    CL = len(cycle)
    mover_seq = [succ[c][1] for c in cycle]
    fair = set(mover_seq) == set(range(n))

    print(f"\n  Good cycle: length={CL}, fair={fair}")
    print(f"  Mover seq: {mover_seq}")

    # ─── Multi-privilege analysis ───
    print(f"\n  --- Multi-Privilege Structure ---")

    # For multi-priv configs: check if ALL successors lead to basin
    # vs if some lead outside
    rev_all = defaultdict(set)
    for c in configs:
        for p in priv_map[c]:
            s = apply_move(c, p, fs, ms)
            rev_all[s].add(c)

    # Deterministic basin (single-priv tree)
    rev_det = defaultdict(list)
    for c in single_priv:
        s, _ = succ[c]
        rev_det[s].append(c)

    det_basin = set(cycle_set)
    queue = deque(cycle_set)
    while queue:
        node = queue.popleft()
        for pred in rev_det[node]:
            if pred not in det_basin:
                det_basin.add(pred)
                queue.append(pred)

    # Full basin (reachability via any move)
    full_basin = set(det_basin)
    queue = deque(det_basin)
    while queue:
        node = queue.popleft()
        for pred in rev_all[node]:
            if pred not in full_basin:
                full_basin.add(pred)
                queue.append(pred)

    print(f"  Det basin (single-priv tree): {len(det_basin)}")
    print(f"  Full basin (any move reaches): {len(full_basin)}")

    # For each multi-priv config in the full basin: can the daemon avoid the cycle?
    # A config c is "convergent" iff ALL paths from c eventually reach the cycle.
    # A config c is "escapable" iff there EXISTS a path from c to the cycle.
    # Self-stabilization requires convergent. We check escapable.

    # Actually, the key distinction is:
    # For convergence, we need that the bad config subgraph has NO cycles.
    # (Because if there's a cycle in bad configs, the daemon can loop forever.)

    # So let's look at bad configs (outside good cycle) and find cycles
    bad = set(configs) - cycle_set
    bad_succs = defaultdict(set)
    for c in bad:
        for p in priv_map[c]:
            s = apply_move(c, p, fs, ms)
            if s in bad:
                bad_succs[c].add(s)

    # Find SCCs in bad region
    # Use simple DFS-based cycle detection
    color = {c: 0 for c in bad}  # 0=white, 1=gray, 2=black
    has_cycle = False
    cycle_configs = set()

    for start in bad:
        if color[start] != 0:
            continue
        stack = [(start, iter(bad_succs.get(start, set())), False)]
        color[start] = 1
        path = [start]

        while stack:
            node, children, done = stack[-1]
            if done:
                stack.pop()
                color[node] = 2
                if path and path[-1] == node:
                    path.pop()
                continue

            try:
                w = next(children)
                if color[w] == 1:
                    # Found cycle!
                    has_cycle = True
                    # Extract cycle from path
                    idx = path.index(w)
                    for cc in path[idx:]:
                        cycle_configs.add(cc)
                elif color[w] == 0:
                    color[w] = 1
                    path.append(w)
                    stack[-1] = (node, children, False)
                    stack.append((w, iter(bad_succs.get(w, set())), False))
            except StopIteration:
                stack[-1] = (node, children, True)

    print(f"\n  Bad config cycles exist: {has_cycle}")
    print(f"  Configs in bad cycles: {len(cycle_configs)}")

    if has_cycle:
        # How many bad configs are multi-priv?
        bad_multi = {c for c in cycle_configs if len(priv_map[c]) > 1}
        bad_single = {c for c in cycle_configs if len(priv_map[c]) == 1}
        print(f"    Multi-priv in bad cycles: {len(bad_multi)}")
        print(f"    Single-priv in bad cycles: {len(bad_single)}")

        # For multi-priv configs in bad cycles: do they have an escape?
        # (A successor that's NOT in a bad cycle?)
        escapable = 0
        for c in bad_multi & cycle_configs:
            for p in priv_map[c]:
                s = apply_move(c, p, fs, ms)
                if s not in cycle_configs:
                    escapable += 1
                    break
        print(f"    Multi-priv in bad cycles with escape: {escapable}")
    else:
        print(f"  => CONVERGENT! (but may still fail mutual exclusion or fairness)")

    # ─── Fiber analysis ───
    print(f"\n  --- Fiber Analysis ---")
    # At each cycle step, the mover p fires. All configs that agree on
    # positions {p-1, p, p+1} have the same transition at p.
    # But configs that differ at positions far from p follow "parallel" paths.

    # Group cycle configs by the values at non-mover positions
    for t in range(min(CL, 5)):
        c = cycle[t]
        p = mover_seq[t]
        near = {(p-1)%n, p, (p+1)%n}
        far = [i for i in range(n) if i not in near]
        far_vals = tuple(c[i] for i in far)
        near_vals = tuple(c[i] for i in sorted(near))
        print(f"  Step {t}: mover={p}, near_vals={near_vals} (pos {sorted(near)}), "
              f"far_vals={far_vals} (pos {far})")

    # For each cycle step: how many OTHER configs have the same near-values?
    # These form the "fiber" — they all make the same transition.
    print(f"\n  Fiber sizes at each step:")
    total_fiber_product = 1
    for t in range(CL):
        c = cycle[t]
        p = mover_seq[t]
        near = {(p-1)%n, p, (p+1)%n}
        far = [i for i in range(n) if i not in near]

        # Count configs matching near values
        near_vals = {i: c[i] for i in sorted(near)}
        fiber_size = 1
        for i in far:
            fiber_size *= ms[i]

        print(f"  Step {t}: mover={p}, fiber_size={fiber_size} (product of far state counts)")

    # ─── Key insight: the "carried-along" dimension ───
    print(f"\n  --- Carried-Along Analysis ---")
    print(f"  When mover p fires, positions far from p are unchanged.")
    print(f"  Two configs differing only at far positions follow parallel paths.")
    print(f"  This creates 'sheets' of configs that shadow the good cycle.")
    print(f"")
    print(f"  BUT: at the NEXT step, a different proc fires, and the previously-far")
    print(f"  position may now be NEAR. So the sheet only lasts one step.")
    print(f"")

    # Track which positions are "untouched" (never near any mover) after k steps
    for start_t in range(1):  # just first step
        untouched = set(range(n))
        for k in range(CL):
            p = mover_seq[(start_t + k) % CL]
            near = {(p-1)%n, p, (p+1)%n}
            untouched -= near
            if not untouched:
                print(f"  From step {start_t}: all positions touched by step {k} ({k+1} steps)")
                break
        else:
            print(f"  From step {start_t}: untouched after full cycle: {sorted(untouched)}")

    # ─── Binary flip persistence through transitions ───
    print(f"\n  --- Binary Flip Persistence ---")
    binary_procs = [i for i in range(n) if ms[i] == 2]
    if binary_procs:
        for b in binary_procs:
            print(f"\n  Binary proc {b}:")
            # Start with a good cycle config, flip b, follow the orbit
            c0 = cycle[0]
            cf = list(c0); cf[b] = 1 - cf[b]; cf = tuple(cf)

            # Follow cf for up to 3*P steps
            node = cf
            orbit = [node]
            visited = {node}
            for step in range(3 * P):
                priv = priv_map[node]
                if not priv:
                    print(f"    Dead at step {step}!")
                    break
                if len(priv) == 1:
                    node = apply_move(node, priv[0], fs, ms)
                else:
                    # Pick first privileged (nondeterministic — we pick one path)
                    node = apply_move(node, priv[0], fs, ms)

                if node in visited:
                    # Found cycle
                    idx = orbit.index(node)
                    tail_len = idx
                    cycle_len = len(orbit) - idx
                    print(f"    Orbit: tail={tail_len}, cycle={cycle_len}, total={len(orbit)}")

                    # Is this cycle in the good cycle?
                    orbit_cycle = orbit[idx:]
                    in_good = sum(1 for c in orbit_cycle if c in cycle_set)
                    print(f"    In good cycle: {in_good}/{cycle_len}")

                    if in_good == 0:
                        print(f"    *** BAD CYCLE (puddle) ***")
                        # Show the bad cycle
                        for i, cc in enumerate(orbit_cycle[:5]):
                            priv_cc = priv_map[cc]
                            print(f"      {cc} priv={priv_cc}")
                    break
                visited.add(node)
                orbit.append(node)
            else:
                print(f"    No cycle found in {3*P} steps")

    # ─── THE CRITICAL TEST: exhaustive search for transition functions ───
    # For ms=(2,2,2,3,3), P=72: can ANY transition function achieve convergence?
    # We know the answer is NO (lower bound proved), but HOW does it fail?
    print(f"\n  --- Convergence Failure Anatomy ---")
    print(f"  For sub-threshold systems, convergence always fails because:")
    print(f"  Multi-priv configs create nondeterministic choices.")
    print(f"  Even if full basin = P (all configs CAN reach cycle),")
    print(f"  a daemon can choose moves that cycle among bad configs.")
    print(f"  The question is: must there ALWAYS be a bad cycle?")


def main():
    print("=" * 70)
    print("DRAINAGE BASIN v2: DEEP DIVE")
    print("=" * 70)

    # 1. Valid M_5=96 witness
    ms96, fs96 = build_m5_96_witness()
    deep_analysis(ms96, fs96, "M_5=96 VALID")

    # 2. Sol1 at various sizes
    for n, K in [(5, 4), (5, 3)]:
        ms, fs = build_dijkstra_sol1(n, K)
        deep_analysis(ms, fs, f"Sol1 n={n} K={K}")

    # 3. Sub-threshold systems
    for ms_test in [(2,2,2,3,3), (2,2,2,2,3), (2,2,2,2,2)]:
        fs_test = build_sol1_style(list(ms_test))
        deep_analysis(list(ms_test), fs_test, "Sol1-style sub-threshold")

    # 4. CRITICAL: Compare bad cycle structure at threshold vs sub-threshold
    print("\n\n" + "=" * 70)
    print("BAD CYCLE COMPARISON: THRESHOLD vs SUB-THRESHOLD")
    print("=" * 70)

    # At threshold (M_5=96): VALID, no bad cycles
    ms96, fs96 = build_m5_96_witness()
    configs96 = list(all_configs(ms96))
    priv96 = {c: privileged_set(c, fs96, ms96) for c in configs96}

    # Count multi-priv at threshold
    multi96 = sum(1 for c in configs96 if len(priv96[c]) > 1)
    print(f"\n  AT THRESHOLD (ms=[2,2,2,3,4], P=96):")
    print(f"    Multi-priv: {multi96}/{96} = {100*multi96/96:.1f}%")

    # Sub-threshold Sol1
    ms_sub = [2, 2, 2, 3, 3]
    fs_sub = build_sol1_style(ms_sub)
    configs_sub = list(all_configs(ms_sub))
    priv_sub = {c: privileged_set(c, fs_sub, ms_sub) for c in configs_sub}
    multi_sub = sum(1 for c in configs_sub if len(priv_sub[c]) > 1)
    print(f"\n  SUB-THRESHOLD (ms=[2,2,2,3,3], P=72):")
    print(f"    Multi-priv: {multi_sub}/{72} = {100*multi_sub/72:.1f}%")

    # The point: multi-priv configs are where the daemon has freedom.
    # More multi-priv => more opportunity for bad cycles.
    # Can we bound the multi-priv fraction?

    # ─── Count multi-priv for various state vectors ───
    print(f"\n  Multi-priv counts for various systems:")
    for ms_test in [(2,2,2,3,3), (2,2,2,3,4), (2,2,2,3,5), (2,2,2,3,6),
                    (2,2,2,4,4), (2,2,3,3,3), (2,3,3,3,3), (3,3,3,3,3)]:
        P = 1
        for m in ms_test:
            P *= m
        fs_test = build_sol1_style(list(ms_test))
        configs_test = list(all_configs(ms_test))
        priv_test = {c: privileged_set(c, fs_test, ms_test) for c in configs_test}
        single = sum(1 for c in configs_test if len(priv_test[c]) == 1)
        multi = sum(1 for c in configs_test if len(priv_test[c]) > 1)
        dead = sum(1 for c in configs_test if len(priv_test[c]) == 0)
        binary_count = sum(1 for m in ms_test if m == 2)
        print(f"    ms={list(ms_test)} P={P:>5} bin={binary_count}: single={single:>4} ({100*single/P:5.1f}%), multi={multi:>4} ({100*multi/P:5.1f}%), dead={dead}")

    # ─── THE REAL QUESTION: In-degree bound for the good cycle ───
    print(f"\n\n{'='*70}")
    print("IN-DEGREE BOUND ANALYSIS")
    print("=" * 70)
    print()
    print("The deterministic basin is tiny (single-priv tree).")
    print("Convergence works through multi-priv configs, which have CHOICES.")
    print("For convergence, NO bad cycle can exist in the full nondeterministic graph.")
    print()
    print("The binary flip ALWAYS breaks single-privilege because the transition")
    print("function at binary proc b depends on b's value (as L, S, or R).")
    print("When you flip b, any neighbor proc whose context includes b will see")
    print("a different (L,S,R), potentially changing privilege status.")
    print()
    print("KEY INSIGHT: The parallel sheet argument FAILS because:")
    print("1. No position is 'always far' from all movers (fairness)")
    print("2. Even for one step, flipping a far binary changes privilege at LATER steps")
    print("3. The transition functions are NOT value-independent at binary procs")
    print()

    # ─── Count in-degree by mover identity ───
    print("In-degree analysis for M_5=96 witness:")
    ms96, fs96 = build_m5_96_witness()
    configs96 = list(all_configs(ms96))

    # For each config c, count predecessors:
    # c' -> c iff there exists p such that:
    #   1. p is privileged in c' (could be one of several)
    #   2. move(c', p) = c
    pred_count = defaultdict(int)
    pred_by_mover = defaultdict(lambda: defaultdict(int))

    for c_prime in configs96:
        priv = privileged_set(c_prime, fs96, ms96)
        for p in priv:
            c = apply_move(c_prime, p, fs96, ms96)
            pred_count[c] += 1
            pred_by_mover[c][p] += 1

    # Stats
    in_degs = [pred_count[c] for c in configs96]
    print(f"  In-degree stats: min={min(in_degs)}, max={max(in_degs)}, avg={sum(in_degs)/len(in_degs):.2f}")
    print(f"  In-degree distribution: {dict(Counter(in_degs))}")

    # Compare: how many predecessors come from mover at binary procs?
    for p in range(5):
        preds_from_p = sum(pred_by_mover[c][p] for c in configs96)
        print(f"  Predecessors via mover {p} (m={ms96[p]}): {preds_from_p}")


if __name__ == "__main__":
    main()
