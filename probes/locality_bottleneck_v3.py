"""
Locality Bottleneck v3: Test an alternative cycle for ms=(2,2,2,3,3)
that avoids the conflicts found in v2.

Key fix: P3 returns to initial state BEFORE P4 does, so P0 sees
different P4 states at the two (0,0,0) binary positions.

If this cycle is consistent AND convergence can be achieved,
then the quaternary necessity conjecture is FALSE.
"""

import sys
sys.path.insert(0, '.')
from itertools import product as iproduct
from collections import defaultdict

ms = [2, 2, 2, 3, 3]
n = 5

# Alternative cycle: P3 returns first, P4 returns second.
# NB pairs used: (0,0), (1,0), (1,1), (0,1) — all 4 of the 2x2 grid.
cycle = [
    (0,0,0,0,0),  # 0: P0 moves
    (1,0,0,0,0),  # 1: P1 moves
    (1,1,0,0,0),  # 2: P2 moves
    (1,1,1,0,0),  # 3: P3 moves
    (1,1,1,1,0),  # 4: P4 moves
    (1,1,1,1,1),  # 5: P0 moves
    (0,1,1,1,1),  # 6: P1 moves
    (0,0,1,1,1),  # 7: P2 moves
    (0,0,0,1,1),  # 8: P3 moves  ← P3 returns FIRST
    (0,0,0,0,1),  # 9: P4 moves  ← then P4 returns → back to start
]
movers = [0, 1, 2, 3, 4, 0, 1, 2, 3, 4]

print("="*70)
print("ALTERNATIVE CYCLE FOR ms=(2,2,2,3,3)")
print("="*70)

# Verify configs are distinct
assert len(set(cycle)) == len(cycle), "Configs not distinct!"
print(f"All {len(cycle)} configs distinct ✓")

# Verify movers are correct
for idx in range(len(cycle)):
    c = cycle[idx]
    c_next = cycle[(idx+1) % len(cycle)]
    diffs = [j for j in range(n) if c[j] != c_next[j]]
    assert len(diffs) == 1, f"Step {idx}: {len(diffs)} diffs"
    assert diffs[0] == movers[idx], f"Step {idx}: mover should be {movers[idx]}, got {diffs[0]}"
print("Mover sequence verified ✓")

# Collect required transition function entries
required = defaultdict(set)  # (proc, L, S, R) -> set of (type, output, step)

for idx in range(len(cycle)):
    c = cycle[idx]
    mover = movers[idx]
    c_next = cycle[(idx+1) % len(cycle)]

    # Mover: privileged
    L = c[(mover-1) % n]
    S = c[mover]
    R = c[(mover+1) % n]
    S_new = c_next[mover]
    required[(mover, L, S, R)].add(('priv', S_new, idx))

    # Non-movers: non-privileged
    for i in range(n):
        if i != mover:
            Li = c[(i-1) % n]
            Si = c[i]
            Ri = c[(i+1) % n]
            required[(i, Li, Si, Ri)].add(('nopriv', Si, idx))

# Check for conflicts
conflicts = []
determined = {}
for key, vals in sorted(required.items()):
    outputs = set(v[1] for v in vals)
    if len(outputs) > 1:
        conflicts.append((key, vals))
    else:
        determined[key] = list(outputs)[0]

if conflicts:
    print(f"\nCONFLICTS FOUND: {len(conflicts)}")
    for key, vals in conflicts:
        print(f"  f{key[0]}({key[1]},{key[2]},{key[3]}): {vals}")
    print("\nThis cycle structure is IMPOSSIBLE.")
else:
    print(f"\nNO CONFLICTS — cycle is consistent! ✓")

    # Show determined entries per processor
    proc_entries = defaultdict(dict)
    for (proc, L, S, R), out in determined.items():
        proc_entries[proc][(L, S, R)] = out

    print("\nDetermined transition entries:")
    for proc in range(n):
        m_L = ms[(proc-1) % n]
        m_S = ms[proc]
        m_R = ms[(proc+1) % n]
        total = m_L * m_S * m_R
        det = len(proc_entries[proc])
        print(f"  P{proc}: {det}/{total} entries")
        for (L,S,R), out in sorted(proc_entries[proc].items()):
            priv = "PRIV" if out != S else "nopriv"
            print(f"    f{proc}({L},{S},{R}) = {out}  [{priv}]")

    # ================================================================
    # NOW: Try to complete transition functions and check convergence
    # Strategy: fix determined entries, enumerate free entries for
    # the smallest processors first (P1 has fewest free entries).
    # ================================================================

    print("\n" + "="*70)
    print("CONVERGENCE CHECK")
    print("="*70)

    # Build transition function templates
    # f[proc][(L,S,R)] = output
    f = [dict() for _ in range(n)]
    for (proc, L, S, R), out in determined.items():
        f[proc][(L, S, R)] = out

    # Enumerate ALL possible inputs for each processor
    all_inputs = []
    for proc in range(n):
        m_L = ms[(proc-1) % n]
        m_S = ms[proc]
        m_R = ms[(proc+1) % n]
        inputs = [(L,S,R) for L in range(m_L) for S in range(m_S) for R in range(m_R)]
        all_inputs.append(inputs)

    # Find free entries for each processor
    free_entries = []
    for proc in range(n):
        free = [(L,S,R) for (L,S,R) in all_inputs[proc] if (L,S,R) not in f[proc]]
        free_entries.append(free)
        print(f"  P{proc}: {len(free)} free entries")

    # Total search space
    total_free = 1
    for proc in range(n):
        for (L,S,R) in free_entries[proc]:
            total_free *= ms[proc]
    print(f"  Total search space: {total_free}")

    # That's too large. Let me try a SMART approach:
    # Use the verifier to check specific completions.

    # First, let's try a "Dijkstra-like" completion:
    # f_i(L, S, R) = L for all free entries (copy left neighbor)
    # This is a simple heuristic.

    def make_system(f_templates, free_choices):
        """Create complete transition functions from templates + free choices."""
        f_complete = [dict(t) for t in f_templates]
        idx = 0
        for proc in range(n):
            for (L,S,R) in free_entries[proc]:
                f_complete[proc][(L,S,R)] = free_choices[idx]
                idx += 1
        return f_complete

    def privileged_set(config, f_complete):
        """Return set of privileged processors."""
        priv = set()
        for i in range(n):
            L = config[(i-1) % n]
            S = config[i]
            R = config[(i+1) % n]
            if f_complete[i][(L,S,R)] != S:
                priv.add(i)
        return priv

    def apply_move(config, proc, f_complete):
        """Apply move by proc, return new config."""
        c = list(config)
        L = config[(proc-1) % n]
        S = config[proc]
        R = config[(proc+1) % n]
        c[proc] = f_complete[proc][(L,S,R)]
        return tuple(c)

    def check_convergence(f_complete, good_set, max_steps=500):
        """Check if all configs converge to good cycle.
        Returns (True, None) or (False, bad_cycle)."""
        all_configs = list(iproduct(*[range(m) for m in ms]))

        for start in all_configs:
            if start in good_set:
                continue
            # BFS/DFS: try all possible daemon choices
            # Use iterative deepening to find bad cycles
            visited = set()
            stack = [(start, [start])]
            found_good = False
            bad_found = False

            # Simple check: from each bad config, can the daemon
            # get stuck in a cycle? Use worst-case analysis.
            # For each config, compute all possible successors.
            pass

        # Better approach: build the full transition graph and check
        # for bad attractors.

        # For each config, compute the set of possible next configs
        # (one for each privileged processor).
        successors = {}
        for config in all_configs:
            priv = privileged_set(config, f_complete)
            if not priv:
                # No one privileged and not on good cycle = deadlock
                if config not in good_set:
                    return (False, f"Deadlock at {config}")
                continue
            succs = set()
            for p in priv:
                succs.add(apply_move(config, p, f_complete))
            successors[config] = succs

        # Check mutual exclusion on good cycle
        for gc in good_set:
            priv = privileged_set(gc, f_complete)
            if len(priv) != 1:
                return (False, f"ME violation at {gc}: {priv}")

        # Find all configs that can reach good cycle
        # (backward reachability from good cycle)
        reachable = set(good_set)
        changed = True
        while changed:
            changed = False
            for config in all_configs:
                if config in reachable:
                    continue
                if config not in successors:
                    continue
                # config reaches good cycle if ALL successors lead
                # to reachable configs (worst-case daemon)
                # Actually for convergence under ANY daemon,
                # we need: from config, ALL paths reach good cycle.
                # This means: no bad cycle reachable from config.
                pass

        # Better: find all SCCs in the transition graph.
        # A bad attractor is an SCC with no edge to a good config.

        # Build full graph
        graph = defaultdict(set)
        for config, succs in successors.items():
            for s in succs:
                graph[config].add(s)

        # Find SCCs using Tarjan's algorithm
        index_counter = [0]
        stack = []
        lowlink = {}
        index = {}
        on_stack = set()
        sccs = []

        def strongconnect(v):
            index[v] = index_counter[0]
            lowlink[v] = index_counter[0]
            index_counter[0] += 1
            stack.append(v)
            on_stack.add(v)

            for w in graph.get(v, []):
                if w not in index:
                    strongconnect(w)
                    lowlink[v] = min(lowlink[v], lowlink[w])
                elif w in on_stack:
                    lowlink[v] = min(lowlink[v], index[w])

            if lowlink[v] == index[v]:
                scc = set()
                while True:
                    w = stack.pop()
                    on_stack.discard(w)
                    scc.add(w)
                    if w == v:
                        break
                sccs.append(scc)

        for v in all_configs:
            if v not in index:
                strongconnect(v)

        # Check: any SCC that doesn't contain a good config and has
        # no edge to outside itself?
        # An SCC is a "bad attractor" if:
        # 1. It contains no good config
        # 2. It is a "bottom SCC" (no edges leaving it)
        # Actually, for worst-case daemon, we need stricter:
        # An SCC is "bad" if it contains no good config and there
        # exists some config in it where ALL successors stay in the SCC.

        # For convergence under worst-case daemon:
        # We need: for every config c not on good cycle,
        # every path from c (under any daemon choices) must eventually
        # reach the good cycle.
        # Equivalently: there is no "bad attractor" — no set S of
        # non-good configs such that for every c in S, there exists
        # a successor of c that is also in S.

        # This is the "adversarial attractor" condition.
        # Compute: start with all non-good configs.
        # Remove any config where ALL successors lead outside the set.
        # Repeat until stable.

        bad_configs = set(all_configs) - good_set
        changed = True
        while changed:
            changed = False
            to_remove = set()
            for c in bad_configs:
                if c not in successors:
                    to_remove.add(c)
                    continue
                # c is "safe" if ALL its successors are either good or
                # already removed from bad_configs.
                # c is "stuck" if at least one successor is in bad_configs.
                if all(s not in bad_configs for s in successors[c]):
                    to_remove.add(c)
            if to_remove:
                bad_configs -= to_remove
                changed = True

        if bad_configs:
            return (False, f"Bad attractor of size {len(bad_configs)}: {list(bad_configs)[:5]}...")
        else:
            return (True, None)

    good_set = set(cycle)

    # Try simple completions
    print("\nTrying completion strategies...")

    # Strategy 1: f_i(L,S,R) = S for all free entries (no one is privileged)
    # This minimizes privilege, but may create deadlocks.
    choices_noop = []
    for proc in range(n):
        for (L,S,R) in free_entries[proc]:
            choices_noop.append(S)  # stay put

    f1_system = make_system([dict(f[p]) for p in range(n)], choices_noop)
    ok, reason = check_convergence(f1_system, good_set)
    print(f"  Strategy 'stay put': {'✓ VALID' if ok else '✗ ' + str(reason)}")

    # Strategy 2: f_i(L,S,R) = L for free entries (copy left)
    choices_left = []
    for proc in range(n):
        for (L,S,R) in free_entries[proc]:
            choices_left.append(L % ms[proc])  # copy left, mod state count

    f2_system = make_system([dict(f[p]) for p in range(n)], choices_left)
    ok, reason = check_convergence(f2_system, good_set)
    print(f"  Strategy 'copy left': {'✓ VALID' if ok else '✗ ' + str(reason)}")

    # Strategy 3: f_i(L,S,R) = R for free entries (copy right)
    choices_right = []
    for proc in range(n):
        for (L,S,R) in free_entries[proc]:
            choices_right.append(R % ms[proc])

    f3_system = make_system([dict(f[p]) for p in range(n)], choices_right)
    ok, reason = check_convergence(f3_system, good_set)
    print(f"  Strategy 'copy right': {'✓ VALID' if ok else '✗ ' + str(reason)}")

    # Strategy 4: Random search
    import random
    random.seed(42)

    best_bad = float('inf')
    found_valid = False

    for trial in range(10000):
        choices = []
        for proc in range(n):
            for (L,S,R) in free_entries[proc]:
                choices.append(random.randint(0, ms[proc]-1))

        f_system = make_system([dict(f[p]) for p in range(n)], choices)
        ok, reason = check_convergence(f_system, good_set)

        if ok:
            print(f"\n  *** VALID SYSTEM FOUND at trial {trial}! ***")
            found_valid = True
            # Print the transition functions
            for proc in range(n):
                print(f"\n  f{proc}:")
                for (L,S,R) in sorted(f_system[proc].keys()):
                    out = f_system[proc][(L,S,R)]
                    on_cycle = "*" if (proc, L, S, R) in determined else " "
                    print(f"    {on_cycle} f{proc}({L},{S},{R}) = {out}")
            break
        else:
            if isinstance(reason, str) and "Bad attractor" in reason:
                size = int(reason.split("size ")[1].split(":")[0])
                if size < best_bad:
                    best_bad = size

    if not found_valid:
        print(f"\n  No valid system found in 10000 random trials.")
        print(f"  Smallest bad attractor: {best_bad} configs")

        # ============================================================
        # DEEPER ANALYSIS: Why does convergence fail?
        # ============================================================
        print("\n" + "="*70)
        print("ANALYZING WHY CONVERGENCE FAILS")
        print("="*70)

        # Check: how many configs have privilege determined by cycle?
        # For configs NOT on the good cycle, what privilege info is determined?

        all_configs = list(iproduct(*[range(m) for m in ms]))

        # For each non-cycle config, check how many processors have
        # their privilege status determined by cycle entries.
        determined_keys = set(determined.keys())

        priv_determined = 0
        priv_undetermined = 0

        for config in all_configs:
            if config in good_set:
                continue
            for i in range(n):
                L = config[(i-1) % n]
                S = config[i]
                R = config[(i+1) % n]
                if (i, L, S, R) in determined_keys:
                    priv_determined += 1
                else:
                    priv_undetermined += 1

        print(f"  Non-cycle configs: {len(all_configs) - len(cycle)}")
        print(f"  Privilege status determined: {priv_determined}")
        print(f"  Privilege status undetermined: {priv_undetermined}")

        # List non-cycle configs where ALL processors have determined privilege
        fully_det = []
        for config in all_configs:
            if config in good_set:
                continue
            all_det = True
            for i in range(n):
                L = config[(i-1) % n]
                S = config[i]
                R = config[(i+1) % n]
                if (i, L, S, R) not in determined_keys:
                    all_det = False
                    break
            if all_det:
                # Compute privilege set
                priv = set()
                for i in range(n):
                    L = config[(i-1) % n]
                    S = config[i]
                    R = config[(i+1) % n]
                    if determined[(i, L, S, R)] != S:
                        priv.add(i)
                fully_det.append((config, priv))

        print(f"\n  Fully determined non-cycle configs: {len(fully_det)}")
        for config, priv in fully_det[:20]:
            print(f"    {config}  priv={priv}")
