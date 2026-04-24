#!/usr/bin/env python3
"""PA: 3CB Convergence Failure — Part 3.

Key findings so far:
1. n=4, ms=(2,2,2,3), P=24: 19 valid systems found.
2. n=5, ms=(2,2,2,3,3), P=72 < M_5=96: should have NO valid system.
3. The ratio P_rest/min_gcl grows exponentially: 0.3 at n=4, 0.75 at n=5, 30.4 at n=9.

This script:
- Exhaustively checks n=5 with MORE transition function options
- If n=5 has valid 3CB systems (which would be surprising since P=72 < M_5=96),
  find them. If not, characterize the failure mode.
- Check n=4 with ms=(2,2,2,2) (P=16 < M_4=24) -- sub-threshold with 4CB.
"""

import itertools
from collections import defaultdict, deque
from math import prod


def check_system(configs, fs, ms, n):
    """Check a system for all 5 Dijkstra properties. Return detailed result."""
    priv_map = {}
    for c in configs:
        priv = []
        for i in range(n):
            L = c[(i-1) % n]
            S = c[i]
            R = c[(i+1) % n]
            if fs[i](L, S, R) != S:
                priv.append(i)
        priv_map[c] = priv

    dead = [c for c in configs if len(priv_map[c]) == 0]
    if dead:
        return {'valid': False, 'reason': 'liveness', 'priv_map': priv_map}

    good = {c for c in configs if len(priv_map[c]) == 1}
    bad = {c for c in configs if len(priv_map[c]) >= 2}

    if len(good) < n:
        return {'valid': False, 'reason': 'too_few_good', 'priv_map': priv_map,
                'good': good, 'bad': bad}

    # Closure
    succ = {}
    for c in good:
        p = priv_map[c][0]
        nc = list(c)
        nc[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
        succ[c] = tuple(nc)

    for c in good:
        if succ[c] not in good:
            return {'valid': False, 'reason': 'closure', 'priv_map': priv_map,
                    'good': good, 'bad': bad}

    # Find fair cycle
    visited = set()
    cycles = []
    for start in good:
        if start in visited:
            continue
        path = [start]
        visited.add(start)
        c = succ[start]
        while c not in visited:
            visited.add(c)
            path.append(c)
            c = succ[c]
        if c in set(path):
            idx = path.index(c)
            cycles.append(path[idx:])

    fair_cycle = None
    for cycle in cycles:
        procs_visited = {priv_map[c][0] for c in cycle}
        if len(procs_visited) == n:
            fair_cycle = cycle
            break

    if fair_cycle is None:
        return {'valid': False, 'reason': 'fairness', 'priv_map': priv_map,
                'good': good, 'bad': bad, 'cycles': cycles}

    good = set(fair_cycle)
    bad = set(configs) - good

    # Bad SCC check
    can_reach_good = set()
    bad_succ_map = defaultdict(set)
    for c in bad:
        for p in priv_map[c]:
            nc = list(c)
            nc[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
            nc = tuple(nc)
            bad_succ_map[c].add(nc)
            if nc in good:
                can_reach_good.add(c)

    bad_pred = defaultdict(set)
    for c in bad:
        for nc in bad_succ_map[c]:
            if nc in bad:
                bad_pred[nc].add(c)

    queue = deque(can_reach_good)
    while queue:
        c = queue.popleft()
        for pred in bad_pred[c]:
            if pred not in can_reach_good:
                can_reach_good.add(pred)
                queue.append(pred)

    stuck = bad - can_reach_good
    if stuck:
        return {'valid': False, 'reason': 'convergence', 'priv_map': priv_map,
                'good': good, 'bad': bad, 'stuck': stuck,
                'bad_scc_size': len(stuck)}

    return {'valid': True, 'priv_map': priv_map, 'good': good, 'bad': bad,
            'good_count': len(good), 'bad_scc_size': 0}


def make_func_from_table(table):
    def f(L, S, R):
        return table[(L, S, R)]
    return f


def exhaustive_n5():
    """Exhaustive search at n=5, ms=(2,2,2,3,3), P=72.

    We need to be smart about which functions to try.
    Strategy: fix procs 3,4 to Dijkstra-style, enumerate ALL for proc 1 (256),
    and try a comprehensive set for procs 0, 2.

    For proc 0: context (c[4], c[0], c[1]) with c[4] in {0,1,2}.
    For proc 2: context (c[1], c[2], c[3]) with c[3] in {0,1,2}.

    These are 12-context binary functions. Instead of 2^12 each, decompose:
    For proc 0: (L,R) pairs where L=c[4] in {0,1,2}, R=c[1] in {0,1}: 6 pairs.
    For each pair, 4 choices -> 4^6 = 4096 functions.
    Same for proc 2.

    With 256 * 4096 * 4096 = 4.3 billion: too many.
    But we can use the n=4 insight: valid n=4 systems used specific patterns
    (L==S, S==R, S!=R). Let's expand to more patterns but not all.
    """
    n = 5
    ms = [2, 2, 2, 3, 3]
    P = prod(ms)
    configs = list(itertools.product(*(range(m) for m in ms)))

    print(f"n={n}, ms={ms}, P={P}, M_5=96")
    print(f"Sub-threshold (P < M_5): {P < 96}")

    # Ternary procs: try both Dijkstra variants
    def f_inc(L, S, R):
        return (S+1) % 3 if L != S else S

    def f_dec(L, S, R):
        return (S-1) % 3 if L != S else S

    def f_right_inc(L, S, R):
        return (S+1) % 3 if S != R else S

    def f_right_dec(L, S, R):
        return (S-1) % 3 if S != R else S

    ternary_options = [
        ("L!=S,inc", f_inc),
        ("L!=S,dec", f_dec),
        ("S!=R,inc", f_right_inc),
        ("S!=R,dec", f_right_dec),
    ]

    # Binary procs: expand the set of rules
    # For procs 0 and 2 whose neighbors include ternary procs:
    # We need functions (L,S,R) -> {0,1} for various context sizes.

    def make_binary_rules_for_context(L_range, R_range):
        """Generate a comprehensive set of binary rules."""
        rules = []

        # Standard rules
        rules.append(("L!=S", lambda L, S, R: (1-S) if L != S else S))
        rules.append(("S!=R", lambda L, S, R: (1-S) if S != R else S))
        rules.append(("L!=R", lambda L, S, R: (1-S) if L != R else S))
        rules.append(("L==S", lambda L, S, R: (1-S) if L == S else S))
        rules.append(("S==R", lambda L, S, R: (1-S) if S == R else S))
        rules.append(("L==R", lambda L, S, R: (1-S) if L == R else S))
        rules.append(("toggle", lambda L, S, R: 1-S))
        rules.append(("L%2!=S", lambda L, S, R: (1-S) if L % 2 != S else S))
        rules.append(("R%2!=S", lambda L, S, R: (1-S) if R % 2 != S else S))
        rules.append(("L%2==S", lambda L, S, R: (1-S) if L % 2 == S else S))
        rules.append(("R%2==S", lambda L, S, R: (1-S) if R % 2 == S else S))
        # XOR-type rules
        rules.append(("L^S!=R%2", lambda L, S, R: (1-S) if (L ^ S) != R % 2 else S))
        rules.append(("L%2^R%2!=S", lambda L, S, R: (1-S) if (L%2) ^ (R%2) != S else S))
        # Threshold rules
        if max(L_range) >= 2:
            rules.append(("L>=2", lambda L, S, R: (1-S) if L >= 2 else S))
            rules.append(("L<2", lambda L, S, R: (1-S) if L < 2 else S))
        if max(R_range) >= 2:
            rules.append(("R>=2", lambda L, S, R: (1-S) if R >= 2 else S))
            rules.append(("R<2", lambda L, S, R: (1-S) if R < 2 else S))
        # Combined rules
        rules.append(("L!=S&S!=R", lambda L, S, R: (1-S) if L != S and S != R else S))
        rules.append(("L!=S|S!=R", lambda L, S, R: (1-S) if L != S or S != R else S))
        rules.append(("L==S&S==R", lambda L, S, R: (1-S) if L == S and S == R else S))

        return rules

    p0_L_range = range(ms[4])  # c[4] in {0,1,2}
    p0_R_range = range(ms[1])  # c[1] in {0,1}
    p2_L_range = range(ms[1])  # c[1] in {0,1}
    p2_R_range = range(ms[3])  # c[3] in {0,1,2}

    p0_rules = make_binary_rules_for_context(p0_L_range, p0_R_range)
    p2_rules = make_binary_rules_for_context(p2_L_range, p2_R_range)

    # Proc 1 contexts: all binary. (c[0], c[1], c[2]) in {0,1}^3.
    p1_contexts = [(a, b, c) for a in range(2) for b in range(2) for c in range(2)]
    p1_rules = make_binary_rules_for_context(range(2), range(2))

    print(f"\nRule counts: p0={len(p0_rules)}, p1={len(p1_rules)}, p2={len(p2_rules)}")
    print(f"Ternary options: {len(ternary_options)}")

    valid_count = 0
    total = 0
    failure_reasons = defaultdict(int)
    convergence_details = []

    for f0_name, f0 in p0_rules:
        for f1_name, f1 in p1_rules:
            for f2_name, f2 in p2_rules:
                for f3_name, f3 in ternary_options:
                    for f4_name, f4 in ternary_options:
                        fs = [f0, f1, f2, f3, f4]
                        total += 1

                        result = check_system(configs, fs, ms, n)
                        if result['valid']:
                            valid_count += 1
                            print(f"  VALID! f0={f0_name}, f1={f1_name}, f2={f2_name}, "
                                  f"f3={f3_name}, f4={f4_name}")
                            print(f"    good={result['good_count']}")
                        else:
                            failure_reasons[result['reason']] += 1
                            if result['reason'] == 'convergence' and len(convergence_details) < 20:
                                convergence_details.append({
                                    'f0': f0_name, 'f1': f1_name, 'f2': f2_name,
                                    'f3': f3_name, 'f4': f4_name,
                                    'scc_size': result.get('bad_scc_size', 0),
                                    'good': len(result.get('good', set())),
                                    'bad': len(result.get('bad', set())),
                                })

    print(f"\nTotal: {total}, Valid: {valid_count}")
    print(f"Failures: {dict(failure_reasons)}")

    if convergence_details:
        print(f"\nSample convergence failures:")
        for d in convergence_details[:10]:
            print(f"  {d}")

    return valid_count


def four_cb_check():
    """Check 4CB at n=4: ms=(2,2,2,2), P=16.

    This is a known impossibility (4 consecutive binary, Gouda-Haddix).
    Let's verify and understand the mechanism.
    """
    n = 4
    ms = [2, 2, 2, 2]
    P = prod(ms)
    configs = list(itertools.product(*(range(m) for m in ms)))

    print(f"\n{'='*60}")
    print(f"4CB CHECK: n={n}, ms={ms}, P={P}")
    print(f"{'='*60}")

    # All binary: each proc has 8 contexts {0,1}^3. 2^8 = 256 functions each.
    # Total: 256^4 = 4.3 billion. Too many.
    # Use rule-based approach.

    rules = [
        ("L!=S", lambda L, S, R: (1-S) if L != S else S),
        ("S!=R", lambda L, S, R: (1-S) if S != R else S),
        ("L!=R", lambda L, S, R: (1-S) if L != R else S),
        ("L==S", lambda L, S, R: (1-S) if L == S else S),
        ("S==R", lambda L, S, R: (1-S) if S == R else S),
        ("L==R", lambda L, S, R: (1-S) if L == R else S),
        ("toggle", lambda L, S, R: 1-S),
        ("L^R!=S", lambda L, S, R: (1-S) if (L ^ R) != S else S),
        ("L^R==S", lambda L, S, R: (1-S) if (L ^ R) == S else S),
    ]

    valid_count = 0
    total = 0
    failure_reasons = defaultdict(int)

    for f0_name, f0 in rules:
        for f1_name, f1 in rules:
            for f2_name, f2 in rules:
                for f3_name, f3 in rules:
                    fs = [f0, f1, f2, f3]
                    total += 1
                    result = check_system(configs, fs, ms, n)
                    if result['valid']:
                        valid_count += 1
                        print(f"  VALID! {f0_name},{f1_name},{f2_name},{f3_name}")
                    failure_reasons[result['reason']] += 1

    print(f"\nTotal: {total}, Valid: {valid_count}")
    print(f"Failures: {dict(failure_reasons)}")


def analyze_valid_n4_systems():
    """Analyze the valid n=4 3CB systems in detail.

    From Part 2: 19 valid systems at n=4, ms=(2,2,2,3).
    All have good=9 configs. Total=24. Bad=15.

    Key question: what makes these work? What's the drainage structure?
    """
    n = 4
    ms = [2, 2, 2, 3]
    P = prod(ms)
    configs = list(itertools.product(*(range(m) for m in ms)))

    print(f"\n{'='*60}")
    print(f"VALID n=4 SYSTEM ANALYSIS: ms={ms}, P={P}")
    print(f"{'='*60}")

    # Recreate one valid system: f0=L==S, f1=L!=S, f2=L!=S, f3=Dijkstra_L!=S
    def f0(L, S, R):
        return (1-S) if L == S else S  # L==S: priv
    def f1(L, S, R):
        return (1-S) if L != S else S  # L!=S: priv
    def f2(L, S, R):
        return (1-S) if L != S else S  # L!=S: priv
    def f3(L, S, R):
        return (S+1) % 3 if L != S else S  # Dijkstra

    fs = [f0, f1, f2, f3]
    result = check_system(configs, fs, ms, n)
    print(f"System valid: {result['valid']}")
    if not result['valid']:
        print(f"  Reason: {result['reason']}")
        return

    good = result['good']
    bad = result['bad']
    priv_map = result['priv_map']

    print(f"Good configs ({len(good)}):")
    for c in sorted(good):
        p = priv_map[c][0]
        print(f"  {c} -> proc {p}")

    print(f"\nBad configs ({len(bad)}):")
    for c in sorted(bad):
        print(f"  {c} priv={priv_map[c]}")

    # Analyze proc 1 privilege in bad configs
    bad_with_p1 = {c for c in bad if 1 in priv_map[c]}
    print(f"\nBad with proc 1 priv: {len(bad_with_p1)}")
    for c in sorted(bad_with_p1):
        # Show what happens when we fire each privileged proc
        for p in priv_map[c]:
            nc = list(c)
            nc[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
            nc = tuple(nc)
            status = "GOOD" if nc in good else "BAD"
            print(f"  {c} fire {p} -> {nc} [{status}] priv={priv_map.get(nc, [])}")

    # Drainage analysis: from each bad config, what paths lead to good?
    print(f"\nDrainage paths from bad configs with proc 1 priv:")
    for c in sorted(bad_with_p1):
        # BFS from c
        visited = {c}
        queue = deque([c])
        path_to_good = None
        parents = {}
        while queue and path_to_good is None:
            curr = queue.popleft()
            for p in priv_map[curr]:
                nc = list(curr)
                nc[p] = fs[p](curr[(p-1)%n], curr[p], curr[(p+1)%n])
                nc = tuple(nc)
                if nc in good:
                    # Found path to good
                    path = [curr, f"fire_{p}", nc]
                    cc = curr
                    while cc in parents:
                        pp, prev = parents[cc]
                        path = [prev, f"fire_{pp}"] + path
                        cc = prev
                    path_to_good = path
                    break
                if nc not in visited and nc in bad:
                    visited.add(nc)
                    parents[nc] = (p, curr)
                    queue.append(nc)

        if path_to_good:
            print(f"  {c}: path length {len(path_to_good)//2}")
        else:
            print(f"  {c}: NO PATH TO GOOD!")


def proc1_privilege_persistence_n5():
    """At n=5, specifically check the privilege persistence mechanism.

    For each transition function combination that passes liveness+closure+fairness:
    1. Fix proc 1's privileged context (a,b,c) in M.
    2. Count configs where proc 1 has this context.
    3. Check: when far procs fire, do these configs cycle?
    """
    n = 5
    ms = [2, 2, 2, 3, 3]
    P = prod(ms)
    configs = list(itertools.product(*(range(m) for m in ms)))

    print(f"\n{'='*60}")
    print(f"PRIVILEGE PERSISTENCE at n={n}")
    print(f"{'='*60}")

    # Use rules that worked at n=4
    def f0(L, S, R):
        return (1-S) if L == S else S
    def f1(L, S, R):
        return (1-S) if L != S else S
    def f2(L, S, R):
        return (1-S) if L != S else S
    def f3(L, S, R):
        return (S+1) % 3 if L != S else S
    def f4(L, S, R):
        return (S+1) % 3 if L != S else S

    fs = [f0, f1, f2, f3, f4]

    priv_map = {}
    for c in configs:
        priv = []
        for i in range(n):
            L = c[(i-1) % n]
            S = c[i]
            R = c[(i+1) % n]
            if fs[i](L, S, R) != S:
                priv.append(i)
        priv_map[c] = priv

    dead = sum(1 for c in configs if len(priv_map[c]) == 0)
    good = {c for c in configs if len(priv_map[c]) == 1}
    bad = {c for c in configs if len(priv_map[c]) >= 2}

    print(f"Dead: {dead}, Good: {len(good)}, Bad: {len(bad)}")

    if dead > 0:
        print("System has dead configs -- not viable")
        dead_configs = [c for c in configs if len(priv_map[c]) == 0]
        for c in dead_configs[:5]:
            print(f"  Dead: {c}")
        return

    # Check closure
    closed = True
    for c in good:
        p = priv_map[c][0]
        nc = list(c)
        nc[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
        nc = tuple(nc)
        if nc not in good:
            closed = False
            print(f"  Closure fails: {c} fire {p} -> {tuple(nc)} not in good")
            break

    if not closed:
        print("Closure fails!")

    # Proc 1 privilege analysis
    M = set()
    for a in range(2):
        for b in range(2):
            for c_ in range(2):
                if f1(a, b, c_) != b:
                    M.add((a, b, c_))

    print(f"\nProc 1 privilege set M = {M}")
    print(f"|M| = {len(M)}")

    # For proc 1 with rule L!=S:
    # Privileged when c[0] != c[1].
    # M = {(0,1,0), (0,1,1), (1,0,0), (1,0,1)} -> |M|=4

    # Configs where proc 1 is privileged: |M| * P_rest = 4 * 9 = 36
    priv1_configs = {c for c in configs if 1 in priv_map[c]}
    print(f"Configs with proc 1 priv: {len(priv1_configs)}")

    # Of these, how many are good?
    good_with_p1 = priv1_configs & good
    bad_with_p1 = priv1_configs & bad
    print(f"  Good with proc 1 priv: {len(good_with_p1)}")
    print(f"  Bad with proc 1 priv: {len(bad_with_p1)}")

    # Far procs: 3, 4
    # When a far proc fires, proc 1's context (c[0],c[1],c[2]) doesn't change.
    # Check: do far-proc fires keep us in priv1_configs?
    far_closure = True
    for c in priv1_configs:
        for p in [3, 4]:
            if p in priv_map[c]:  # far proc is privileged
                nc = list(c)
                nc[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
                nc = tuple(nc)
                if tuple(nc) not in priv1_configs:
                    far_closure = False
                    print(f"  Far closure fails: {c} fire {p} -> {tuple(nc)}")

    print(f"Far-proc fires preserve proc 1 privilege: {far_closure}")

    # Check: within bad_with_p1, do far-proc fires form cycles?
    print(f"\nFar-proc fire graph within bad_with_p1:")
    far_succ = defaultdict(set)
    for c in bad_with_p1:
        for p in [3, 4]:
            if p in priv_map[c]:
                nc = list(c)
                nc[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
                nc = tuple(nc)
                if nc in bad_with_p1:
                    far_succ[c].add(nc)

    # Find SCCs in this subgraph
    # Tarjan's algorithm
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

        for w in far_succ.get(v, set()):
            if w not in index:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], index[w])

        if lowlink[v] == index[v]:
            scc = []
            while True:
                w = stack.pop()
                on_stack.discard(w)
                scc.append(w)
                if w == v:
                    break
            if len(scc) > 1:
                sccs.append(scc)

    for v in bad_with_p1:
        if v not in index:
            strongconnect(v)

    print(f"  Far-proc SCCs in bad_with_p1: {len(sccs)}")
    for i, scc in enumerate(sccs[:5]):
        print(f"  SCC {i}: size {len(scc)}")
        for c in scc[:3]:
            print(f"    {c} priv={priv_map[c]}")

    # Now check: for configs in these SCCs, can they escape through near-proc fires?
    if sccs:
        print(f"\nEscape analysis for far-proc SCCs:")
        for scc in sccs[:3]:
            scc_set = set(scc)
            can_escape = 0
            for c in scc:
                for p in priv_map[c]:
                    if p not in [3, 4]:  # near proc or proc 1
                        nc = list(c)
                        nc[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
                        nc = tuple(nc)
                        if nc not in scc_set:
                            can_escape += 1
                            break
            print(f"  SCC size {len(scc)}: {can_escape} configs can escape via near-proc fire")


def count_convergence_failures_by_n():
    """For each n from 4 to 7, count how many rule-based systems
    pass liveness+closure+fairness and check convergence.

    This reveals the phase transition.
    """
    print(f"\n{'='*60}")
    print(f"CONVERGENCE FAILURE RATE BY n")
    print(f"{'='*60}")

    # Common rules
    binary_rules = [
        ("L!=S", lambda L, S, R: (1-S) if L != S else S),
        ("S!=R", lambda L, S, R: (1-S) if S != R else S),
        ("L!=R", lambda L, S, R: (1-S) if L != R else S),
        ("L==S", lambda L, S, R: (1-S) if L == S else S),
        ("S==R", lambda L, S, R: (1-S) if S == R else S),
        ("L==R", lambda L, S, R: (1-S) if L == R else S),
        ("toggle", lambda L, S, R: 1-S),
        ("L%2!=S", lambda L, S, R: (1-S) if L % 2 != S else S),
        ("R%2!=S", lambda L, S, R: (1-S) if R % 2 != S else S),
    ]

    ternary_rules = [
        ("L!=S,inc", lambda L, S, R: (S+1) % 3 if L != S else S),
        ("L!=S,dec", lambda L, S, R: (S-1) % 3 if L != S else S),
        ("S!=R,inc", lambda L, S, R: (S+1) % 3 if S != R else S),
        ("S!=R,dec", lambda L, S, R: (S-1) % 3 if S != R else S),
    ]

    for n in [4, 5, 6]:
        ms = [2, 2, 2] + [3] * (n - 3)
        P = prod(ms)
        configs = list(itertools.product(*(range(m) for m in ms)))

        print(f"\nn={n}, ms={ms}, P={P}, threshold={4*3**(n-2)}")

        total = 0
        valid = 0
        failure_reasons = defaultdict(int)

        for f0_name, f0 in binary_rules:
            for f1_name, f1 in binary_rules:
                for f2_name, f2 in binary_rules:
                    ternary_combos = list(itertools.product(ternary_rules, repeat=n-3))
                    for t_combo in ternary_combos:
                        t_names = [t[0] for t in t_combo]
                        t_funcs = [t[1] for t in t_combo]
                        fs = [f0, f1, f2] + t_funcs
                        total += 1

                        result = check_system(configs, fs, ms, n)
                        if result['valid']:
                            valid += 1
                            failure_reasons['valid'] += 1
                        else:
                            failure_reasons[result['reason']] += 1

        print(f"  Total: {total}, Valid: {valid}")
        print(f"  Failures: {dict(failure_reasons)}")
        conv_fail = failure_reasons.get('convergence', 0)
        pass_pre_conv = total - failure_reasons.get('liveness', 0) - \
                        failure_reasons.get('too_few_good', 0) - \
                        failure_reasons.get('closure', 0) - \
                        failure_reasons.get('fairness', 0)
        print(f"  Pass pre-convergence: {pass_pre_conv}")
        print(f"  Convergence failures: {conv_fail}")
        if pass_pre_conv > 0:
            print(f"  Convergence failure rate: {conv_fail/pass_pre_conv:.1%}")


if __name__ == "__main__":
    # First: analyze valid n=4 systems to understand what makes them work
    print("### Analyzing valid n=4 3CB systems ###")
    analyze_valid_n4_systems()

    # Privilege persistence at n=5
    print("\n\n### Privilege persistence at n=5 ###")
    proc1_privilege_persistence_n5()

    # Phase transition
    print("\n\n### Convergence failure rate by n ###")
    count_convergence_failures_by_n()

    # 4CB impossibility
    print("\n\n### 4CB impossibility check ###")
    four_cb_check()
