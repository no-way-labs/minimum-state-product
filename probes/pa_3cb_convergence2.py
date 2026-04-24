#!/usr/bin/env python3
"""PA: 3CB Convergence Failure — Deep Investigation.

Part 2: Direct system construction and verification at small n.
Focus on understanding EXACTLY what fails and why.
"""

import itertools
from collections import defaultdict, deque
from math import prod

def build_all_systems_n4():
    """n=4, ms=(2,2,2,3), P=24. Small enough to try everything.

    Proc 0: ctx (c[3], c[0], c[1]) in {0,1,2}*{0,1}*{0,1} = 12. Output {0,1}. 2^12 = 4096.
    Proc 1: ctx (c[0], c[1], c[2]) in {0,1}^3 = 8. Output {0,1}. 2^8 = 256.
    Proc 2: ctx (c[1], c[2], c[3]) in {0,1}*{0,1}*{0,1,2} = 12. Output {0,1}. 2^12 = 4096.
    Proc 3: ctx (c[2], c[3], c[0]) in {0,1}*{0,1,2}*{0,1} = 12. Output {0,1,2}. 3^12 = 531441.

    Total: 4096 * 256 * 4096 * 531441 ≈ 2.28 * 10^15. Way too many.

    Let's use the existing verifier approach: build a smaller space.
    """
    n = 4
    ms = [2, 2, 2, 3]
    P = prod(ms)  # 24
    configs = list(itertools.product(*(range(m) for m in ms)))

    print(f"n={n}, ms={ms}, P={P}")
    print(f"Total configs: {len(configs)}")

    # For proc 3 (ternary), use Dijkstra-style: priv when L!=S
    # Try both incrementing and decrementing for proc 3
    def f3_inc(L, S, R):
        return (S+1) % 3 if L != S else S

    def f3_dec(L, S, R):
        return (S-1) % 3 if L != S else S

    # For proc 3, also try: priv when S!=R
    def f3_right(L, S, R):
        return (S+1) % 3 if S != R else S

    f3_options = [("inc_L!=S", f3_inc), ("dec_L!=S", f3_dec), ("inc_S!=R", f3_right)]

    # For procs 0, 1, 2 (all binary), enumerate ALL 256 functions each...
    # Proc 0: 12 contexts -> 2^12 = 4096 too many.
    # Let's try systematic sampling.

    # Better approach: enumerate all "L!=S" and "S!=R" type rules for binary procs.
    # For binary proc i with context (L, S, R):
    # - L in range(ms[(i-1)%n]), S in {0,1}, R in range(ms[(i+1)%n])
    # Binary output: f(L,S,R) in {0,1}.
    # Privileged iff f(L,S,R) != S, i.e., f(L,S,R) = 1-S.

    # Simple rules for binary proc:
    # 1. Dijkstra left: priv when L != S
    # 2. Dijkstra right: priv when S != R
    # 3. Toggle: always priv (f = 1-S)
    # 4. Identity: never priv (f = S)
    # 5. L-match: f = L%2 (priv when L%2 != S)
    # 6. R-match: f = R%2 (priv when R%2 != S)

    binary_rules = {}

    def make_rule(name, priv_cond):
        def f(L, S, R):
            if priv_cond(L, S, R):
                return 1 - S
            return S
        return (name, f)

    b_rules = [
        make_rule("L!=S", lambda L, S, R: L != S),
        make_rule("S!=R", lambda L, S, R: S != R),
        make_rule("L!=R", lambda L, S, R: L != R),
        make_rule("L==S", lambda L, S, R: L == S),
        make_rule("S==R", lambda L, S, R: S == R),
        make_rule("toggle", lambda L, S, R: True),
        make_rule("L%2!=S", lambda L, S, R: L % 2 != S),
        make_rule("R%2!=S", lambda L, S, R: R % 2 != S),
    ]

    valid_count = 0
    total = 0
    failure_reasons = defaultdict(int)

    for f0_name, f0 in b_rules:
        for f1_name, f1 in b_rules:
            for f2_name, f2 in b_rules:
                for f3_name, f3 in f3_options:
                    fs = [f0, f1, f2, f3]
                    total += 1

                    result = check_system(configs, fs, ms, n)
                    if result['valid']:
                        valid_count += 1
                        print(f"  VALID: f0={f0_name}, f1={f1_name}, f2={f2_name}, f3={f3_name}")
                        print(f"    good={result['good_count']}, bad_sccs={result.get('bad_scc_size', 0)}")
                    else:
                        failure_reasons[result['reason']] += 1

    print(f"\nTotal tried: {total}")
    print(f"Valid: {valid_count}")
    print(f"Failure reasons: {dict(failure_reasons)}")
    return valid_count


def check_system(configs, fs, ms, n):
    """Check a system for all 5 Dijkstra properties."""
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

    # Liveness
    dead = [c for c in configs if len(priv_map[c]) == 0]
    if dead:
        return {'valid': False, 'reason': 'liveness'}

    # Good/bad
    good = {c for c in configs if len(priv_map[c]) == 1}
    bad = {c for c in configs if len(priv_map[c]) >= 2}

    if len(good) < n:  # need at least n good configs for fairness
        return {'valid': False, 'reason': 'too_few_good'}

    # Closure: good -> good under unique privileged fire
    succ = {}
    for c in good:
        p = priv_map[c][0]
        nc = list(c)
        nc[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
        nc = tuple(nc)
        succ[c] = nc

    # Check closure
    for c in good:
        if succ[c] not in good:
            return {'valid': False, 'reason': 'closure'}

    # Find cycles in good graph
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
        if c == start:
            cycles.append(path)
        elif c in path:
            idx = path.index(c)
            cycles.append(path[idx:])

    if not cycles:
        return {'valid': False, 'reason': 'no_good_cycle'}

    # Fairness: some cycle visits all procs
    fair_cycle = None
    for cycle in cycles:
        procs_visited = set()
        for c in cycle:
            procs_visited.add(priv_map[c][0])
        if len(procs_visited) == n:
            fair_cycle = cycle
            break

    if fair_cycle is None:
        return {'valid': False, 'reason': 'fairness'}

    # Use only the fair cycle as good configs
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
                if c not in can_reach_good:
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
        return {'valid': False, 'reason': 'convergence', 'bad_scc_size': len(stuck)}

    return {'valid': True, 'good_count': len(good), 'bad_scc_size': 0}


def exhaustive_binary_rules_n4():
    """Try ALL possible binary transition rules for procs 0, 1, 2 at n=4.

    For procs 0 and 2: each has some context with a ternary neighbor.
    Proc 0: ctx = (c[3], c[0], c[1]) where c[3] in {0,1,2}. 12 contexts.
    Proc 2: ctx = (c[1], c[2], c[3]) where c[3] in {0,1,2}. 12 contexts.

    For proc 1: ctx = (c[0], c[1], c[2]), all binary. 8 contexts.

    We need to enumerate more transition functions.
    For the BINARY procs, the key is which contexts are privileged.
    For proc 0: 12 contexts, privilege (yes/no) for each -> 2^12 = 4096.
    Too many. But we can use the (a,c) pair decomposition.

    For proc 0: context (L,S,R) with L in {0,1,2}, S in {0,1}, R in {0,1}.
    Group by (L,R): 6 pairs. For each (L,R):
    - Neither (L,0,R) nor (L,1,R) privileged: identity at this (L,R)
    - Only (L,0,R) privileged: always output 1 at this (L,R)
    - Only (L,1,R) privileged: always output 0 at this (L,R)
    - Both privileged: toggle at this (L,R)

    4^6 = 4096 functions. That's the same as 2^12.

    For proc 1: (L,R) has 4 pairs -> 4^4 = 256 functions.
    For proc 2: (L,R) in {0,1}*{0,1,2} = 6 pairs -> 4^6 = 4096 functions.

    Total for binary procs: 4096 * 256 * 4096 ≈ 4.3 * 10^9. Too many.

    Let me reduce further: for the ternary proc, fix to Dijkstra-style.
    Then try ALL 256 functions for proc 1, and sample for procs 0, 2.
    """
    pass


def investigate_why_n5_fails():
    """For n=5, ms=(2,2,2,3,3), try MANY transition functions and see what fails.

    Focus on: which property fails most? Liveness, closure, fairness, or convergence?
    """
    n = 5
    ms = [2, 2, 2, 3, 3]
    P = prod(ms)
    configs = list(itertools.product(*(range(m) for m in ms)))

    print(f"\n{'='*60}")
    print(f"WHY n=5 FAILS: ms={ms}, P={P}")
    print(f"{'='*60}")

    # Use Dijkstra for procs 3, 4
    def f_dijk(mi):
        def f(L, S, R):
            return (S+1) % mi if L != S else S
        return f

    f3 = f_dijk(3)
    f4 = f_dijk(3)

    # For proc 1: try all 256
    # For procs 0, 2: try a wider set of rules

    # For binary proc with ternary left neighbor:
    # Proc 0: (c[4], c[0], c[1]) where c[4] in {0,1,2}
    # Group by (c[4], c[1]): 6 pairs. 4^6 = 4096 functions.

    # For binary proc with ternary right neighbor:
    # Proc 2: (c[1], c[2], c[3]) where c[3] in {0,1,2}
    # Group by (c[1], c[3]): 6 pairs. 4^6 = 4096 functions.

    # Let's try ALL 256 for proc 1 and sample 100 each for procs 0, 2.
    import random
    random.seed(42)

    # Generate random binary functions for proc 0
    def random_binary_func(context_pairs, mi_self=2):
        """Generate a random binary transition function."""
        table = {}
        for L_R_pair in context_pairs:
            L, R = L_R_pair
            choice = random.randint(0, 3)
            if choice == 0:
                table[(L, 0, R)] = 0
                table[(L, 1, R)] = 1
            elif choice == 1:
                table[(L, 0, R)] = 1
                table[(L, 1, R)] = 1
            elif choice == 2:
                table[(L, 0, R)] = 0
                table[(L, 1, R)] = 0
            else:
                table[(L, 0, R)] = 1
                table[(L, 1, R)] = 0
        def f(L, S, R):
            return table[(L, S, R)]
        return f

    # Context pairs for proc 0: (c[4], c[1]) with c[4] in {0,1,2}, c[1] in {0,1}
    p0_pairs = [(L, R) for L in range(3) for R in range(2)]
    # Context pairs for proc 2: (c[1], c[3]) with c[1] in {0,1}, c[3] in {0,1,2}
    p2_pairs = [(L, R) for L in range(2) for R in range(3)]

    # Also include the structured rules
    def make_structured(priv_cond):
        def f(L, S, R):
            return (1 - S) if priv_cond(L, S, R) else S
        return f

    struct_rules = [
        make_structured(lambda L, S, R: L != S),
        make_structured(lambda L, S, R: S != R),
        make_structured(lambda L, S, R: L != R),
        make_structured(lambda L, S, R: True),  # toggle
        make_structured(lambda L, S, R: L % 2 != S),
        make_structured(lambda L, S, R: R % 2 != S),
    ]

    # Generate proc 0 and proc 2 candidate functions
    p0_funcs = list(struct_rules)
    p2_funcs = list(struct_rules)

    # Add random functions
    for _ in range(200):
        p0_funcs.append(random_binary_func(p0_pairs))
        p2_funcs.append(random_binary_func(p2_pairs))

    failure_reasons = defaultdict(int)
    total = 0
    valid = 0
    convergence_fails = 0
    convergence_fail_details = []

    # Proc 1: all 256
    contexts_1 = [(a, b, c) for a in range(2) for b in range(2) for c in range(2)]

    for f0 in p0_funcs:
        for f1_bits in range(256):
            f1_table = {}
            for idx, ctx in enumerate(contexts_1):
                f1_table[ctx] = (f1_bits >> idx) & 1

            def f1(L, S, R, _t=f1_table):
                return _t[(L, S, R)]

            for f2 in p2_funcs:
                fs = [f0, f1, f2, f3, f4]
                total += 1

                result = check_system(configs, fs, ms, n)
                if result['valid']:
                    valid += 1
                    M = {ctx for ctx in contexts_1 if f1_table[ctx] != ctx[1]}
                    print(f"  VALID! |M|={len(M)}")
                elif result['reason'] == 'convergence':
                    convergence_fails += 1
                    if len(convergence_fail_details) < 10:
                        M = {ctx for ctx in contexts_1 if f1_table[ctx] != ctx[1]}
                        convergence_fail_details.append({
                            '|M|': len(M),
                            'bad_scc': result.get('bad_scc_size', 0),
                        })
                failure_reasons[result['reason']] += 1

                if total % 100000 == 0:
                    print(f"  Progress: {total} tried, {valid} valid, {convergence_fails} convergence fails")

    print(f"\nTotal tried: {total}")
    print(f"Valid: {valid}")
    print(f"Convergence fails: {convergence_fails}")
    print(f"Failure reasons: {dict(failure_reasons)}")
    if convergence_fail_details:
        print(f"Sample convergence failures: {convergence_fail_details[:5]}")


def investigate_n4_direct():
    """n=4, ms=(2,2,2,3), P=24. Try ALL binary proc functions with Dijkstra ternary.

    For proc 1: 256 functions.
    For procs 0 and 2: each has context size 12 (ternary neighbor).
    But we can decompose: for proc 0, context (c[3],c[0],c[1]).
    Group by (c[3], c[1]): 6 groups. 4^6 = 4096 functions.
    Same for proc 2: 4096 functions.

    Total: 4096 * 256 * 4096 ≈ 4.3 billion. Too many.

    Instead, enumerate ALL functions for proc 1 (256),
    and try ALL 4096 for proc 0, with a fixed proc 2 = Dijkstra.
    Then swap.
    """
    n = 4
    ms = [2, 2, 2, 3]
    P = prod(ms)  # 24
    configs = list(itertools.product(*(range(m) for m in ms)))

    print(f"\n{'='*60}")
    print(f"n=4 DIRECT: ms={ms}, P={P}")
    print(f"threshold={4*3**(n-2)}={4*9}=36, M_4=24")
    print(f"{'='*60}")

    # Proc 3 (ternary): Dijkstra
    def f3(L, S, R):
        return (S+1) % 3 if L != S else S

    # Proc 2: Dijkstra
    def f2_dijk(L, S, R):
        return (1-S) if L != S else S

    # Proc 0: enumerate all 4096 functions
    # Context: (c[3], c[0], c[1]) with c[3] in {0,1,2}, c[0],c[1] in {0,1}
    p0_contexts = [(L, S, R) for L in range(3) for S in range(2) for R in range(2)]
    # 12 contexts

    # Proc 1: enumerate all 256
    p1_contexts = [(a, b, c) for a in range(2) for b in range(2) for c in range(2)]

    failure_reasons = defaultdict(int)
    valid_count = 0
    total = 0

    for f0_bits in range(2**12):
        f0_table = {}
        for idx, ctx in enumerate(p0_contexts):
            f0_table[ctx] = (f0_bits >> idx) & 1

        def f0(L, S, R, _t=f0_table):
            return _t[(L, S, R)]

        for f1_bits in range(256):
            f1_table = {}
            for idx, ctx in enumerate(p1_contexts):
                f1_table[ctx] = (f1_bits >> idx) & 1

            def f1(L, S, R, _t=f1_table):
                return _t[(L, S, R)]

            fs = [f0, f1, f2_dijk, f3]
            total += 1

            result = check_system(configs, fs, ms, n)
            if result['valid']:
                valid_count += 1
                M = {ctx for ctx in p1_contexts if f1_table[ctx] != ctx[1]}
                M0 = {ctx for ctx in p0_contexts if f0_table[ctx] != ctx[1]}
                print(f"  VALID! f0 has |M0|={len(M0)}, f1 has |M|={len(M)}")
            failure_reasons[result['reason']] += 1

        if (f0_bits + 1) % 500 == 0:
            print(f"  Progress: f0_bits={f0_bits+1}/4096, valid={valid_count}")

    print(f"\nTotal: {total}, Valid: {valid_count}")
    print(f"Failures: {dict(failure_reasons)}")
    return valid_count


def quick_convergence_anatomy():
    """Quick check: at n=4 and n=5 with simple rules, what does convergence failure look like?

    Focus: find systems that pass liveness+closure+fairness but fail convergence.
    Analyze the bad SCCs.
    """
    for n, ms in [(4, [2,2,2,3]), (5, [2,2,2,3,3])]:
        P = prod(ms)
        configs = list(itertools.product(*(range(m) for m in ms)))

        print(f"\n{'='*60}")
        print(f"CONVERGENCE ANATOMY: n={n}, ms={ms}, P={P}")
        print(f"{'='*60}")

        # Simple Dijkstra rules for all procs
        def f_dijk_binary(L, S, R):
            return (1-S) if L != S else S

        def f_dijk_ternary(L, S, R):
            return (S+1) % 3 if L != S else S

        fs = []
        for i in range(n):
            if ms[i] == 2:
                fs.append(f_dijk_binary)
            else:
                fs.append(f_dijk_ternary)

        result = check_system(configs, fs, ms, n)
        print(f"All Dijkstra L!=S: {result['reason'] if not result['valid'] else 'VALID'}")
        if result.get('bad_scc_size'):
            print(f"  Bad SCC size: {result['bad_scc_size']}")

        # Analyze the SCC structure
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

        good = {c for c in configs if len(priv_map[c]) == 1}
        bad = {c for c in configs if len(priv_map[c]) >= 2}

        print(f"  Good configs: {len(good)}")
        print(f"  Bad configs: {len(bad)}")
        print(f"  Dead configs: {sum(1 for c in configs if len(priv_map[c]) == 0)}")

        if not good:
            print(f"  No good configs!")
            continue

        # Check closure
        closed = True
        for c in good:
            p = priv_map[c][0]
            nc = list(c)
            nc[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
            nc = tuple(nc)
            if nc not in good:
                closed = False
                break

        if not closed:
            print(f"  Closure fails!")
            continue

        # Check fairness
        visited_procs = set()
        start = next(iter(good))
        c = start
        cycle_len = 0
        for _ in range(len(good) + 1):
            p = priv_map[c][0]
            visited_procs.add(p)
            nc = list(c)
            nc[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
            c = tuple(nc)
            cycle_len += 1
            if c == start:
                break

        print(f"  Good cycle length: {cycle_len}")
        print(f"  Procs visited: {visited_procs}")

        if len(visited_procs) < n:
            print(f"  Fairness fails!")

        # Bad SCC analysis
        bad_succ = defaultdict(set)
        for c in bad:
            for p in priv_map[c]:
                nc = list(c)
                nc[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
                bad_succ[c].add(tuple(nc))

        # Find which bad configs have proc 1 privileged
        bad_with_p1 = {c for c in bad if 1 in priv_map[c]}
        print(f"  Bad configs with proc 1 privileged: {len(bad_with_p1)}")

        # Check if bad_with_p1 forms a closed set under far-proc fires
        for c in list(bad_with_p1)[:5]:
            far_succs = []
            for p in priv_map[c]:
                if p >= 3:  # far proc
                    nc = list(c)
                    nc[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
                    nc = tuple(nc)
                    far_succs.append((p, nc, 1 in priv_map.get(nc, [])))
            near_succs = []
            for p in priv_map[c]:
                if p in [0, 2]:  # near proc
                    nc = list(c)
                    nc[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
                    nc = tuple(nc)
                    near_succs.append((p, nc, 1 in priv_map.get(nc, [])))
            if far_succs or near_succs:
                print(f"  Config {c}: priv={priv_map[c]}")
                for p, nc, p1_priv in far_succs:
                    print(f"    Fire far proc {p} -> {nc}, p1_priv={p1_priv}, priv={priv_map.get(nc, [])}")
                for p, nc, p1_priv in near_succs:
                    print(f"    Fire near proc {p} -> {nc}, p1_priv={p1_priv}, priv={priv_map.get(nc, [])}")


def privilege_overlap_analysis():
    """Analyze how many configs have MULTIPLE binary procs privileged simultaneously.

    If procs 0 AND 1 are both privileged: bad config.
    If procs 0 AND 1 AND 2 are all privileged: very bad config.

    With Dijkstra L!=S rule for all binary procs:
    - Proc 0 privileged when c[n-1] != c[0]
    - Proc 1 privileged when c[0] != c[1]
    - Proc 2 privileged when c[1] != c[2]

    For binary c[0],c[1],c[2] in {0,1}^3:
    - c[0]!=c[1] AND c[1]!=c[2]: c[0]=c[2]!=c[1]. 2 patterns: (0,1,0), (1,0,1).
    - All three priv: c[n-1]!=c[0] AND c[0]!=c[1] AND c[1]!=c[2].
      c[0]=c[2]!=c[1], plus c[n-1]!=c[0].

    This means: for ANY choice of c[3],...,c[n-1], if we set the binary states to
    (0,1,0) or (1,0,1), AND the ternary neighbor c[n-1] != c[0], then ALL THREE
    binary procs are simultaneously privileged. Massive bad config production.
    """
    for n in [5, 7, 8, 9]:
        ms = [2, 2, 2] + [3] * (n - 3)
        P = prod(ms)
        P_rest = prod(ms[3:])

        # With Dijkstra L!=S for binary procs:
        # Configs with all 3 binary procs privileged:
        # Need c[n-1]!=c[0], c[0]!=c[1], c[1]!=c[2].
        # c[0],c[1],c[2] in {0,1}^3. Patterns with c[0]!=c[1] and c[1]!=c[2]:
        # (0,1,0) and (1,0,1).
        # For each: c[n-1] != c[0]. c[n-1] in {0,1,2} (ternary).
        # (0,1,0): c[n-1] != 0, so c[n-1] in {1,2}. 2 choices.
        # (1,0,1): c[n-1] != 1, so c[n-1] in {0,2}. 2 choices.
        # Total: 4 values of (c[n-1], c[0], c[1], c[2]).
        # For each: any assignment to c[3],...,c[n-2]. That's prod(ms[3:n-1]).
        # Wait: c[n-1] is already fixed (it's the ternary proc's state).
        # So the free variables are c[3],...,c[n-2].
        # P_inner = prod(ms[3:n-1]) = 3^(n-4) (for all-ternary).

        P_inner = 3**(n-4) if n > 4 else 1
        all3_priv = 4 * P_inner

        # Configs with procs 0 AND 1 privileged:
        # c[n-1] != c[0] AND c[0] != c[1].
        # c[0],c[1] in {0,1}^2 with c[0]!=c[1]: (0,1) and (1,0). 2 patterns.
        # c[n-1] != c[0]: 2 choices each. c[2]: free (2 choices).
        # Total: 2 * 2 * 2 * P_inner = 8 * P_inner? Wait...
        # (c[n-1],c[0],c[1]) with c[n-1]!=c[0] and c[0]!=c[1]:
        #   c[0]=0: c[1]=1, c[n-1] in {1,2}. 2 options.
        #   c[0]=1: c[1]=0, c[n-1] in {0,2}. 2 options.
        # c[2]: free, 2 options.
        # c[3],...,c[n-2]: P_inner options.
        # Total: 4 * 2 * P_inner = 8 * P_inner

        p01_priv = 8 * P_inner

        # Configs with proc 1 privileged only (no proc 0 or 2):
        # c[0]!=c[1], c[n-1]==c[0], c[1]==c[2].
        # c[0]!=c[1]: (0,1) or (1,0).
        # c[n-1]==c[0]: c[n-1] = c[0] (1 choice, but c[n-1] in {0,1,2}).
        #   c[0]=0: c[n-1]=0. c[0]=1: c[n-1]=1.
        # c[2]==c[1]: c[2] = c[1]. (1,0): c[2]=0. (0,1): c[2]=1.
        # Total: 2 * P_inner

        p1_only = 2 * P_inner

        print(f"\nn={n}, ms={ms}, P={P}")
        print(f"  P_inner={P_inner}, P_rest={P_rest}")
        print(f"  All 3 binary priv: {all3_priv} ({all3_priv/P*100:.1f}%)")
        print(f"  Procs 0+1 priv: {p01_priv} ({p01_priv/P*100:.1f}%)")
        print(f"  Proc 1 only priv: {p1_only} ({p1_only/P*100:.1f}%)")
        print(f"  Good cycle needs: {sum(ms)} configs, proc 1 fires 2 times")
        print(f"  Ratio bad_with_p1_priv / good_cycle: {(P_rest-2)/sum(ms):.1f}")


if __name__ == "__main__":
    print("PA: 3CB Convergence Failure — Deep Investigation")
    print("=" * 70)

    # Quick anatomy
    print("\n### Convergence Anatomy with Dijkstra rules ###")
    quick_convergence_anatomy()

    # Privilege overlap
    print("\n\n### Privilege Overlap Analysis ###")
    privilege_overlap_analysis()

    # n=4 direct construction
    print("\n\n### n=4 Direct Construction ###")
    build_all_systems_n4()
