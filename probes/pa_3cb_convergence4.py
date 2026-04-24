#!/usr/bin/env python3
"""PA: 3CB Convergence Failure — Part 4.

KEY FINDING from Part 3:
- At n=4 (ms=2,2,2,3, P=24): 28 valid systems exist!
- At n=5 (ms=2,2,2,3,3, P=72): ZERO systems pass closure+fairness.
  The failure is NOT convergence -- it's that no valid good cycle exists.
- At n=6: same -- zero pass closure+fairness.

This means the 3CB obstruction at sub-threshold n>=5 is MORE fundamental
than "bad SCCs exist" -- it's "no valid good cycle can be constructed."

This script investigates WHY closure fails and whether this is a
counting/pigeonhole argument.

HYPOTHESIS: With 3CB and ms=(2,2,2,3,...,3):
- P_total = 8 * 3^(n-3)
- Good cycle length = L, with each proc firing m_i times.
- Minimum L = sum(ms) = 3n - 3.
- For closure: each good config's successor (fire unique priv proc) must also be good.
- The binary procs create constraints: when a binary proc fires (toggling 1 bit),
  the successor config must have exactly 1 privileged proc.
- With 3 consecutive binary, the toggling creates complex constraint propagation.

NOTE: The failure mode is entry conflict (EC): in the good cycle, the mover
word (sequence of which proc fires) imposes constraints on transition functions
that are unsatisfiable. This is the SAME mechanism as the shadow/EC proof
in the main paper. The 3CB convergence failure is a CONSEQUENCE of EC, not
a separate mechanism.

Wait -- but the task asks specifically about convergence failure, not EC.
Let me reconsider. The RA data says "ALL 768 constructions produce 384-528
recurrent bad states." This implies some constructions DO pass closure+fairness
but fail convergence. So at n=8 with ms=(2,2,2,3,3,3,3,4), P=2592, some
systems have valid good cycles but bad SCCs.

The difference: ms=(2,2,2,3,...,3) with P = 8*3^(n-3) may fail at the
closure level. But ms=(2,2,2,3,...,3,4) with P = 8*4*3^(n-4) = 32*3^(n-4)
might pass closure but fail convergence.

Let me check this hypothesis.
"""

import itertools
from collections import defaultdict, deque
from math import prod
import sys


def check_system(configs, fs, ms, n):
    """Check all 5 Dijkstra properties."""
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
                'good': good, 'bad': bad}

    good = set(fair_cycle)
    bad = set(configs) - good

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
            'good_count': len(good)}


def check_3cb_with_quaternary():
    """Check 3CB with a quaternary proc: ms=(2,2,2,...,4) at various n.

    At n=5: ms=(2,2,2,3,4), P=96 = M_5. This IS the minimum!
    So a valid system MUST exist.

    At n=6: ms=(2,2,2,3,3,4), P=288. Threshold = 324. Sub-threshold.
    M_6 = 32*3^2 = 288. So this IS M_6!

    At n=7: ms=(2,2,2,3,3,3,4), P=864 = M_7. Valid system exists.

    At n=8: ms=(2,2,2,3,3,3,3,4), P=2592 = M_8. Task says ALL fail!

    Let me verify n=5 and n=6 to see if valid 3CB systems exist at the
    minimum product.
    """
    print(f"{'='*60}")
    print(f"3CB WITH QUATERNARY PROCESSOR")
    print(f"{'='*60}")

    for n, ms_test in [
        (5, [2,2,2,3,4]),    # P=96 = M_5
        (5, [2,2,2,4,3]),    # rotation
        (6, [2,2,2,3,3,4]),  # P=288 = M_6
        (6, [2,2,2,3,4,3]),  # rotation
        (7, [2,2,2,3,3,3,4]),  # P=864 = M_7
    ]:
        P = prod(ms_test)
        threshold = 4 * 3**(n-2)
        configs = list(itertools.product(*(range(m) for m in ms_test)))

        print(f"\nn={n}, ms={ms_test}, P={P}")
        print(f"  Threshold: {threshold}, P/threshold={P/threshold:.4f}")

        # Try comprehensive rules
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

        def make_ternary_rules():
            return [
                ("L!=S,inc", lambda L, S, R: (S+1) % 3 if L != S else S),
                ("L!=S,dec", lambda L, S, R: (S-1) % 3 if L != S else S),
                ("S!=R,inc", lambda L, S, R: (S+1) % 3 if S != R else S),
                ("S!=R,dec", lambda L, S, R: (S-1) % 3 if S != R else S),
            ]

        def make_quaternary_rules():
            return [
                ("L!=S,inc", lambda L, S, R: (S+1) % 4 if L != S else S),
                ("L!=S,dec", lambda L, S, R: (S-1) % 4 if L != S else S),
                ("S!=R,inc", lambda L, S, R: (S+1) % 4 if S != R else S),
                ("S!=R,dec", lambda L, S, R: (S-1) % 4 if S != R else S),
                ("L%2!=S%2,inc", lambda L, S, R: (S+1) % 4 if L % 2 != S % 2 else S),
            ]

        valid_count = 0
        total = 0
        failure_reasons = defaultdict(int)

        # Build proc-level rule lists
        proc_rules = []
        for i in range(n):
            if ms_test[i] == 2:
                proc_rules.append(binary_rules)
            elif ms_test[i] == 3:
                proc_rules.append(make_ternary_rules())
            elif ms_test[i] == 4:
                proc_rules.append(make_quaternary_rules())

        # Enumerate all combinations (up to limit)
        total_combos = prod(len(r) for r in proc_rules)
        print(f"  Total rule combos: {total_combos}")
        if total_combos > 10**7:
            print(f"  Too many, sampling...")
            continue

        for combo in itertools.product(*proc_rules):
            names = [c[0] for c in combo]
            funcs = [c[1] for c in combo]
            total += 1

            result = check_system(configs, funcs, ms_test, n)
            if result['valid']:
                valid_count += 1
                if valid_count <= 5:
                    print(f"  VALID! {names}, good={result['good_count']}")
            elif result['valid'] is False:
                failure_reasons[result['reason']] += 1

        print(f"  Total: {total}, Valid: {valid_count}")
        print(f"  Failures: {dict(failure_reasons)}")

        # If valid, analyze one
        if valid_count > 0:
            # Find and analyze a valid system
            for combo in itertools.product(*proc_rules):
                funcs = [c[1] for c in combo]
                result = check_system(configs, funcs, ms_test, n)
                if result['valid']:
                    analyze_drainage(configs, funcs, ms_test, n, result)
                    break


def analyze_drainage(configs, fs, ms, n, result):
    """Analyze the drainage structure of a valid system."""
    priv_map = result['priv_map']
    good = result['good']
    bad = result['bad']

    print(f"\n  Drainage analysis:")
    print(f"    Good configs: {len(good)}")
    print(f"    Bad configs: {len(bad)}")

    # Count bad configs by number of privileged procs
    priv_count_dist = defaultdict(int)
    for c in bad:
        priv_count_dist[len(priv_map[c])] += 1
    print(f"    Bad config priv count dist: {dict(sorted(priv_count_dist.items()))}")

    # Proc 1 privilege analysis
    bad_with_p1 = {c for c in bad if 1 in priv_map[c]}
    print(f"    Bad with proc 1 priv: {len(bad_with_p1)}/{len(bad)}")

    # Drainage depth: BFS from good
    depth = {}
    queue = deque()
    for c in bad:
        for p in priv_map[c]:
            nc = list(c)
            nc[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
            nc = tuple(nc)
            if nc in good and c not in depth:
                depth[c] = 1
                queue.append(c)

    bad_pred = defaultdict(set)
    for c in bad:
        for p in priv_map[c]:
            nc = list(c)
            nc[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
            nc = tuple(nc)
            if nc in bad:
                bad_pred[nc].add(c)

    while queue:
        c = queue.popleft()
        for pred in bad_pred[c]:
            if pred not in depth:
                depth[pred] = depth[c] + 1
                queue.append(pred)

    max_depth = max(depth.values()) if depth else 0
    depth_dist = defaultdict(int)
    for d in depth.values():
        depth_dist[d] += 1
    print(f"    Max drainage depth: {max_depth}")
    print(f"    Drainage depth dist: {dict(sorted(depth_dist.items()))}")


def the_real_question():
    """The REAL question: at n=8, ms=(2,2,2,3,3,3,3,4), P=2592=M_8,
    does ANY 3CB system work?

    The task says ALL 768 constructions fail with bad SCCs.
    But "768 constructions" might be a specific rule-based subset.

    Actually, the known M_8 witness has ms=(2,2,2,3,3,3,3,4) or rotation.
    But the valid system might NOT have 3 CONSECUTIVE binary.
    The ms could be (2,3,2,3,2,3,3,4) = non-consecutive binary.

    Key insight from the main paper:
    - For n<=8: M_n = 32*3^(n-4), achieved by ms with 3 binary + 1 quaternary + rest ternary.
    - The binary procs may or may not be consecutive.
    - If consecutive: the system might not be valid (EC/shadow blocks it).
    - If non-consecutive: the system IS valid (the known witnesses).

    So the question is: does 3CB SPECIFICALLY block validity, even when
    the product is at M_n?

    For n=5: M_5 = 96, achieved by ms=(2,2,2,3,4).
    This HAS 3CB. So either:
    (a) The valid ms=(2,2,2,3,4) system doesn't exist (but M_5=96 is proved), OR
    (b) The valid ms=(2,2,2,3,4) system exists but with non-Dijkstra rules, OR
    (c) My rule enumeration is incomplete.

    Actually wait: M_5=96 is the MINIMUM product. The achieving ms could be
    (2,2,2,3,4) or any permutation. But for n=5 with 3 binary, there are only
    2 non-binary procs. If 3 binary are consecutive at {0,1,2}, the non-binary
    are at {3,4}. If non-consecutive, e.g., (2,3,2,3,2), that's also possible.

    The key result from the paper is:
    - 3 consecutive binary at sub-threshold product is blocked by entry conflict.
    - The proof uses shadow cycles, EC, palindromic EC, etc.
    - This is about the GOOD CYCLE, not about convergence specifically.

    So: the 3CB impossibility is that NO valid good cycle exists.
    This is stronger than "convergence fails" -- there's no system to begin with.
    """
    pass


def verify_m5_witness():
    """Verify the M_5 = 96 witness.

    The known valid system for n=5, ms=(2,2,2,3,4), P=96.
    From the CUP/CLB infrastructure.

    Actually, let me check: is the known M_5 witness at ms=(2,2,2,3,4)
    or at some other configuration?
    """
    # From the verifier: Dijkstra Solution 1 has ms=(2,3,...,3) or rotations.
    # M_5 = 96 = 2^5 * 3 = 32*3 = 96.
    # Wait: 32*3^(5-4) = 32*3 = 96. Yes.
    # ms must have product 96 = 2^5 * 3.
    # With n=5 procs, product = m_0*m_1*m_2*m_3*m_4 = 96.
    # Possibilities: (2,2,2,3,4), (2,2,2,4,3), (2,2,3,2,4), etc.
    # (2,2,2,2,6), (2,2,4,3,2), (3,2,2,2,4), (4,2,2,2,3)...

    # The M_4=24 correction says: ms=(2,2,2,3) with valid system at n=4.
    # For n=5, M_5=96. Let me check if the verifier has this.

    print(f"\n{'='*60}")
    print(f"M_5 = 96 WITNESS VERIFICATION")
    print(f"{'='*60}")

    # Try ms=(2,2,2,3,4) with more comprehensive rules
    n = 5
    ms = [2, 2, 2, 3, 4]
    P = prod(ms)
    configs = list(itertools.product(*(range(m) for m in ms)))

    print(f"n={n}, ms={ms}, P={P}")
    print(f"Configs: {len(configs)}")

    # From CUP-2: the valid construction uses specific lookup tables.
    # For ms=(2,3,...,3,2): T_bot, T_low, T_mid, T_high, T_top.
    # But our ms is different: (2,2,2,3,4).
    # Let me try a broader search.

    # Approach: for the quaternary proc (proc 4), enumerate ALL functions
    # that could work. Context: (c[3], c[4], c[0]) in {0,1,2}*{0,1,2,3}*{0,1}.
    # 3*4*2 = 24 contexts. Output {0,1,2,3}. 4^24 = too many.

    # Instead: try more rule types.
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

    quaternary_rules = [
        ("L!=S,inc", lambda L, S, R: (S+1) % 4 if L != S else S),
        ("L!=S,dec", lambda L, S, R: (S-1) % 4 if L != S else S),
        ("S!=R,inc", lambda L, S, R: (S+1) % 4 if S != R else S),
        ("S!=R,dec", lambda L, S, R: (S-1) % 4 if S != R else S),
        ("L%2!=S%2,inc", lambda L, S, R: (S+1) % 4 if L % 2 != S % 2 else S),
        ("L%3!=S,inc", lambda L, S, R: (S+1) % 4 if L % 3 != S % 3 else S),
        # More creative rules
        ("L!=S&S!=R,inc", lambda L, S, R: (S+1) % 4 if L != S and S != R else S),
        ("L!=S|S!=R,inc", lambda L, S, R: (S+1) % 4 if L != S or S != R else S),
        ("L+R!=2S,inc", lambda L, S, R: (S+1) % 4 if (L + R) % 4 != (2*S) % 4 else S),
        ("L==S,inc", lambda L, S, R: (S+1) % 4 if L == S else S),
        ("S==R,inc", lambda L, S, R: (S+1) % 4 if S == R else S),
    ]

    proc_rules = [binary_rules, binary_rules, binary_rules, ternary_rules, quaternary_rules]
    total_combos = prod(len(r) for r in proc_rules)
    print(f"Total rule combos: {total_combos}")

    valid_count = 0
    total = 0
    failure_reasons = defaultdict(int)

    for combo in itertools.product(*proc_rules):
        names = [c[0] for c in combo]
        funcs = [c[1] for c in combo]
        total += 1

        result = check_system(configs, funcs, ms, n)
        if result['valid']:
            valid_count += 1
            print(f"  VALID! {names}, good={result['good_count']}")
            if valid_count <= 2:
                analyze_drainage(configs, funcs, ms, n, result)
        else:
            failure_reasons[result['reason']] += 1

    print(f"\nTotal: {total}, Valid: {valid_count}")
    print(f"Failures: {dict(failure_reasons)}")


def brute_force_n5_2224():
    """Try ms=(2,2,2,4) at n=4 (P=32) and ms=(2,2,2,4,3) at n=5 (P=96).

    Since we found valid 3CB at n=4, let's see if adding a quaternary
    makes the system work at n=5.

    For n=4, ms=(2,2,2,4): P=32, threshold=36. Sub-threshold.
    Can we find a valid system?
    """
    print(f"\n{'='*60}")
    print(f"n=4 with quaternary: ms=(2,2,2,4)")
    print(f"{'='*60}")

    n = 4
    ms = [2, 2, 2, 4]
    P = prod(ms)
    configs = list(itertools.product(*(range(m) for m in ms)))

    print(f"P={P}, threshold={4*3**(n-2)}")

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

    quaternary_rules = [
        ("L!=S,inc", lambda L, S, R: (S+1) % 4 if L != S else S),
        ("L!=S,dec", lambda L, S, R: (S-1) % 4 if L != S else S),
        ("S!=R,inc", lambda L, S, R: (S+1) % 4 if S != R else S),
        ("S!=R,dec", lambda L, S, R: (S-1) % 4 if S != R else S),
        ("L==S,inc", lambda L, S, R: (S+1) % 4 if L == S else S),
        ("L%2!=S%2,inc", lambda L, S, R: (S+1) % 4 if L % 2 != S % 2 else S),
    ]

    valid_count = 0
    total = 0
    failure_reasons = defaultdict(int)

    for combo in itertools.product(binary_rules, binary_rules, binary_rules, quaternary_rules):
        names = [c[0] for c in combo]
        funcs = [c[1] for c in combo]
        total += 1

        result = check_system(configs, funcs, ms, n)
        if result['valid']:
            valid_count += 1
            if valid_count <= 3:
                print(f"  VALID! {names}, good={result['good_count']}")
        else:
            failure_reasons[result['reason']] += 1

    print(f"Total: {total}, Valid: {valid_count}")
    print(f"Failures: {dict(failure_reasons)}")


def understand_closure_failure():
    """Deep dive: WHY does closure fail at n=5 with ms=(2,2,2,3,3)?

    Closure means: from each good config (unique priv proc), firing that proc
    leads to another good config.

    With Dijkstra L!=S rules: proc i priv when c[i-1] != c[i].
    Fire proc i: c[i] -> 1-c[i] (binary) or (c[i]+1)%3 (ternary).

    After firing binary proc 1 (c[0]!=c[1]): c[1] -> 1-c[1].
    New config has c[1]' = 1-c[1]. Now c[0] = c[1]' (since c[0] != c[1] and binary).
    So proc 1 is NOT privileged in new config (c[0] == c[1]'). Good.
    But proc 2: context (c[1]', c[2], c[3]). Is proc 2 privileged?
    c[1]' changed, so proc 2's privilege status may have changed.
    If c[1]' != c[2]: proc 2 is privileged.
    If c[1]' == c[2]: proc 2 is not privileged.
    If the new config has exactly 1 privileged proc: closure holds for this step.
    If 0 or 2+: closure fails.

    The issue: firing one binary proc creates a ripple effect through
    neighboring binary procs.
    """
    n = 5
    ms = [2, 2, 2, 3, 3]
    P = prod(ms)
    configs = list(itertools.product(*(range(m) for m in ms)))

    print(f"\n{'='*60}")
    print(f"CLOSURE FAILURE ANALYSIS: n={n}, ms={ms}")
    print(f"{'='*60}")

    # Use Dijkstra L!=S for all
    def f_binary(L, S, R):
        return (1-S) if L != S else S

    def f_ternary(L, S, R):
        return (S+1) % 3 if L != S else S

    fs = [f_binary, f_binary, f_binary, f_ternary, f_ternary]

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
    dead = {c for c in configs if len(priv_map[c]) == 0}

    print(f"Good: {len(good)}, Bad: {len(bad)}, Dead: {len(dead)}")

    # Build succession graph on good configs
    succ = {}
    closure_fail = 0
    for c in good:
        p = priv_map[c][0]
        nc = list(c)
        nc[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
        nc = tuple(nc)
        succ[c] = nc
        if nc not in good:
            closure_fail += 1
            if closure_fail <= 10:
                print(f"  Closure fail: {c} (priv={p}) -> {nc} (priv={priv_map.get(nc, ['DEAD'])})")

    print(f"Closure failures: {closure_fail} out of {len(good)}")

    # Analyze: which proc fires cause closure failures?
    fire_proc_dist = defaultdict(lambda: [0, 0])  # [pass, fail]
    for c in good:
        p = priv_map[c][0]
        nc = succ[c]
        if nc in good:
            fire_proc_dist[p][0] += 1
        else:
            fire_proc_dist[p][1] += 1

    print(f"\nBy proc fired:")
    for p in sorted(fire_proc_dist.keys()):
        passes, fails = fire_proc_dist[p]
        print(f"  Proc {p}: {passes} pass, {fails} fail")

    # Now try the rules that worked at n=4: (L==S, L!=S, L!=S, Dijkstra)
    print(f"\n--- Trying n=4 winning rules at n=5 ---")

    def f0_eq(L, S, R):
        return (1-S) if L == S else S

    fs2 = [f0_eq, f_binary, f_binary, f_ternary, f_ternary]

    priv_map2 = {}
    for c in configs:
        priv = []
        for i in range(n):
            L = c[(i-1) % n]
            S = c[i]
            R = c[(i+1) % n]
            if fs2[i](L, S, R) != S:
                priv.append(i)
        priv_map2[c] = priv

    good2 = {c for c in configs if len(priv_map2[c]) == 1}
    bad2 = {c for c in configs if len(priv_map2[c]) >= 2}
    dead2 = {c for c in configs if len(priv_map2[c]) == 0}

    print(f"Good: {len(good2)}, Bad: {len(bad2)}, Dead: {len(dead2)}")

    if dead2:
        print(f"Dead configs exist -- system not viable")
        for c in sorted(dead2):
            print(f"  Dead: {c}")
        return

    closure_fail2 = 0
    for c in good2:
        p = priv_map2[c][0]
        nc = list(c)
        nc[p] = fs2[p](c[(p-1)%n], c[p], c[(p+1)%n])
        nc = tuple(nc)
        if nc not in good2:
            closure_fail2 += 1
            if closure_fail2 <= 5:
                print(f"  Closure fail: {c} (priv={p}) -> {tuple(nc)} (priv={priv_map2.get(tuple(nc), ['?'])})")

    print(f"Closure failures: {closure_fail2}/{len(good2)}")


if __name__ == "__main__":
    # Understand why closure fails at n=5 with all-ternary rest
    understand_closure_failure()

    # Try 3CB with quaternary
    check_3cb_with_quaternary()

    # M_5 witness
    verify_m5_witness()
