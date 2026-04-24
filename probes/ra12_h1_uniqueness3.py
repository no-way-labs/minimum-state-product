#!/usr/bin/env python3
"""
RA12 Part 3: Understanding single-priv non-good configs on tails

Puzzle: configs like (0,0,0,0,0) in Sol3 n=5 have exactly 1 privileged proc,
their successor IS in the good cycle, yet they're NOT in good_set.

Explanation: good_set = the cycle itself (not cycle + tails).
The verifier finds the maximal closed subset of single_priv configs.
A "tail" config c maps into the cycle but nothing maps TO c from within
the closed set. So c is removed during the iterative closure.

Wait — that's wrong. The verifier starts with ALL single-priv configs
and removes those whose successor leaves the set. If c's successor is
in the cycle (which is in the closed set), then c should stay.

Unless: c's successor is in single_priv but NOT in the cycle, and that
intermediate config gets removed.

Let me trace through the verifier logic carefully.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import verify_system, privileged_set, apply_move


def build_sol3(n):
    ms = [3] * n
    def f_bottom(L, S, R):
        if (S + 1) % 3 == R: return (S - 1) % 3
        return S
    def f_top(L, S, R):
        if L == R and (L + 1) % 3 != S: return (L + 1) % 3
        return S
    def f_middle(L, S, R):
        if (S + 1) % 3 == L: return L
        if (S + 1) % 3 == R: return R
        return S
    fs = [f_bottom] + [f_middle] * (n - 2) + [f_top]
    return ms, fs


def build_cup2(n):
    ms = [2] + [3] * (n - 2) + [2]
    T_bot = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
    T_low = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
    T_mid = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,(2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):0,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2}
    T_high = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,(2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
    T_top = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}
    def get_table(pos):
        if pos == 0: return T_bot
        if pos == 1: return T_low
        if pos == n-2: return T_high
        if pos == n-1: return T_top
        return T_mid
    fs = []
    for p in range(n):
        tbl = get_table(p)
        def make_f(t): return lambda L,S,R: t[(L,S,R)]
        fs.append(make_f(tbl))
    return ms, fs


def trace_good_set_construction(ms, fs, label):
    """Trace the verifier's good_set construction to understand
    why tail configs are excluded."""
    n = len(ms)
    configs = list(cartesian(*(range(m) for m in ms)))

    # Single-priv configs
    single_priv = set()
    for c in configs:
        priv = privileged_set(c, fs, ms)
        if len(priv) == 1:
            single_priv.add(c)

    # Build successor map on single_priv
    succ = {}
    for c in single_priv:
        priv = privileged_set(c, fs, ms)
        p = priv[0]
        s = apply_move(c, p, fs, ms)
        succ[c] = s

    # Iterative closure
    good_candidates = set(single_priv)
    removed_rounds = []
    round_num = 0
    while True:
        to_remove = set()
        for c in good_candidates:
            if succ[c] not in good_candidates:
                to_remove.add(c)
        if not to_remove:
            break
        removed_rounds.append(to_remove)
        good_candidates -= to_remove
        round_num += 1

    # What does the actual verifier return?
    result = verify_system(ms, fs)
    cycle = result['cycle']
    good_set = set(cycle)

    print(f"\n{'='*60}")
    print(f"{label}")
    print(f"  Total configs: {len(configs)}")
    print(f"  Single-priv configs: {len(single_priv)}")
    print(f"  After closure: {len(good_candidates)} candidates")
    print(f"  Verifier good_set (cycle only): {len(good_set)}")
    print(f"  Removal rounds: {len(removed_rounds)}")

    # Check: are good_candidates == good_set?
    diff = good_candidates - good_set
    print(f"  Candidates NOT in cycle: {len(diff)}")
    if diff:
        print(f"  These are tail configs that survived closure!")
        for c in sorted(diff)[:5]:
            s = succ[c]
            print(f"    {c} -> {s}, in cycle: {s in good_set}, in candidates: {s in good_candidates}")

    # The verifier's good_set includes tails (via BFS backwards from cycle)
    # But the CYCLE is what we care about for H-1 uniqueness
    # Let me check: does the verifier's "good" include tails?
    full_good = result.get('good_configs', set())
    print(f"  Verifier's full good_configs: {len(full_good)}")
    if full_good:
        tails = full_good - good_set
        print(f"  Tail configs (good but not on cycle): {len(tails)}")

    # KEY: The single-priv "violations" we found are tail configs.
    # They ARE good configs (the verifier includes them).
    # The verifier's good_set = cycle + tails.
    # So these aren't really violations of forcedSucc_nonGood!

    # Let me re-check: are the "single-priv non-good" configs actually
    # in the verifier's FULL good set?
    all_cfgs = list(cartesian(*(range(m) for m in ms)))
    truly_non_good = [c for c in all_cfgs if c not in full_good] if full_good else []

    sp_truly_ng = []
    for c in truly_non_good:
        priv = privileged_set(c, fs, ms)
        if len(priv) == 1:
            sp_truly_ng.append(c)

    print(f"\n  Single-priv configs that are TRULY non-good: {len(sp_truly_ng)}")
    if sp_truly_ng:
        for c in sp_truly_ng[:5]:
            priv = privileged_set(c, fs, ms)
            moved = apply_move(c, priv[0], fs, ms)
            print(f"    {c} -> {moved}, moved in good: {moved in full_good}")

    # Now: re-check forcedSucc_nonGood with FULL good set
    violations = []
    for c in truly_non_good:
        priv = privileged_set(c, fs, ms)
        for p in priv:
            moved = apply_move(c, p, fs, ms)
            if moved in full_good:
                violations.append((c, p, moved, priv))

    print(f"\n  forcedSucc_nonGood violations (using FULL good set): {len(violations)}")
    if violations:
        sp_v = [v for v in violations if len(v[3]) == 1]
        mp_v = [v for v in violations if len(v[3]) > 1]
        print(f"    Single-priv: {len(sp_v)}")
        print(f"    Multi-priv: {len(mp_v)}")
        if sp_v:
            print(f"    *** TRUE single-priv violations: ***")
            for c, p, moved, priv in sp_v[:5]:
                print(f"      {c}, priv={priv}, move={moved}")
        if mp_v:
            print(f"    Sample multi-priv violations:")
            for c, p, moved, priv in mp_v[:5]:
                print(f"      {c}, priv={priv}, fire {p} -> {moved}")
    else:
        print(f"    forcedSucc_nonGood HOLDS with full good set!")


# Test
trace_good_set_construction(*build_sol3(5), "Sol3 n=5")
trace_good_set_construction(*build_cup2(5), "CUP-2 n=5")
trace_good_set_construction(*build_cup2(7), "CUP-2 n=7")
trace_good_set_construction(*build_cup2(9), "CUP-2 n=9")

print("\n" + "=" * 70)
print("CONCLUSION")
print("=" * 70)
print("""
The verifier's 'good_configs' includes BOTH cycle configs AND tail configs.
Tail configs are single-priv configs whose deterministic successor chain
leads into the cycle. They ARE good configs.

Previous analysis used only cycle configs as "good", missing the tails.
This created false "single-priv violations."

With the FULL good set (cycle + tails):
- Are there still forcedSucc_nonGood violations?
- If so, they must be multi-priv (since single-priv configs whose
  successor is good are automatically in the good set).
""")
