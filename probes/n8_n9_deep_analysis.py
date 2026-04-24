#!/usr/bin/env python3
"""n8_n9_deep_analysis.py — Deep structural analysis of the n=8 vs n=9 phase transition.

KEY FINDING from initial analysis:
- P3 has context (2,3,4) = 24 slots.
  At n=8: CL=22, CL/ctx=0.917 < 1.0. Room to avoid collision.
  At n=9: CL=25, CL/ctx=1.042 > 1.0. PIGEONHOLE FORCES collision.

This means at n=9, EVERY good cycle (with incrementing transitions) must have
a context collision at P3. But collision != entry conflict. Let's check if the
collision is necessarily mover-vs-nonmover.

Also: at n=8, even though P3 is below 1.0, other procs are above.
The question is: can the system tolerate EC at some procs but not others?
No! EC at ANY proc kills the system. So the question is really:
is there ANY good cycle (any mover word, any transition mode) that avoids
EC at ALL procs simultaneously?

This script does:
1. Enumerate ALL valid mover words for small n (n=5..8) with the 3-binary+quat pattern
2. For each, check EC at every proc
3. Find which mover words are EC-free (if any)
4. Analyze the structural difference at n=8 vs n=9

The insight: it's not about one proc crossing 1.0.
It's about whether there exists ANY cycle avoiding EC everywhere simultaneously.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict
from math import prod

def enumerate_good_cycles_increment(n, ms, max_cycles=50000):
    """Enumerate good cycles with incrementing transitions.

    A good cycle starting from config c with mover word w = (p_0, ..., p_{CL-1}):
    - c_0 = c
    - c_{i+1} = c_i with c_i[p_i] incremented mod m_{p_i}
    - c_{CL} = c_0
    - Each proc p fires exactly m_p times (incrementing returns to start)
    - CL = sum(ms)

    We only need to enumerate mover words; the cycle is determined by (c_0, w).
    But c_0 is any valid starting config, and the cycle is the same up to rotation.
    Actually, for incrementing transitions, the cycle determined by mover word w
    starting from all-zeros gives a specific set of configs. Different starting configs
    just rotate the cycle.

    So we enumerate mover words and check EC for each.
    """
    CL = sum(ms)

    # A mover word is a permutation of [0]*m_0 + [1]*m_1 + ... + [n-1]*m_{n-1}
    # with CL = sum(ms) elements.
    # This is too many to enumerate for large n. For n=8, CL=22.
    # Number of mover words = CL! / (m_0! * m_1! * ... * m_{n-1}!)
    # For n=8: 22! / (2!*2!*2!*3!*4!*3!*3!*3!) = huge

    # Instead, let's use a smarter approach: check a SAMPLE of mover words,
    # including sweep-type and bounce-type patterns.
    return None  # Use specific cycle generators instead


def build_cycle_from_mover_word(n, ms, movers, start=None):
    """Build a cycle from a mover word starting from a given config."""
    if start is None:
        start = tuple([0] * n)
    config = list(start)
    cycle = [tuple(config)]
    for mv in movers:
        config = list(cycle[-1])
        config[mv] = (config[mv] + 1) % ms[mv]
        nc = tuple(config)
        cycle.append(nc)

    if cycle[-1] != cycle[0]:
        return None  # doesn't close
    return cycle[:-1]  # remove duplicate last


def check_entry_conflicts(n, ms, cycle, movers):
    """Check entry conflicts for a specific cycle."""
    CL = len(cycle)
    mover_ctx = defaultdict(set)
    nonmover_ctx = defaultdict(set)

    for idx in range(CL):
        c = cycle[idx]
        mv = movers[idx]
        for p in range(n):
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
            ctx = (L, S, R)
            if p == mv:
                mover_ctx[p].add(ctx)
            else:
                nonmover_ctx[p].add(ctx)

    conflicts = {}
    for p in range(n):
        overlap = mover_ctx[p] & nonmover_ctx[p]
        conflicts[p] = overlap

    total = sum(len(v) for v in conflicts.values())
    return conflicts, total


def generate_sweep_cycles(n, ms):
    """Generate sweep-type mover words: CW and CCW sweeps."""
    CL = sum(ms)
    # CW sweep: 0,1,2,...,n-1, repeated
    cw = []
    counts = [0] * n
    p = 0
    while len(cw) < CL:
        if counts[p] < ms[p]:
            cw.append(p)
            counts[p] += 1
        p = (p + 1) % n
        if all(counts[i] >= ms[i] for i in range(n)):
            break

    # CCW sweep: n-1,n-2,...,0, repeated
    ccw = []
    counts = [0] * n
    p = n - 1
    while len(ccw) < CL:
        if counts[p] < ms[p]:
            ccw.append(p)
            counts[p] += 1
        p = (p - 1) % n
        if all(counts[i] >= ms[i] for i in range(n)):
            break

    return [('CW_sweep', cw), ('CCW_sweep', ccw)]


def generate_bounce_cycles(n, ms):
    """Generate bounce-type mover words: up-down patterns."""
    CL = sum(ms)
    up_down = list(range(n)) + list(range(n-2, 0, -1))  # 0,1,...,n-1,n-2,...,1
    period = len(up_down)

    full = up_down * (CL // period + 2)
    # Build until we have CL movers with correct fire counts
    movers = []
    counts = [0] * n
    for mv in full:
        if counts[mv] < ms[mv]:
            movers.append(mv)
            counts[mv] += 1
        if len(movers) == CL:
            break

    return [('bounce', movers)]


def generate_interleaved_cycles(n, ms):
    """Generate cycles that interleave processors in various patterns."""
    CL = sum(ms)
    results = []

    # Pattern: fire each proc once in order, repeat
    for start in range(n):
        movers = []
        counts = [0] * n
        for _ in range(CL):
            for offset in range(n):
                p = (start + offset) % n
                if counts[p] < ms[p]:
                    movers.append(p)
                    counts[p] += 1
                    break
            if len(movers) >= CL:
                break
        if len(movers) == CL:
            results.append((f'interleave_start{start}', movers))

    # Pattern: fire binary procs first, then others
    binary_procs = [p for p in range(n) if ms[p] == 2]
    other_procs = [p for p in range(n) if ms[p] != 2]
    movers = []
    counts = [0] * n
    for _ in range(CL):
        fired = False
        for p in binary_procs + other_procs:
            if counts[p] < ms[p]:
                movers.append(p)
                counts[p] += 1
                fired = True
                break
        if not fired:
            break
    if len(movers) == CL:
        results.append(('binary_first', movers))

    return results


def generate_random_cycles(n, ms, num=200):
    """Generate random mover words."""
    import random
    CL = sum(ms)
    base = []
    for p in range(n):
        base.extend([p] * ms[p])
    assert len(base) == CL

    results = []
    seen = set()
    for _ in range(num):
        perm = list(base)
        random.shuffle(perm)
        key = tuple(perm)
        if key not in seen:
            seen.add(key)
            results.append(('random', perm))
    return results


def full_ec_analysis(n, ms, verbose=True):
    """Full entry conflict analysis across cycle types."""
    import random
    random.seed(42)

    CL = sum(ms)
    product_val = prod(ms)
    threshold = 4 * 3**(n-2)

    if verbose:
        print(f"\n{'='*70}")
        print(f"n={n}: ms={ms}, product={product_val}, threshold={threshold}")
        print(f"CL={CL}, sub-threshold={product_val < threshold}")
        print(f"{'='*70}")

    # Generate cycle types
    cycles_to_test = []
    cycles_to_test.extend(generate_sweep_cycles(n, ms))
    cycles_to_test.extend(generate_bounce_cycles(n, ms))
    cycles_to_test.extend(generate_interleaved_cycles(n, ms))
    cycles_to_test.extend(generate_random_cycles(n, ms, num=500))

    ec_free = 0
    ec_present = 0
    min_conflicts = float('inf')
    best_cycle_name = None

    per_proc_ec_free = defaultdict(int)  # proc -> count of cycles where this proc has no EC

    for name, movers in cycles_to_test:
        if len(movers) != CL:
            continue
        # Verify mover word is valid (correct fire counts)
        counts = [0] * n
        for mv in movers:
            counts[mv] += 1
        if any(counts[p] != ms[p] for p in range(n)):
            continue

        cycle = build_cycle_from_mover_word(n, ms, movers)
        if cycle is None:
            continue

        conflicts, total = check_entry_conflicts(n, ms, cycle, movers)

        if total == 0:
            ec_free += 1
        else:
            ec_present += 1

        if total < min_conflicts:
            min_conflicts = total
            best_cycle_name = name

        for p in range(n):
            if len(conflicts[p]) == 0:
                per_proc_ec_free[p] += 1

    total_tested = ec_free + ec_present
    if verbose:
        print(f"\nTested {total_tested} cycles")
        print(f"  EC-free: {ec_free}")
        print(f"  EC-present: {ec_present}")
        print(f"  Min conflicts: {min_conflicts} (cycle type: {best_cycle_name})")
        print(f"  Per-proc EC-free fraction:")
        for p in range(n):
            frac = per_proc_ec_free.get(p, 0) / total_tested if total_tested > 0 else 0
            m_L = ms[(p-1)%n]; m_S = ms[p]; m_R = ms[(p+1)%n]
            ctx = m_L * m_S * m_R
            print(f"    P{p} (ctx={ctx}): {per_proc_ec_free.get(p,0)}/{total_tested} = {frac:.3f}")

    return {
        'total': total_tested, 'ec_free': ec_free,
        'min_conflicts': min_conflicts, 'per_proc_ec_free': dict(per_proc_ec_free)
    }


def p3_crossover_analysis():
    """Detailed analysis of the P3 pigeonhole crossover.

    P3 has context (m_2, m_3, m_4) = (2, 3, 4) => ctx_size = 24.
    Cycle length CL = sum(ms) = 6 + 3(n-4) + 4 = 3n - 2.
    Wait... ms = (2,2,2,3,4,...): sum = 2+2+2+3+4+3*(n-5) = 13+3(n-5) = 3n-2.

    CL/ctx_P3 = (3n-2)/24.
    This equals 1.0 when 3n-2=24, i.e., n=26/3 ≈ 8.67.
    So: n<=8 => CL/ctx < 1 at P3; n>=9 => CL/ctx > 1 at P3.

    This is the EXACT crossover.
    """
    print("\n" + "="*70)
    print("P3 PIGEONHOLE CROSSOVER ANALYSIS")
    print("="*70)

    for n in range(5, 15):
        ms = tuple([2, 2, 2, 3, 4] + [3] * (n - 5))
        CL = sum(ms)
        # P3 has left=P2(m=2), self=P3(m=3), right=P4(m=4)
        ctx_P3 = 2 * 3 * 4  # = 24
        ratio = CL / ctx_P3

        # How many mover fires at P3?
        mover_P3 = ms[3]  # = 3
        nonmover_P3 = CL - mover_P3

        # Minimum possible mover-nonmover overlap by pigeonhole:
        # mover uses 3 distinct contexts (must be distinct for incrementing)
        # nonmover uses CL-3 contexts (need not be distinct)
        # nonmover distinct contexts <= ctx_P3
        # For mover-nonmover overlap: if mover uses M distinct and nonmover uses N distinct,
        # overlap >= max(0, M + N - ctx_P3)
        # M = 3, N <= min(CL-3, ctx_P3)
        N_max = min(CL - 3, ctx_P3)
        min_overlap = max(0, 3 + N_max - ctx_P3)

        # But nonmover may reuse contexts, reducing distinct count.
        # Minimum overlap when nonmover minimizes distinct contexts = ?
        # Nonmover can reuse as much as it wants. Minimum distinct nonmover = 1 (same context each time).
        # But that's unrealistic -- the cycle visits different configs.

        # More realistic: how many DISTINCT nonmover contexts at P3?
        # This depends on the mover word. With sweep-type words, nonmover
        # contexts change slowly. With random words, they spread more.

        print(f"  n={n}: CL={CL}, ctx_P3={ctx_P3}, CL/ctx={ratio:.4f}, "
              f"mover={mover_P3}, nonmover={CL-3}, "
              f"min_overlap>={min_overlap}")


def p3_context_anatomy(n, ms):
    """For each cycle type, examine P3's context distribution in detail."""
    CL = sum(ms)

    print(f"\n{'='*70}")
    print(f"P3 Context Anatomy: n={n}, ms={ms}, CL={CL}")
    print(f"P3 context = (P2_state, P3_state, P4_state) = (0..1, 0..2, 0..3)")
    print(f"{'='*70}")

    # Bounce cycle
    movers_list = generate_bounce_cycles(n, ms)
    for name, movers in movers_list:
        cycle = build_cycle_from_mover_word(n, ms, movers)
        if cycle is None:
            continue

        mover_steps = []
        nonmover_steps = []

        for idx in range(CL):
            c = cycle[idx]
            p = 3
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
            ctx = (L, S, R)
            if movers[idx] == p:
                mover_steps.append((idx, ctx))
            else:
                nonmover_steps.append((idx, ctx))

        mover_ctx_set = set(ctx for _, ctx in mover_steps)
        nonmover_ctx_set = set(ctx for _, ctx in nonmover_steps)
        overlap = mover_ctx_set & nonmover_ctx_set

        print(f"\n  {name}:")
        print(f"    Mover contexts ({len(mover_steps)} steps, {len(mover_ctx_set)} distinct):")
        for idx, ctx in mover_steps:
            marker = " <-- OVERLAP" if ctx in overlap else ""
            print(f"      step {idx:3d}: {ctx}{marker}")
        print(f"    Non-mover contexts ({len(nonmover_steps)} steps, {len(nonmover_ctx_set)} distinct):")
        for idx, ctx in nonmover_steps:
            marker = " <-- OVERLAP" if ctx in overlap else ""
            print(f"      step {idx:3d}: {ctx}{marker}")
        print(f"    Overlap: {overlap}")
        print(f"    |overlap| = {len(overlap)}")


def exhaustive_ec_check_small(n, ms, max_perms=1000000):
    """For small n, exhaustively check ALL mover word permutations for EC.

    This is feasible only for n=5 (CL=13, ~300K permutations).
    """
    from itertools import permutations
    import random

    CL = sum(ms)
    base = []
    for p in range(n):
        base.extend([p] * ms[p])

    # Count total permutations
    from math import factorial
    total_perms = factorial(CL)
    for p in range(n):
        total_perms //= factorial(ms[p])
    print(f"\n  Total mover word permutations: {total_perms}")

    if total_perms > max_perms:
        print(f"  Too many ({total_perms} > {max_perms}). Sampling instead.")
        # Sample
        random.seed(42)
        tested = 0
        ec_free = 0
        seen = set()
        while tested < max_perms and len(seen) < total_perms:
            perm = list(base)
            random.shuffle(perm)
            key = tuple(perm)
            if key in seen:
                continue
            seen.add(key)

            cycle = build_cycle_from_mover_word(n, ms, perm)
            if cycle is None:
                continue

            _, total = check_entry_conflicts(n, ms, cycle, perm)
            tested += 1
            if total == 0:
                ec_free += 1
                if ec_free <= 3:
                    print(f"    EC-FREE FOUND: {perm}")

        print(f"  Tested {tested}/{total_perms}: {ec_free} EC-free")
        return ec_free
    else:
        # Exhaustive
        from more_itertools import distinct_permutations
        # Fall back to manual dedup
        tested = 0
        ec_free = 0
        seen = set()

        def gen_perms(items):
            """Generate distinct permutations."""
            if len(items) <= 1:
                yield tuple(items)
                return
            prev = None
            sorted_items = sorted(items)
            for perm in permutations(sorted_items):
                if perm != prev:
                    prev = perm
                    yield perm

        # Use set for dedup since permutations generates duplicates
        for perm in permutations(base):
            key = perm
            if key in seen:
                continue
            seen.add(key)

            cycle = build_cycle_from_mover_word(n, ms, list(perm))
            if cycle is None:
                tested += 1
                continue

            _, total = check_entry_conflicts(n, ms, cycle, list(perm))
            tested += 1
            if total == 0:
                ec_free += 1
                if ec_free <= 5:
                    print(f"    EC-FREE FOUND: {list(perm)}")

            if tested % 50000 == 0:
                print(f"    ... tested {tested}/{total_perms}, ec_free={ec_free}")

        print(f"  Exhaustive: tested {tested}, ec_free={ec_free}")
        return ec_free


def find_all_valid_cycles_n5():
    """Find all valid mover words at n=5 with ms=(2,2,2,3,4).

    CL=13. Total distinct mover words = 13!/(2!*2!*2!*3!*4!) = 900900.
    Feasible to enumerate.
    """
    n = 5
    ms = (2, 2, 2, 3, 4)
    CL = sum(ms)  # 13
    product_val = prod(ms)  # 96
    threshold = 4 * 3**(n-2)  # 108

    print(f"\n{'='*70}")
    print(f"EXHAUSTIVE EC CHECK: n={n}, ms={ms}")
    print(f"product={product_val}, threshold={threshold}, sub-threshold={product_val < threshold}")
    print(f"CL={CL}")
    print(f"{'='*70}")

    return exhaustive_ec_check_small(n, ms, max_perms=200000)


if __name__ == "__main__":
    # P3 crossover
    p3_crossover_analysis()

    # Context anatomy at n=8 and n=9
    for n in [8, 9]:
        ms = tuple([2, 2, 2, 3, 4] + [3] * (n - 5))
        p3_context_anatomy(n, ms)

    # Full EC analysis for each n
    for n in [5, 6, 7, 8]:
        ms = tuple([2, 2, 2, 3, 4] + [3] * (n - 5))
        full_ec_analysis(n, ms)

    # n=9 for comparison
    ms9 = (2, 2, 2, 3, 4, 3, 3, 3, 3)
    full_ec_analysis(9, ms9)

    # Exhaustive check at n=5
    find_all_valid_cycles_n5()

    # Now the KEY question: for mover words that are EC-free at n=5,
    # can we actually build valid systems?
    print("\n" + "="*70)
    print("CRITICAL QUESTION: Can EC-free cycles yield valid systems?")
    print("="*70)
    print("\nAt n=5, ms=(2,2,2,3,4), product=96=M_5.")
    print("We KNOW valid systems exist (M_5=96 is achievable).")
    print("So EC-free cycles MUST exist at n=5.")
    print("The question: at what n do they disappear?")
