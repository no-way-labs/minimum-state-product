#!/usr/bin/env python3
"""
Fixed Point Impossibility for Sweep Good Cycles.

Theorem: For a sweep good cycle with non-consecutive binary, isolated firings,
n >= 9, sub-threshold product (< 4*3^(n-2)), >= 3 binary processors:
every non-good config has at least one privileged processor.

Equivalently: no fixed point (config with 0 privileged procs) exists outside
the good cycle.

Approach: In a sweep good cycle, the mover at step t fires at processor p_t.
The mover context is (L_t, S_t, R_t) and the transition maps it to S'_t != S_t.
If a fixed point c exists, then for every processor p, f_p(c[p-1], c[p], c[p+1]) = c[p].
This means the context (c[p-1], c[p], c[p+1]) at processor p must NOT be a mover
context of the good cycle (otherwise f_p would map to something != c[p]).

So: a fixed point uses only "non-mover contexts" at every processor.
We check: can we find a config where every processor sees a non-mover context?

For a sweep cycle: mover visits every processor exactly m_p times (where m_p
is the state count). The mover contexts at processor p are exactly the (L, S, R)
triples where the transition fires. Let's count and check coverage.
"""

from itertools import product as iproduct
import sys

def build_sweep_cycle(ms, direction='cw'):
    """
    Build the canonical CW sweep good cycle for state vector ms.

    For the CUP-2 / CLB construction with ms = (2,3,...,3,2) or similar,
    we need to be more careful. Let's build a generic sweep cycle.

    A sweep cycle visits processors 0, 1, 2, ..., n-1, 0, 1, ... (CW)
    Each processor p is visited m_p times total (fire count = m_p in a full cycle).
    Cycle length = sum(m_p) = total state product? No, cycle length = sum(m_p).
    Wait: in a sweep, the mover word is (0, 1, 2, ..., n-1, 0, 1, ...) repeating.
    Each proc fires m_p times. Cycle length = sum(m_p).

    Actually for fire_count = m_p, each proc cycles through all m_p values.
    Let me think about what configs look like in a sweep cycle.

    In a CW sweep, at step t, processor p_t = t mod n fires.
    The state at p_t cycles through its m_p values.

    Let's just enumerate mover contexts computationally for small n.
    """
    n = len(ms)
    # For a sweep good cycle, we need to construct actual configs.
    # Let's use the standard incrementing transition for simplicity:
    # when proc p fires, c[p] -> (c[p] + 1) % m_p

    # Start from all-zeros config
    c = [0] * n
    configs = []
    movers = []
    mover_contexts = {p: set() for p in range(n)}
    nonmover_contexts = {p: set() for p in range(n)}

    cycle_len = sum(ms)

    for t in range(cycle_len):
        p = t % n  # CW sweep: 0, 1, 2, ..., n-1, 0, 1, ...
        config = tuple(c)
        configs.append(config)
        movers.append(p)

        L = c[(p - 1) % n]
        S = c[p]
        R = c[(p + 1) % n]
        mover_contexts[p].add((L, S, R))

        # Record non-mover contexts
        for q in range(n):
            if q != p:
                Lq = c[(q - 1) % n]
                Sq = c[q]
                Rq = c[(q + 1) % n]
                nonmover_contexts[q].add((Lq, Sq, Rq))

        # Apply move: increment
        c[p] = (c[p] + 1) % ms[p]

    return configs, movers, mover_contexts, nonmover_contexts


def count_total_contexts(ms):
    """Total possible (L, S, R) contexts at each processor."""
    n = len(ms)
    total = {}
    for p in range(n):
        total[p] = ms[(p-1) % n] * ms[p] * ms[(p+1) % n]
    return total


def check_fixed_point_possible(ms, mover_contexts):
    """
    Check if a fixed point config exists that avoids all mover contexts.

    A fixed point c has: for each p, (c[p-1], c[p], c[p+1]) not in mover_contexts[p].

    This is a constraint satisfaction problem. We enumerate all configs and check.
    """
    n = len(ms)
    total_configs = 1
    for m in ms:
        total_configs *= m

    if total_configs > 10**7:
        return None, "too large"

    fixed_points = []
    for c in iproduct(*(range(m) for m in ms)):
        is_fp = True
        for p in range(n):
            L = c[(p-1) % n]
            S = c[p]
            R = c[(p+1) % n]
            if (L, S, R) in mover_contexts[p]:
                is_fp = False
                break
        if is_fp:
            fixed_points.append(c)

    return fixed_points, f"found {len(fixed_points)}"


def analyze_sweep_coverage(ms):
    """Analyze mover context coverage for a sweep cycle."""
    n = len(ms)
    configs, movers, mover_ctx, nonmover_ctx = build_sweep_cycle(ms)
    total_ctx = count_total_contexts(ms)

    print(f"\nms = {ms}, n = {n}, product = {prod(ms)}")
    print(f"Cycle length = {sum(ms)}")
    print(f"Configs in good cycle = {len(configs)}")

    for p in range(n):
        mc = len(mover_ctx[p])
        tc = total_ctx[p]
        free = tc - mc
        print(f"  P{p} (m={ms[p]}): mover contexts = {mc}/{tc}, "
              f"free = {free} ({100*free/tc:.1f}%)")

    # Check if fixed point exists
    fps, msg = check_fixed_point_possible(ms, mover_ctx)
    if fps is not None:
        print(f"Fixed points avoiding all mover contexts: {len(fps)}")
        if fps and len(fps) <= 10:
            for fp in fps:
                print(f"  {fp}")
                # Check if it's in the good cycle
                if fp in set(map(tuple, [list(c) for c in configs])):
                    print(f"    ^ IN GOOD CYCLE")
    else:
        print(f"Fixed point check: {msg}")

    return mover_ctx, fps


def prod(lst):
    r = 1
    for x in lst:
        r *= x
    return r


def analyze_binary_proc_coverage(ms, mover_ctx):
    """
    For binary processors (m_p = 2), analyze mover context coverage in detail.

    Key insight: a binary processor p has states {0, 1}.
    Mover contexts: (L, S, R) where the sweep fires p.
    In a sweep, p fires exactly 2 times (m_p = 2), cycling 0->1->0.
    So mover contexts at p: exactly 2 entries: (L_first, 0, R_first) and (L_second, 1, R_second).

    For a fixed point at p: we need (c[p-1], c[p], c[p+1]) to NOT be a mover context.
    Since c[p] is either 0 or 1, we need to avoid the mover context for that value.
    """
    n = len(ms)
    for p in range(n):
        if ms[p] == 2:
            print(f"\n  Binary P{p}: mover contexts = {sorted(mover_ctx[p])}")
            # For each value s in {0, 1}, which (L, R) pairs are blocked?
            for s in range(2):
                blocked = [(L, R) for (L, S, R) in mover_ctx[p] if S == s]
                total_LR = ms[(p-1)%n] * ms[(p+1)%n]
                print(f"    s={s}: blocked (L,R) = {blocked}, "
                      f"free = {total_LR - len(blocked)}/{total_LR}")


print("="*70)
print("FIXED POINT IMPOSSIBILITY ANALYSIS")
print("="*70)

# Test small cases first
print("\n--- Small cases with incrementing sweep ---")

# n=5, non-consecutive binary: e.g., ms=(2,3,2,3,2) - 3 non-consecutive binary
for ms in [
    [2, 3, 2, 3, 2],   # 3 non-consec binary, product=72 < 108=4*27
    [2, 3, 3, 2, 3],   # 2 non-consec binary
    [2, 3, 2, 3, 3],   # 2 non-consec binary (at 0,2)
]:
    mover_ctx, fps = analyze_sweep_coverage(ms)
    analyze_binary_proc_coverage(ms, mover_ctx)

print("\n\n--- n=6 cases ---")
for ms in [
    [2, 3, 2, 3, 2, 3],  # 3 non-consec binary, product=216 < 324
    [2, 3, 2, 3, 3, 3],  # 2 non-consec, product=162 < 324
]:
    mover_ctx, fps = analyze_sweep_coverage(ms)

print("\n\n--- n=9 cases (sub-threshold < 4*3^7 = 8748) ---")
for ms in [
    [2, 3, 2, 3, 2, 3, 3, 3, 3],  # 3 non-consec, product=5832
    [2, 3, 2, 3, 2, 3, 2, 3, 3],  # 4 non-consec, product=3888
]:
    mover_ctx, fps = analyze_sweep_coverage(ms)
