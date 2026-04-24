#!/usr/bin/env python3
"""PA: Universal EC proof — definitive check.

The argument: for >=3 non-consecutive binary at sub-threshold product,
every good cycle has entry conflict SOMEWHERE.

We need to check:
1. EC at boundary ternary? (answer: yes for n>=7 computationally)
2. EC anywhere? (answer: always yes, even at n=5)
3. What mechanism covers the n=5 residual?

Then we prove the theorem analytically for n>=9.

ANALYSIS OF THE PROOF:

THEOREM: For n >= 5, ms with >=3 non-consecutive binary, product < 4*3^(n-2),
every good cycle gc has entry conflict.

PROOF SKETCH:
Case A: Some boundary ternary t has a dispatchable phase -> EC by existing mechanisms
Case B: All boundary ternary procs have all-normalForm phases:
  Sub-case B1 (n>=7): The (L,R)-pair pigeonhole at M=1 boundary ternary forces EC.
    - At M=1, each S-level has exactly 1 mover (L,R) pair.
    - We show nonmover covers enough (L,R) pairs to force collision.
  Sub-case B2 (n=5): EC occurs at a BINARY proc. The binary proc's context
    space is tiny (neighbors are ternary: 3*2*3=18 contexts). The constraint
    that binary toggles 0/1 with each firing means the all-zero config
    (0,0,0) appears at both mover and nonmover steps.

Let me verify the exact mechanism.
"""
from collections import Counter, defaultdict
import itertools


def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    min_len = sum(ms)
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= min_len and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
            return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n)
                      if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            nc = list(config)
            nc[nxt] = (nc[nxt] + 1) % ms[nxt]
            nf = list(fc)
            nf[nxt] += 1
            word.append(nxt)
            dfs(word, nf, tuple(nc))
            word.pop()
    for p in range(n):
        first = list(start)
        first[p] = (first[p] + 1) % ms[p]
        dfs([p], [1 if i == p else 0 for i in range(n)], tuple(first))
    return results


def build_cycle(ms, n, word):
    ell = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:ell])) != ell:
        return None
    return configs[:ell]


def has_ec_at_proc(word, cycle, n, t):
    """Check EC at specific proc."""
    ell = len(word)
    bL = (t - 1) % n
    bR = (t + 1) % n
    mover = set()
    nonmover = set()
    for s in range(ell):
        ctx = (cycle[s][bL], cycle[s][t], cycle[s][bR])
        if word[s] == t:
            mover.add(ctx)
        else:
            nonmover.add(ctx)
    return bool(mover & nonmover)


def has_ec_anywhere(word, cycle, ms, n):
    """Check EC at any proc."""
    for t in range(n):
        if has_ec_at_proc(word, cycle, n, t):
            return True
    return False


# ======================================================================
# DEFINITIVE: n=5, 7, 9 check — EC EVERYWHERE
# ======================================================================
print("=" * 70)
print("DEFINITIVE UNIVERSAL EC CHECK")
print("For >=3 non-consecutive binary, sub-threshold product")
print("=" * 70)

for n, ms_list, max_len in [
    (5, [2, 3, 2, 3, 2], 16),
    (7, [2, 3, 2, 3, 2, 3, 2], 22),
]:
    boundary_t = [t for t in range(n) if ms_list[t] == 3
                  and ms_list[(t-1)%n] == 2 and ms_list[(t+1)%n] == 2]

    words = enumerate_mover_words(ms_list, n, max_len)
    print(f"\nn={n}, ms={ms_list}")

    total = 0
    ec_boundary = 0
    ec_binary = 0
    ec_any = 0
    no_ec = 0

    for word in words:
        cycle = build_cycle(ms_list, n, word)
        if cycle is None:
            continue
        total += 1

        # Check EC at boundary ternary
        has_bt_ec = any(has_ec_at_proc(word, cycle, n, t) for t in boundary_t)
        # Check EC at binary
        binary_procs = [p for p in range(n) if ms_list[p] == 2]
        has_bin_ec = any(has_ec_at_proc(word, cycle, n, b) for b in binary_procs)
        # Check EC anywhere
        has_any_ec = has_ec_anywhere(word, cycle, ms_list, n)

        if has_bt_ec:
            ec_boundary += 1
        if has_bin_ec:
            ec_binary += 1
        if has_any_ec:
            ec_any += 1
        else:
            no_ec += 1

    print(f"  Total cycles: {total}")
    print(f"  EC at boundary ternary: {ec_boundary}/{total} ({100*ec_boundary/total:.1f}%)")
    print(f"  EC at binary:           {ec_binary}/{total} ({100*ec_binary/total:.1f}%)")
    print(f"  EC anywhere:            {ec_any}/{total} ({100*ec_any/total:.1f}%)")
    print(f"  NO EC anywhere:         {no_ec}")

    if no_ec == 0:
        print(f"  *** UNIVERSAL EC CONFIRMED ***")
    else:
        print(f"  *** WARNING: {no_ec} cycles with NO EC ***")

# ======================================================================
# KEY QUESTION: At n>=9, what is the minimum cycle length?
# And how does the pigeonhole work?
# ======================================================================
print(f"\n{'='*70}")
print("CYCLE LENGTH AND CONTEXT CAPACITY ANALYSIS")
print("=" * 70)

for n, ms_list, max_len in [
    (5, [2, 3, 2, 3, 2], 16),
    (7, [2, 3, 2, 3, 2, 3, 2], 22),
]:
    boundary_t = [t for t in range(n) if ms_list[t] == 3
                  and ms_list[(t-1)%n] == 2 and ms_list[(t+1)%n] == 2]

    words = enumerate_mover_words(ms_list, n, max_len)

    ell_dist = Counter()
    for word in words:
        cycle = build_cycle(ms_list, n, word)
        if cycle is None:
            continue
        ell_dist[len(word)] += 1

    print(f"\nn={n}: cycle length distribution")
    for ell, cnt in sorted(ell_dist.items()):
        # Compute context capacity at boundary ternary
        # Context space = 2 * 3 * 2 = 12 (binary-ternary-binary)
        # Mover uses 3 (M=1) or 3*M contexts
        # Nonmover uses ell - 3*M steps (but some share contexts)
        ctx_space = 12  # for boundary ternary between two binary
        min_mover = 3  # M=1: one per S-level
        nonmover_steps = ell - min_mover
        print(f"  ell={ell}: {cnt} cycles, nonmover_steps={nonmover_steps}, ctx_space={ctx_space}")

# ======================================================================
# THE PROOF IDEA FOR n >= 9
# ======================================================================
print(f"\n{'='*70}")
print("PROOF IDEA FOR n >= 9")
print("=" * 70)

print("""
For n >= 9 with >=3 non-consecutive binary, alternating [2,3,2,...]:

1. There are >= 3 boundary ternary procs (each sandwiched between 2 binary).
   Actually with >=4 binary (n>=9 needs >=4 for product < 4*3^(n-2)),
   there are >=4 boundary ternary.

2. At each boundary ternary t (between binary bL, bR):
   Context space = {0,1} x {0,1,2} x {0,1} = 12 contexts.
   t fires >= 3 times (minimum: fc_t = 3, M=1).
   Mover gets 3 distinct contexts (one per S-level).
   Nonmover gets ell - 3 steps.

3. Minimum cycle length: ell >= sum(ms) = 2*B + 3*T where B = #binary, T = #ternary.
   For n=9: ell >= 2*4 + 3*5 = 23 (alternating, 4 binary).
   Or: ell >= 2*5 + 3*4 = 22 (5 binary at n=10).

4. Nonmover steps at t: ell - 3 >= 20 (for n=9).
   20 steps visiting 12 contexts → by pigeonhole, each context appears ~1.67 times.
   Actually: distinct nonmover contexts >= min(ell-3, 12) since the cycle is
   a SIMPLE cycle (all configs distinct).

5. KEY CONSTRAINT: the mover's (L,R) pair at S=k is determined by the
   binary neighbors' values JUST BEFORE t fires in phase k.
   The nonmover's (L,R) pairs at the SAME S=k include all intermediate
   binary values during the phase.

6. In a normalForm phase (J,K) ∈ {(1,0),(0,1),(1,1),(2,1),(1,2)}:
   - (1,0): bL fires once, bR doesn't. bL toggles. At S=k:
     nonmover sees bL=0 then bL=1 (or vice versa). 2 distinct (L,R).
     Mover sees the final value. Nonmover sees the initial value.
     DIFFERENT if bL changed by exactly 1 toggle.
   - (1,1): both fire once. 2 or 3 distinct (L,R) patterns.
   - (2,1): bL fires twice (returns to start!), bR once.
     Mover sees bL back at start value. Some nonmover step also has start value.
     THIS IS THE KEY: (2,1) means bL fires twice = returns to original.

WAIT. With (2,1): bL fires 2 times (even → returns to start value).
At the START of the phase, bL has value v. After 2 firings, bL = v again.
The mover's context at the END of the phase has bL = v.
But some nonmover step at the START of the phase ALSO has bL = v.
If S and R match too → EC!

Let me check this specifically.
""")

# Verify the (2,1) return mechanism
print("VERIFICATION: Does (2,1) phase at boundary ternary always give EC?")
print("=" * 70)

for n, ms_list, max_len in [
    (5, [2, 3, 2, 3, 2], 16),
    (7, [2, 3, 2, 3, 2, 3, 2], 22),
]:
    boundary_t = [t for t in range(n) if ms_list[t] == 3
                  and ms_list[(t-1)%n] == 2 and ms_list[(t+1)%n] == 2]

    words = enumerate_mover_words(ms_list, n, max_len)

    total_21_phases = 0
    ec_in_21_phase = 0

    for word in words:
        cycle = build_cycle(ms_list, n, word)
        if cycle is None:
            continue

        ell = len(word)
        fc = Counter(word)

        for t in boundary_t:
            bL = (t - 1) % n
            bR = (t + 1) % n
            t_steps = [s for s in range(ell) if word[s] == t]
            fc_t = len(t_steps)

            for i in range(fc_t):
                start = (t_steps[i] + 1) % ell
                end = t_steps[(i + 1) % fc_t]
                J, K = 0, 0
                s = start
                steps_in_phase = []
                while s != end:
                    steps_in_phase.append(s)
                    if word[s] == bL:
                        J += 1
                    elif word[s] == bR:
                        K += 1
                    s = (s + 1) % ell

                if (J, K) == (2, 1):
                    total_21_phases += 1
                    # Check EC: mover is at t_steps[(i+1)%fc_t]
                    mover_step = t_steps[(i + 1) % fc_t]
                    mover_ctx = (cycle[mover_step][bL], cycle[mover_step][t], cycle[mover_step][bR])

                    # Check if any nonmover in this phase has same context
                    has_match = False
                    for s in steps_in_phase:
                        if word[s] != t:
                            nm_ctx = (cycle[s][bL], cycle[s][t], cycle[s][bR])
                            if nm_ctx == mover_ctx:
                                has_match = True
                                break

                    # Also check: the FIRST nonmover step of the phase
                    # should have bL = mover's bL (since bL fires 2x = returns)
                    first_nm = None
                    for s in steps_in_phase:
                        if word[s] != t:
                            first_nm = s
                            break

                    if has_match:
                        ec_in_21_phase += 1

    print(f"\nn={n}: total (2,1) phases: {total_21_phases}")
    print(f"  EC within (2,1) phase: {ec_in_21_phase}/{total_21_phases}")
    if total_21_phases > 0:
        print(f"  Rate: {100*ec_in_21_phase/total_21_phases:.1f}%")
