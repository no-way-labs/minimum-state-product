#!/usr/bin/env python3
"""PA: The counting argument for why normalForm phases force EC.

THEOREM STRUCTURE:
Given >=3 non-consecutive binary on a ring of n>=9 procs, sub-threshold product,
any good cycle gc:

1. Each ternary proc t fires fc[t] = 3*M_t times (M_t >= 1)
2. Each binary proc b fires fc[b] = 2*K_b times (K_b >= 1)
3. At boundary ternary t between binary bL and bR:
   - t has 3*M_t phases (one per t-value interval)
   - In each phase, bL fires J times and bR fires K times
   - Sum over phases: sum(J_i) = total bL-firings seen by t
   - Sum over phases: sum(K_i) = total bR-firings seen by t

KEY INSIGHT: The constraint is on the BINARY fire counts.
Each binary b has fc[b] = 2*K_b firings. These firings are "seen" by
b's two ternary neighbors (one on each side). In a non-consecutive
binary placement, b has TWO ternary neighbors.

At ternary t_left of b: b fires contribute to the K (right-side) count
At ternary t_right of b: b fires contribute to the J (left-side) count

The total firings of b = sum over t_left's phases of K_i + ??
Wait, that's not quite right. ALL of b's firings happen in the global
cycle. Each firing of b occurs in exactly one phase of each of its
ternary neighbors. So:

For ternary tL (left of b): sum_over_phases(K_i) = total b-firings = 2*K_b
For ternary tR (right of b): sum_over_phases(J_i) = total b-firings = 2*K_b

CONSTRAINT: sum_over_phases(J or K from b) = 2*K_b (EVEN).

NormalForm values: (1,0), (0,1), (1,1), (2,1), (1,2).
One-sided contributions per phase: J or K ∈ {0, 1, 2}.

If all phases are normalForm, the possible J values per phase from bL are:
  0 (from (0,1)), 1 (from (1,0),(1,1),(1,2)), 2 (from (2,1))

And these must sum to an EVEN number (2*K_bL).

Similarly for K values from bR.

Question: is this sum-to-even constraint always satisfiable?
Answer: Yes, trivially: just pick an even number of odd-J phases.

So the counting argument alone doesn't give a contradiction.
We need a STRUCTURAL argument.

Let me check: at n=7, what structural property forces EC in normalForm cycles?
"""

from collections import Counter, defaultdict


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


def extract_phases(word, cycle, ms, n, t):
    ell = len(word)
    bL = (t - 1) % n
    bR = (t + 1) % n
    t_steps = [s for s in range(ell) if word[s] == t]
    fc_t = len(t_steps)
    if fc_t == 0:
        return []
    phases = []
    for i in range(fc_t):
        start = (t_steps[i] + 1) % ell
        end = t_steps[(i + 1) % fc_t]
        J, K = 0, 0
        s = start
        while s != end:
            if word[s] == bL:
                J += 1
            elif word[s] == bR:
                K += 1
            s = (s + 1) % ell
        phases.append((J, K))
    return phases


# At n=7, analyze WHY all normalForm cycles have EC
n = 7
ms = [2, 3, 2, 3, 2, 3, 2]
max_len = 22
boundary_t = [1, 3, 5]

words = enumerate_mover_words(ms, n, max_len)
print(f"n=7, {len(words)} words")

# Find normalForm cycles and check what causes EC
nf_cycles = []
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None:
        continue

    all_nf = True
    for t in boundary_t:
        phases = extract_phases(word, cycle, ms, n, t)
        for J, K in phases:
            if (J, K) not in [(1, 0), (0, 1), (1, 1), (2, 1), (1, 2)]:
                all_nf = False
                break
        if not all_nf:
            break
    if all_nf:
        nf_cycles.append((word, cycle))

print(f"NormalForm cycles: {len(nf_cycles)}")

# For each normalForm cycle, find WHERE EC occurs
ec_location = Counter()
binary_ec_count = 0

for word, cycle in nf_cycles:
    ell = len(word)
    fc = Counter(word)

    ec_at = []
    for t in range(n):
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
        if mover & nonmover:
            ec_at.append(t)

    for t in ec_at:
        ec_location[t] += 1

    if any(ms[t] == 2 for t in ec_at):
        binary_ec_count += 1

print(f"\nEC location distribution:")
for t in range(n):
    cnt = ec_location.get(t, 0)
    label = f"binary" if ms[t] == 2 else f"ternary"
    bt = "boundary" if t in boundary_t else ""
    print(f"  proc {t} ({label} {bt}): EC in {cnt}/{len(nf_cycles)} cycles")
print(f"\nCycles with EC at some binary: {binary_ec_count}/{len(nf_cycles)}")

# KEY: What phase patterns appear at boundary ternary?
print(f"\nPhase pattern distribution at boundary ternary:")
phase_patterns = Counter()
for word, cycle in nf_cycles:
    for t in boundary_t:
        phases = extract_phases(word, cycle, ms, n, t)
        phase_patterns[tuple(sorted(phases))] += 1

for pattern, cnt in phase_patterns.most_common(20):
    print(f"  {pattern}: {cnt}")

# For normalForm cycles: check the VALUE TRACE at boundary ternary
# What context (L,S,R) appears at mover vs nonmover steps?
# The EC mechanism must be: the limited context space (binary neighbor
# has only 2 values) forces a collision even with normalForm phases.
print(f"\n{'='*70}")
print("VALUE TRACE ANALYSIS: WHY normalForm cycles still have EC at n=7")
print("=" * 70)

for word, cycle in nf_cycles[:3]:
    ell = len(word)
    fc = Counter(word)
    print(f"\nword={word}")
    print(f"fc_mult = {tuple(fc[p]//ms[p] for p in range(n))}")

    for t in boundary_t:
        bL = (t - 1) % n
        bR = (t + 1) % n
        phases = extract_phases(word, cycle, ms, n, t)
        print(f"  proc {t} phases={phases}")

        # Track value of t at each step
        mover_ctx = {}
        nonmover_ctx = {}
        for s in range(ell):
            ctx = (cycle[s][bL], cycle[s][t], cycle[s][bR])
            if word[s] == t:
                mover_ctx[s] = ctx
            else:
                nonmover_ctx[s] = ctx

        m_set = set(mover_ctx.values())
        n_set = set(nonmover_ctx.values())
        print(f"    mover_ctx={m_set}")
        print(f"    nonmover_ctx={n_set}")
        print(f"    overlap={m_set & n_set}")
        print(f"    |mover|={len(m_set)}, |nonmover|={len(n_set)}, total_ctx_space={2*ms[t]*2}")
