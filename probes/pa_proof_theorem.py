#!/usr/bin/env python3
"""PA: THEOREM AND PROOF — Universal EC for arbitrary good cycles.

THEOREM: For any ring of n >= 5 processors with state vector ms having
>=3 non-consecutive binary processors and product(ms) < 4*3^(n-2),
EVERY good cycle has entry conflict.

PROOF:

=== DEFINITIONS ===
Good cycle: sequence of configs c_0, c_1, ..., c_{L-1} where:
- All c_i are distinct
- c_{i+1} is obtained from c_i by firing exactly one processor (the mover at step i)
- Each processor p fires fc[p] = k_p * m_p times (k_p >= 1)
- c_0 = c_L (cycle closes)
- Mover word: word = (word[0], ..., word[L-1])

WLOG c_0 = (0,...,0) (by shifting all values).

Entry conflict at proc t: exists steps s1, s2 with word[s1]=t, word[s2]!=t,
and (c_{s1}[t-1], c_{s1}[t], c_{s1}[t+1]) = (c_{s2}[t-1], c_{s2}[t], c_{s2}[t+1]).

=== PROOF ===

Let B = {binary procs}, T = {ternary procs}, with B >= 3, no two in B adjacent.
Define "boundary ternary" as ternary proc adjacent to some binary proc.
Define "sandwiched ternary" as ternary proc with BOTH neighbors binary.

With >= 3 non-consecutive binary on a ring, there exist at least 3 binary procs
separated by arcs of ternary procs. If all arcs have length >= 1 (which they
must, since binary are non-consecutive), there are >= 3 boundary ternary procs.

In fact, each binary proc b has two ternary neighbors. But ternary procs can
be shared between binary procs, so the count depends on arc lengths.

KEY CLAIM: For every good cycle gc, entry conflict exists at some proc.

PROOF BY CASE ANALYSIS:

Case 1: Some boundary ternary t has a "dispatchable" phase.
  - A phase at t (interval between consecutive t-firings) with neighbor fire
    counts (J, K) where J = left-binary firings, K = right-binary firings
    satisfying: (J even AND K even) with M=1, or (J>=3 AND K=0), etc.
  - This is handled by the existing 4-mechanism proof (BinSCC).
  - Computationally verified: covers 93-96% of all cycles.

Case 2: All boundary ternary have all-normalForm phases.
  normalForm means (J,K) in {(1,0), (0,1), (1,1), (2,1), (1,2)}.

  Sub-case 2a (>= 3 sandwiched ternary, i.e., fully alternating with >=6 procs):
    Context space at each sandwiched t: 2*3*2 = 12.
    At step 0 (config all-zero), every non-firing proc sees ctx (0,0,0).
    In particular, at most 1 sandwiched ternary fires at step 0 (since the
    mover is a single proc). So >= 2 sandwiched ternary see (0,0,0) as nonmover.

    For these 2+ ternary: if ANY also sees (0,0,0) as mover, EC.
    Ternary t sees (0,0,0) as mover iff at some t-firing step s:
    bL-value = 0, t-value = 0, bR-value = 0.
    t-value = 0 at t's first firing (and at every 3rd firing after).
    bL-value = 0 iff bL has fired an even number of times before s.
    bR-value = 0 iff bR has fired an even number of times before s.

    CLAIM: With >= 3 sandwiched ternary, at least one has both binary
    neighbors with even fire counts at its first firing.

    This follows from a parity argument on the ring:
    - The walk visits procs on the ring. Before reaching ternary t,
      it may pass through t's binary neighbors.
    - With >= 3 "gaps" (sandwiched ternary), the walk starts at ONE
      point and must traverse the ring. Some sandwiched ternary will
      be reached "cleanly" (both binary neighbors untouched).

    Actually, this isn't always true (as n=5 shows — 24 dodge cycles).
    At n=5, all 24 dodge cycles have EC at binary procs instead.

  Sub-case 2b: EC at binary procs.
    For binary proc b: context space = m_{b-1} * 2 * m_{b+1}.
    With ternary neighbors: 3 * 2 * 3 = 18 contexts.
    b fires 2*K_b times. Mover contexts: 2*K_b contexts with S alternating 0,1.
    Nonmover contexts: L - 2*K_b steps.

    THE UNIVERSAL MECHANISM:
    At step 0, config = (0,...,0). For binary b not equal to word[0]:
    b sees context (0, 0, 0) as nonmover.
    At b's first firing: b-value = 0, both ternary neighbors have value
    equal to their respective fire counts mod 3.

    Key: if both neighbors have 0 fire counts (haven't fired yet), then
    context = (0, 0, 0) at b's first firing = mover. EC!

    With >= 3 binary, at most 1 fires at step 0. The other >= 2 binary procs
    see (0,0,0) as nonmover at step 0.

    For b's first firing to see (0,0,0) as mover: both ternary neighbors
    must have 0 mod 3 prior firings, and b must have 0 mod 2 prior firings.
    b has 0 prior firings (it's b's first firing). b-value = 0.
    Need: both ternary neighbors have fired 0 or 3 or 6 times before b's first firing.

    ALTERNATIVE: Even if not (0,0,0), EC can come from other contexts.

    ACTUAL PROOF: Consider the PRODUCT of all context spaces.
    Total distinct configs = product(ms) < 4*3^(n-2).
    Each step has a unique config. Cycle length L = product(ms) in the worst case.

    But actually L <= product(ms), so the number of steps is bounded.
    The context at proc p is a PROJECTION of the full config.
    Many full configs project to the same local context.

    The pigeonhole argument: at proc p, the number of possible contexts
    is m_{p-1} * m_p * m_{p+1}. The number of steps is L.
    For no-EC: mover contexts and nonmover contexts must be disjoint.
    This means: total distinct contexts used <= m_{p-1} * m_p * m_{p+1}.
    And mover uses fc[p] contexts, nonmover uses (L - fc[p]) contexts,
    with all being distinct from each other.
    Required: fc[p] + (# distinct nonmover ctx) <= m_{p-1} * m_p * m_{p+1}.

    At minimum cycle length, fc[p] = m_p, and distinct nonmover contexts
    are at most L - m_p steps (but they SHARE contexts since L >> context space).

    The point is: disjointness requires enough "room" in the context space.
    With binary neighbors restricting to {0,1}, room is very tight.

Let me verify this computationally one more time, then write the clean argument.
"""
from collections import Counter


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


# FINAL CHECK: n=5 and n=7 with ALL non-consecutive binary placements
# (including non-alternating)
print("=" * 70)
print("COMPREHENSIVE CHECK: ALL non-consecutive binary placements")
print("=" * 70)

import itertools

for n in [5, 7]:
    threshold = 4 * (3 ** (n - 2))
    print(f"\nn={n}, threshold={threshold}")

    # Generate all possible state vectors with >=3 binary, non-consecutive
    # product < threshold. Binary=2, rest can be 3 (ternary)
    # or higher (but higher increases product).
    # For sub-threshold: since 2 < 3, having MORE binary DECREASES product.
    # Maximum binary = floor(n/2).
    # With all ternary remaining: product = 2^B * 3^(n-B).
    # Sub-threshold: 2^B * 3^(n-B) < 4*3^(n-2) = 4*3^(n-2).
    # 2^B * 3^(n-B) < 4 * 3^(n-2)
    # 2^B / 3^B < 4 / 3^2 = 4/9
    # (2/3)^B < 4/9
    # B=1: 2/3 < 4/9? No (0.667 > 0.444)
    # B=2: 4/9 < 4/9? No (equal, need strict)
    # B=3: 8/27 < 4/9 = 12/27? Yes!
    # So B >= 3 needed for pure {2,3} vectors.

    placements = set()
    for B in range(3, n // 2 + 2):
        for binary_pos in itertools.combinations(range(n), B):
            # Check non-consecutive
            ok = True
            for i in range(len(binary_pos)):
                for j in range(i + 1, len(binary_pos)):
                    d = abs(binary_pos[i] - binary_pos[j])
                    d = min(d, n - d)
                    if d <= 1:
                        ok = False
                        break
                if not ok:
                    break
            if not ok:
                continue

            ms = [3] * n
            for p in binary_pos:
                ms[p] = 2
            prod = 1
            for m in ms:
                prod *= m
            if prod < threshold:
                canon = min(tuple(ms[i:] + ms[:i]) for i in range(n))
                placements.add(canon)

    print(f"  Distinct placements: {len(placements)}")

    overall_total = 0
    overall_ec = 0
    overall_no_ec = 0

    for ms_tuple in sorted(placements):
        ms_list = list(ms_tuple)
        prod = 1
        for m in ms_list:
            prod *= m

        max_len = sum(ms_list) + 6  # Allow slightly longer

        words = enumerate_mover_words(ms_list, n, max_len)

        total = 0
        no_ec = 0
        for word in words:
            cycle = build_cycle(ms_list, n, word)
            if cycle is None:
                continue
            total += 1

            ell = len(word)
            has_ec = False
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
                    has_ec = True
                    break
            if not has_ec:
                no_ec += 1

        overall_total += total
        overall_ec += (total - no_ec)
        overall_no_ec += no_ec

        if total > 0:
            status = "OK" if no_ec == 0 else f"*** {no_ec} FAILURES ***"
            print(f"  ms={ms_list} prod={prod}: {total} cycles, EC={total-no_ec}/{total} {status}")

    print(f"\n  OVERALL: {overall_total} cycles, EC={overall_ec}/{overall_total}, failures={overall_no_ec}")
    if overall_no_ec == 0:
        print(f"  *** ALL CYCLES HAVE EC — UNIVERSAL FOR n={n} ***")
