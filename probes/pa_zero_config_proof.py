#!/usr/bin/env python3
"""PA: Zero-Config EC Theorem.

THEOREM: For n >= 5, >=3 non-consecutive binary, sub-threshold product,
every good cycle has entry conflict.

PROOF via the Zero-Config mechanism:

Lemma (Zero-Config EC): Let gc be a good cycle on a ring with n procs,
starting at config (0,...,0). Let t be any proc that does NOT fire at step 0.
Then t sees context (0, 0, 0) as a nonmover at step 0.

If t also sees (0, 0, 0) at some mover step -> EC at t.

Claim 1: t sees (0, 0, 0) as mover iff there exists a step s where word[s]=t
and both neighbors of t have fired an even number of times before step s,
and t has fired a multiple of m_t times (including 0) before step s.

For binary b adjacent to t: b has fired an even number = b's value is 0.
For t (ternary): t's value = 0 iff t has fired 0 or 3 or 6... times.
At t's FIRST firing (0 prior firings): t-value = 0. Need both binary
neighbors to have even prior firings.

Claim 2: In any mover word on a ring, the first proc to fire is word[0].
At step 0, ALL other procs have 0 prior firings (even for binary neighbors).
So word[0] sees (0,0,0) as mover.

If word[0] is NOT a boundary ternary: Then the boundary ternary that is NOT
adjacent to word[0] sees (0,0,0) as nonmover at step 0. We need this ternary
to ALSO see (0,0,0) as mover.

CRITICAL INSIGHT: For a ring walk starting at word[0]:
- word[0] fires first
- word[1] is adjacent to word[0] (ring constraint)
- word[2] is adjacent to word[1]
- etc.

The walk MUST traverse the ring. With >=3 non-consecutive binary, there are
>=3 boundary ternary procs. The walk can only be adjacent to 2 procs at any
time. So it can't "cover" all boundary ternary procs simultaneously.

APPROACH: Find the boundary ternary t that is LAST to be reached by the walk.
Before t fires for the first time, the walk has been going around and may
have fired t's neighbors multiple times. The parity of these firings
determines whether (0,0,0) appears.

But there's a simpler approach: look at the LAST firing of each boundary
ternary. At the 3rd (or 3M-th) firing of t, t-value = 2 (not 0). So
the mover context is (L, 2, R), never (0, 0, 0) at the last firing.

The KEY is the FIRST firing: t-value = 0. If both binary neighbors have
even prior fire counts -> mover sees (0, 0, 0) -> EC with step 0.

ALTERNATIVE: Look at not just step 0, but ALL "return" moments.
If a good cycle visits config (0,...,0) at step 0, it must also
return to (0,...,0) at step ell (wrapping). So configs form a cycle.

The zero config is special: it's the one where ALL procs have value 0.

But for EC, we need (L,S,R) match, not full config match. The zero
context (0,0,0) can appear at many different global configs.

Let me take a different approach: count how many steps have context (0,0,0)
at boundary ternary t, broken down by mover/nonmover.
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


print("=" * 70)
print("ZERO-CONTEXT ANALYSIS: (0,0,0) at boundary ternary")
print("=" * 70)

for n, ms_list, max_len in [
    (5, [2, 3, 2, 3, 2], 16),
    (7, [2, 3, 2, 3, 2, 3, 2], 22),
]:
    boundary_t = [t for t in range(n) if ms_list[t] == 3
                  and ms_list[(t-1)%n] == 2 and ms_list[(t+1)%n] == 2]

    words = enumerate_mover_words(ms_list, n, max_len)

    total = 0
    ec_via_000 = 0  # EC at some boundary ternary via (0,0,0)
    no_ec_000 = 0
    ec_via_000_all = 0  # EC at ANY proc via (0,0,0)

    # Track the 000 mechanism details
    for word in words:
        cycle = build_cycle(ms_list, n, word)
        if cycle is None:
            continue
        total += 1

        ell = len(word)

        # Check (0,0,0) overlap at boundary ternary
        has_000_ec = False
        for t in boundary_t:
            bL = (t - 1) % n
            bR = (t + 1) % n
            mover_000 = False
            nonmover_000 = False
            for s in range(ell):
                ctx = (cycle[s][bL], cycle[s][t], cycle[s][bR])
                if ctx == (0, 0, 0):
                    if word[s] == t:
                        mover_000 = True
                    else:
                        nonmover_000 = True
            if mover_000 and nonmover_000:
                has_000_ec = True
                break

        # Check (0,0,0) overlap at ANY proc
        has_000_any = False
        for t in range(n):
            bL = (t - 1) % n
            bR = (t + 1) % n
            mover_000 = False
            nonmover_000 = False
            for s in range(ell):
                ctx = (cycle[s][bL], cycle[s][t], cycle[s][bR])
                if ctx == (0, 0, 0):
                    if word[s] == t:
                        mover_000 = True
                    else:
                        nonmover_000 = True
            if mover_000 and nonmover_000:
                has_000_any = True
                break

        if has_000_ec:
            ec_via_000 += 1
        else:
            no_ec_000 += 1

        if has_000_any:
            ec_via_000_all += 1

    print(f"\nn={n}: {total} cycles")
    print(f"  EC via (0,0,0) at boundary ternary: {ec_via_000}/{total} ({100*ec_via_000/total:.1f}%)")
    print(f"  EC via (0,0,0) at ANY proc:         {ec_via_000_all}/{total} ({100*ec_via_000_all/total:.1f}%)")
    print(f"  NOT covered by (0,0,0):              {total - ec_via_000_all}")


# The remaining question: for cycles NOT covered by (0,0,0) EC,
# what mechanism gives EC?
print(f"\n{'='*70}")
print("ANALYSIS OF CYCLES NOT COVERED BY (0,0,0) EC")
print("=" * 70)

for n, ms_list, max_len in [
    (5, [2, 3, 2, 3, 2], 16),
    (7, [2, 3, 2, 3, 2, 3, 2], 22),
]:
    boundary_t = [t for t in range(n) if ms_list[t] == 3
                  and ms_list[(t-1)%n] == 2 and ms_list[(t+1)%n] == 2]

    words = enumerate_mover_words(ms_list, n, max_len)

    not_000_count = 0

    for word in words:
        cycle = build_cycle(ms_list, n, word)
        if cycle is None:
            continue

        ell = len(word)

        has_000_any = False
        for t in range(n):
            bL = (t - 1) % n
            bR = (t + 1) % n
            m000 = n000 = False
            for s in range(ell):
                ctx = (cycle[s][bL], cycle[s][t], cycle[s][bR])
                if ctx == (0, 0, 0):
                    if word[s] == t:
                        m000 = True
                    else:
                        n000 = True
            if m000 and n000:
                has_000_any = True
                break

        if has_000_any:
            continue

        not_000_count += 1
        if not_000_count <= 3:
            print(f"\n  n={n}, word={word}")
            # Find what EC exists
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
                overlap = mover & nonmover
                if overlap:
                    print(f"    proc {t} (m={ms_list[t]}): EC at {overlap}")

            # Show context trace for first mover at each proc
            print(f"    First mover of each proc:")
            for t in range(n):
                first_s = next((s for s in range(ell) if word[s] == t), None)
                if first_s is not None:
                    bL = (t - 1) % n
                    bR = (t + 1) % n
                    ctx = (cycle[first_s][bL], cycle[first_s][t], cycle[first_s][bR])
                    print(f"      proc {t}: step {first_s}, ctx={ctx}")

    print(f"\n  n={n}: {not_000_count} cycles NOT covered by (0,0,0)")


# FINAL: What's the SIMPLEST universal mechanism?
# Let's check: does every cycle have EC via SOME context (L, 0, R)?
# I.e., does every boundary ternary see SOME (L, 0, R) at both mover and nonmover?
print(f"\n{'='*70}")
print("LEVEL-ZERO EC: Does some (L, 0, R) always overlap?")
print("=" * 70)

for n, ms_list, max_len in [
    (5, [2, 3, 2, 3, 2], 16),
    (7, [2, 3, 2, 3, 2, 3, 2], 22),
]:
    boundary_t = [t for t in range(n) if ms_list[t] == 3
                  and ms_list[(t-1)%n] == 2 and ms_list[(t+1)%n] == 2]

    words = enumerate_mover_words(ms_list, n, max_len)

    total = 0
    level0_ec = 0

    for word in words:
        cycle = build_cycle(ms_list, n, word)
        if cycle is None:
            continue
        total += 1

        ell = len(word)
        has_l0_ec = False
        for t in range(n):  # Check ALL procs
            bL = (t - 1) % n
            bR = (t + 1) % n
            mover_l0 = set()
            nonmover_l0 = set()
            for s in range(ell):
                if cycle[s][t] == 0:  # Level 0
                    lr = (cycle[s][bL], cycle[s][bR])
                    if word[s] == t:
                        mover_l0.add(lr)
                    else:
                        nonmover_l0.add(lr)
            if mover_l0 & nonmover_l0:
                has_l0_ec = True
                break

        if has_l0_ec:
            level0_ec += 1

    print(f"\nn={n}: {total} cycles")
    print(f"  Level-0 EC at some proc: {level0_ec}/{total} ({100*level0_ec/total:.1f}%)")
