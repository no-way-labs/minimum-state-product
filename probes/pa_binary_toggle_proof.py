#!/usr/bin/env python3
"""PA: The Binary Toggle EC — understanding the exact mechanism.

KEY OBSERVATION: Every good cycle starts at config (0,0,...,0).
Binary proc b has value 0 at step 0. At any step s, b's value is
fc_b(s) mod 2, where fc_b(s) = number of times b has fired by step s.

For a boundary ternary t between binary bL, bR:
At step s: context(t) = (fc_bL(s) mod 2, fc_t(s) mod 3, fc_bR(s) mod 2)

When t fires at step s: t sees context (L, S, R) and produces S' = (S+1) mod 3.
At a nonmover step s where word[s] != t: t sees the SAME context (L, S, R) but
it stays S.

EC = exists step s1 (mover) and step s2 (nonmover) with same (L, S, R).

The constraint: L = fc_bL(s) mod 2, S = fc_t(s) mod 3, R = fc_bR(s) mod 2.

For all configs distinct: the TUPLE (fc_0(s) mod m_0, ..., fc_{n-1}(s) mod m_n)
is distinct for each step s.

CRUCIAL INSIGHT: At the all-zero config (step 0), the context of EVERY proc is
(0, 0, 0). This is a nonmover step for all procs except the first mover.
If t fires at some step s' with context (0, 0, 0), then EC at t.

When does t see (0,0,0) as mover? When fc_bL(s') mod 2 = 0, fc_t(s') mod 3 = 0,
fc_bR(s') mod 2 = 0. I.e., at a "return" to the starting L,S,R pattern.

For M_t = 1: t fires 3 times. The contexts at firings are at S=0, S=1, S=2.
At S=0: fc_t mod 3 = 0. This happens at the FIRST firing of t in each 3-cycle.
If at that first firing, bL and bR also have even fire counts → (0,0,0) context.

But step 0 is a nonmover for t (unless t fires first). So (0,0,0) is in
nonmover. If t also sees (0,0,0) as mover → EC.

The question: MUST t see (0,0,0) as mover?
Not necessarily. The first firing of t could have bL already fired odd times.

Let me check: how often does each boundary ternary see (0,0,0) as mover?
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


# Focus: what SPECIFIC contexts cause EC?
print("=" * 70)
print("WHICH CONTEXTS CAUSE EC AT BOUNDARY TERNARY?")
print("=" * 70)

for n, ms_list, max_len in [
    (7, [2, 3, 2, 3, 2, 3, 2], 22),
]:
    boundary_t = [t for t in range(n) if ms_list[t] == 3
                  and ms_list[(t-1)%n] == 2 and ms_list[(t+1)%n] == 2]

    words = enumerate_mover_words(ms_list, n, max_len)

    ec_ctx_freq = Counter()

    for word in words:
        cycle = build_cycle(ms_list, n, word)
        if cycle is None:
            continue

        ell = len(word)
        for t in boundary_t:
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
            for ctx in overlap:
                ec_ctx_freq[ctx] += 1

    print(f"\nn={n}: EC-causing contexts at boundary ternary:")
    for ctx, cnt in ec_ctx_freq.most_common():
        print(f"  {ctx}: {cnt} occurrences")


# Now: the REAL proof mechanism.
# For the ENTIRE RING, consider the config (0,...,0).
# At step 0, the config is (0,...,0). This is a nonmover step for
# all procs EXCEPT word[0].
# The cycle MUST return through this config.
# So word[0] fires at step 0, changing config[word[0]] to 1.
# At the last step (ell-1), the next config would be (0,...,0) again.
# So step ell-1 changes some proc back to 0.
# Step ell-1 has config = apply^{-1}((0,...,0)) at word[ell-1].

# The key: at step 0, config = (0,...,0). Every non-firing proc
# sees context (0, 0, 0). In particular, all boundary ternary
# that don't fire at step 0 see (0, 0, 0) as nonmover.

# If ANY boundary ternary t also sees (0, 0, 0) at some mover step → EC.
# t sees (0, 0, 0) as mover when: bL-value = 0, t-value = 0, bR-value = 0.
# This means bL and bR have fired even times, and t has fired 0 or 3 or 6... times.

# For M=1: t's value returns to 0 after 3 firings (the last firing).
# At the last t-firing: bL has fired fc_bL times total, bR fc_bR times.
# fc_bL is even (fc_bL = 2*K_bL), fc_bR is even. So bL-value = 0, bR-value = 0.
# Context at last t-firing = (0, 2, 0)! Not (0, 0, 0). Because t-value
# at that step is 2 (t fires from 2 to 0).

# Wait: at step s where t fires for the 3rd time:
# - t's value at step s is 2 (it's about to become 0)
# - context is (bL_val, 2, bR_val)
# So the mover context is (*, 2, *), not (*, 0, *).

# For the 1st t-firing: t's value is 0 → mover context is (*, 0, *).
# For the 2nd: t's value is 1 → (*, 1, *).
# For the 3rd: t's value is 2 → (*, 2, *).

# So the mover's S=0 context: (bL_at_fire1, 0, bR_at_fire1).
# If bL and bR haven't fired yet at fire1: mover ctx = (0, 0, 0).
# This matches the nonmover (0, 0, 0) at step 0 → EC!

# When can this fail? When t fires BEFORE both bL and bR have their
# first firing. Or when bL or bR fires BEFORE t's first firing,
# changing their values from 0.

# So: if word[0] = t, then t fires first, seeing (0, 0, 0) as mover.
# But then step 0 is a mover step for t, not a nonmover. However,
# does (0, 0, 0) appear elsewhere as nonmover?

# Actually: config = (0,...,0) appears at step 0 only (configs are distinct).
# At step 0, word[0] fires. For t != word[0], step 0 is nonmover with ctx (0,0,0).
# For t = word[0], step 0 is mover with ctx (0,0,0).

# With >=3 boundary ternary and the mover word visiting at most 2 neighbors
# of the first proc, at least 1 boundary ternary does NOT fire at step 0.
# That one sees (0,0,0) as nonmover at step 0.

# And: does it also see (0,0,0) as mover? When it fires at S=0 level
# with both binary neighbors at value 0.

# This happens when t fires its first time with bL_val=0 and bR_val=0.
# I.e., bL and bR have both fired an EVEN number of times before t's first firing.
# If they haven't fired at all (0 times, which is even): → mover (0,0,0) → EC!

# So the question becomes: is there ALWAYS a boundary ternary t such that
# both its binary neighbors haven't fired before t's first firing?

# This is a question about the mover word's PREFIX.

print(f"\n{'='*70}")
print("PREFIX ANALYSIS: Before first firing of each boundary ternary")
print("=" * 70)

for n, ms_list, max_len in [
    (5, [2, 3, 2, 3, 2], 16),
    (7, [2, 3, 2, 3, 2, 3, 2], 22),
]:
    boundary_t = [t for t in range(n) if ms_list[t] == 3
                  and ms_list[(t-1)%n] == 2 and ms_list[(t+1)%n] == 2]

    words = enumerate_mover_words(ms_list, n, max_len)
    print(f"\nn={n}, boundary_t={boundary_t}")

    always_some_clean = 0
    never_clean = 0
    total = 0

    for word in words:
        cycle = build_cycle(ms_list, n, word)
        if cycle is None:
            continue
        total += 1

        # For each boundary ternary, check: at its first firing,
        # have both binary neighbors fired 0 times (both even)?
        has_clean_t = False
        for t in boundary_t:
            bL = (t - 1) % n
            bR = (t + 1) % n

            # Find first firing of t
            first_t_step = None
            for s in range(len(word)):
                if word[s] == t:
                    first_t_step = s
                    break

            if first_t_step is None:
                continue

            # Count bL and bR firings before first_t_step
            bL_fires = sum(1 for s in range(first_t_step) if word[s] == bL)
            bR_fires = sum(1 for s in range(first_t_step) if word[s] == bR)

            if bL_fires % 2 == 0 and bR_fires % 2 == 0:
                has_clean_t = True
                # Verify: mover context at first firing should be (0,0,R) or similar
                # Actually (bL_fires%2, 0, bR_fires%2) = (0, 0, 0)
                ctx = (cycle[first_t_step][bL], cycle[first_t_step][t], cycle[first_t_step][bR])
                assert ctx == (0, 0, 0), f"Expected (0,0,0) but got {ctx}"

        if has_clean_t:
            always_some_clean += 1
        else:
            never_clean += 1

    print(f"  Cycles with some clean first-firing: {always_some_clean}/{total} ({100*always_some_clean/total:.1f}%)")
    print(f"  Cycles with NO clean first-firing: {never_clean}/{total}")

    # For the "no clean" cases: they still must have EC. Via what?
    if never_clean > 0:
        print(f"\n  Analyzing {never_clean} non-clean cycles:")
        count = 0
        for word in words:
            cycle = build_cycle(ms_list, n, word)
            if cycle is None:
                continue

            has_clean = False
            for t in boundary_t:
                bL = (t - 1) % n
                bR = (t + 1) % n
                first_t_step = None
                for s in range(len(word)):
                    if word[s] == t:
                        first_t_step = s
                        break
                if first_t_step is None:
                    continue
                bL_fires = sum(1 for s in range(first_t_step) if word[s] == bL)
                bR_fires = sum(1 for s in range(first_t_step) if word[s] == bR)
                if bL_fires % 2 == 0 and bR_fires % 2 == 0:
                    has_clean = True

            if has_clean:
                continue

            count += 1
            if count <= 3:
                # Show which procs fire before each boundary ternary
                ell = len(word)
                print(f"\n    word={word}")
                for t in boundary_t:
                    first_t = next(s for s in range(ell) if word[s] == t)
                    prefix = word[:first_t]
                    bL = (t - 1) % n
                    bR = (t + 1) % n
                    bL_f = sum(1 for p in prefix if p == bL)
                    bR_f = sum(1 for p in prefix if p == bR)
                    print(f"    t={t}: first at step {first_t}, prefix fires: bL({bL})={bL_f}, bR({bR})={bR_f}")

                # Check EC location
                for p in range(n):
                    bL = (p - 1) % n
                    bR = (p + 1) % n
                    mover = set()
                    nonmover = set()
                    for s in range(ell):
                        ctx = (cycle[s][bL], cycle[s][p], cycle[s][bR])
                        if word[s] == p:
                            mover.add(ctx)
                        else:
                            nonmover.add(ctx)
                    if mover & nonmover:
                        print(f"    EC at proc {p} (m={ms_list[p]}): overlap={mover & nonmover}")
