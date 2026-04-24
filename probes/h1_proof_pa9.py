#!/usr/bin/env python3
"""
Proof mechanism: Why does (L,R) pair at mover step appear in complementary interval?

Binary q with all-binary neighbors:
- q fires at steps s1, s2 with fc(q)=2.
- Mover ctx at s1: (a, v, b) -> after fire, q becomes 1-v.
- Mover ctx at s2: (c, 1-v, d) -> after fire, q becomes v.
- Interval I1 = (s1, s2): q = 1-v. Non-mover (L,R) pairs in {0,1}^2.
- Interval I2 = (s2, s1): q = v. Non-mover (L,R) pairs in {0,1}^2.

For EC: need (a, v, b) in nonmover of I2, or (c, 1-v, d) in nonmover of I1.
I.e., need (a, b) ∈ LR(I2) or (c, d) ∈ LR(I1).

Claim: (a, b) ∈ LR(I2) always.

Why? Consider what happens between s2 and s1 (interval I2).
At step s2+1: q just fired, neighbors unchanged.
  - q's left neighbor has value c' (whatever it was at s2 but shifted if it fired)
  - q's right neighbor has value d' (similarly)

Actually, the key is the INITIAL and FINAL states of the interval.

Let me think about it from the cycle structure:
- Step s1: q fires. Config just BEFORE: q-1 = a, q = v, q+1 = b.
- Step s1+1: q = 1-v. Neighbors unchanged from step s1 (only q changed).
  So just after s1: (a, 1-v, b).
- Steps in I1: neighbors may change.
- Step s2: q fires. Config just BEFORE: q-1 = c, q = 1-v, q+1 = d.

So in I1, we start with neighbor values (a, b) and end with (c, d).
The neighbors change as their processors fire.

- Step s2+1: q = v. Just after: (c, v, d). Only q changed.
  But wait: at step s2, q is the mover, so neighbors are still (c, d).
  After q fires: (c, v, d). This is the first config of I2.

- Steps in I2: neighbors may change.
- Step s1 (next period): config is (a, v, b) again (cycle returns).

So I2 starts with neighbor pair (c, d) and ends with (a, b).
Therefore at the LAST step of I2 (just before s1), the neighbor pair is (a, b).
And at that step, q = v (unchanged in I2). So the non-mover context is (a, v, b).

But wait -- is the step just before s1 actually IN I2?
I2 = {s2+1, s2+2, ..., s1-1} (all steps where q doesn't fire).
The step s1-1 is in I2 (it's the step right before q fires at s1).
At step s1-1, the mover is word[s1-1] ≠ q (since q fires at s1, not s1-1).

But at step s1-1, the config may not be (a, v, b) yet!
The config at step s1 is (a, v, b). But between step s1-1 and s1,
the mover at step s1-1 fires. If the mover at s1-1 is neither q-1 nor q+1,
then (q-1, q, q+1) is unchanged, so at step s1-1 the context IS (a, v, b).

But if the mover at s1-1 is q-1 or q+1, then one neighbor changes
between step s1-1 and step s1. Let me think...

Config at step s1: (a, v, b) [the values at positions q-1, q, q+1]
Mover at step s1 is q. But what was mover at step s1-1?
If mover at s1-1 is q-1: then q-1 changed at step s1-1.
  Config at s1-1: (..., a', v, b) where a' is the OLD value of q-1.
  After mover q-1 fires: q-1 becomes a. So at step s1: (a, v, b).
  The non-mover context at q during step s1-1 is (a', v, b) ≠ (a, v, b) in general.

Hmm, this means the argument "config just before s1 is (a,v,b)" doesn't directly work.

BUT: mover at step s1-1 can only be q-1 or q+1 (since movers are adjacent
in the walk). The mover at s1 is q, so mover at s1-1 is a neighbor of q
on the ring (since walk steps are between adjacent processors).

So: the step BEFORE q fires, the mover is one of q's two neighbors.
This means at step s1-1, one of q's neighbors is about to change.

Actually wait -- movers in the walk are ring-adjacent. So word[s1] = q
means word[s1-1] ∈ {q-1, q+1}. Let's say word[s1-1] = q-1.

Then at step s1-1: mover is q-1. Config at step s1-1 has q-1 = a-1 (mod 2)
(since q-1 fires, incrementing). After firing: q-1 = a. So config at s1
has q-1 = a. Correct.

At step s1-1: non-mover context at q is (a-1 mod 2, v, b) = (1-a, v, b).
This is NOT the same as the mover context at s1 = (a, v, b).

So we can't just use "the step before s1". We need to look deeper into I2.

Let me find a step in I2 where the context IS (a, v, b).
"""
from collections import Counter

def build_configs(ms, n, word):
    L = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(L):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:L])) != L:
        return None
    return configs[:L]

def enumerate_good_cycles(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
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

def is_wrap_adjacent(word, n):
    return abs(word[-1] - word[0]) % n in (1, n-1)

def find_phases_at_t(word, t, n):
    L = len(word)
    bL, bR = (t-1)%n, (t+1)%n
    t_steps = [s for s in range(L) if word[s] == t]
    if not t_steps:
        return []
    phases = []
    for idx in range(len(t_steps)):
        s1 = t_steps[idx]
        s2 = t_steps[(idx+1)%len(t_steps)]
        steps = []
        s = (s1+1)%L
        while s != s2:
            steps.append(s)
            s = (s+1)%L
        J = sum(1 for s in steps if word[s] == bL)
        K = sum(1 for s in steps if word[s] == bR)
        phases.append((J, K))
    return phases

n = 5
ms = [2, 2, 2, 2, 3]
t = 4
q = 2
qL, qR = 1, 3

words = enumerate_good_cycles(ms, n, 20)

print("="*70)
print("RETURN-TO-START ANALYSIS")
print("="*70)

# For each cycle: check whether the INITIAL (L,R) at start of I2
# (which is (c,d)) eventually returns to (a,b) during I2.
# And at what step.

for word in words[:50]:
    configs = build_configs(ms, n, word)
    if configs is None:
        continue
    if not is_wrap_adjacent(word, n):
        continue
    phases = find_phases_at_t(word, t, n)
    if not any(J==1 and K==1 for (J,K) in phases):
        continue

    L = len(word)
    fc = Counter(word)
    q_steps = [s for s in range(L) if word[s] == q]
    if fc[q] != 2:
        continue

    s1, s2 = q_steps[0], q_steps[1]
    v = configs[s1][q]  # q's value when it first fires

    # Mover context at s1: (a, v, b)
    a = configs[s1][qL]
    b = configs[s1][qR]
    mctx1 = (a, v, b)

    # Build I2 non-mover contexts
    i2_steps = []
    s = (s2 + 1) % L
    while s != s1:
        i2_steps.append(s)
        s = (s + 1) % L

    # Check each step in I2
    found = False
    for s in i2_steps:
        if word[s] != q:
            ctx = (configs[s][qL], configs[s][q], configs[s][qR])
            if ctx == mctx1:
                # How many steps before s1?
                dist_to_s1 = (s1 - s) % L
                found = True
                break

    if not found:
        print(f"*** NOT FOUND: word={word}, s1={s1}, s2={s2}, mctx1={mctx1}")
        print(f"  I2 contexts:")
        for s in i2_steps:
            ctx = (configs[s][qL], configs[s][q], configs[s][qR])
            mover = word[s]
            print(f"    step {s}: mover={mover}, ctx@q={ctx}")

# Now check: for ALL {2,3} systems, ALL (1,1) cycles, does the overlap
# mechanism work at SOME proc with all-binary context?
# Or does the proof need the no-all-binary case too?
print("\n\n" + "="*70)
print("CASE B: systems with NO all-binary-context proc")
print("="*70)

for ms_tuple in [(2,2,3,2,3), (2,3,2,2,3), (2,3,2,3,2), (3,2,2,3,2), (3,2,3,2,2)]:
    ms = list(ms_tuple)
    binary = [p for p in range(n) if ms[p] == 2]
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]
    binary_allbinary = [p for p in binary if ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]

    if binary_allbinary:
        continue  # only interested in Case B

    print(f"\nms={ms}, binary={binary}, sandwiched={sandwiched}")
    print(f"  No all-binary-context proc exists!")

    words = enumerate_good_cycles(ms, n, 20)
    total_11 = 0
    total_ec = 0

    # WHERE does EC occur?
    ec_by_proc_type = Counter()

    for word in words:
        configs = build_configs(ms, n, word)
        if configs is None:
            continue
        if not is_wrap_adjacent(word, n):
            continue
        has_11 = any(any(J==1 and K==1 for J,K in find_phases_at_t(word, t2, n))
                     for t2 in sandwiched)
        if not has_11:
            continue

        total_11 += 1
        for p in range(n):
            pL, pR = (p-1)%n, (p+1)%n
            mover, nonmover = set(), set()
            for s in range(len(word)):
                ctx = (configs[s][pL], configs[s][p], configs[s][pR])
                if word[s] == p:
                    mover.add(ctx)
                else:
                    nonmover.add(ctx)
            if mover & nonmover:
                ptype = f"m{ms[p]}_nbrs_{ms[pL]}_{ms[pR]}"
                ec_by_proc_type[ptype] += 1

        # Global EC
        has_ec = False
        for p in range(n):
            pL, pR = (p-1)%n, (p+1)%n
            mover, nonmover = set(), set()
            for s in range(len(word)):
                ctx = (configs[s][pL], configs[s][p], configs[s][pR])
                if word[s] == p:
                    mover.add(ctx)
                else:
                    nonmover.add(ctx)
            if mover & nonmover:
                has_ec = True
                break
        if has_ec:
            total_ec += 1

    print(f"  cycles with (1,1): {total_11}, with EC: {total_ec}")
    print(f"  EC by proc type: {dict(ec_by_proc_type)}")
