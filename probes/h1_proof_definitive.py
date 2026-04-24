#!/usr/bin/env python3
"""DEFINITIVE: (L,R) pair analysis at q for the proof."""
from collections import Counter

def build_configs(ms, n, word):
    L = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(L):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]: return None
    if len(set(configs[:L])) != L: return None
    return configs[:L]

def enumerate_good_cycles(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length: return
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

n = 5
ms = [2, 2, 2, 2, 3]
t = 4
q = 2; qL, qR = 1, 3

words = enumerate_good_cycles(ms, n, 20)

print("="*70)
print("NEIGHBOR FIRE COUNTS IN INTERVALS")
print("="*70)

nbr_fire_stats = Counter()

for word in words:
    configs = build_configs(ms, n, word)
    if configs is None: continue
    if not is_wrap_adjacent(word, n): continue
    L = len(word)
    fc = Counter(word)
    t_steps = [s for s in range(L) if word[s] == t]
    ft = len(t_steps)
    has_11 = False
    for idx in range(ft):
        k1 = t_steps[idx]
        k2 = t_steps[(idx+1)%ft]
        phase = []
        s = (k1+1)%L
        while s != k2:
            phase.append(s)
            s = (s+1)%L
        J = sum(1 for s in phase if word[s] == (t-1)%n)
        K = sum(1 for s in phase if word[s] == (t+1)%n)
        if J == 1 and K == 1: has_11 = True; break
    if not has_11: continue

    q_steps = sorted(s for s in range(L) if word[s] == q)
    if len(q_steps) != 2: continue
    s1, s2 = q_steps

    # Count neighbor fires in each interval
    i1_steps = []
    s = (s1+1)%L
    while s != s2:
        i1_steps.append(s)
        s = (s+1)%L

    i2_steps = []
    s = (s2+1)%L
    while s != s1:
        i2_steps.append(s)
        s = (s+1)%L

    i1_fL = sum(1 for s in i1_steps if word[s] == qL)
    i1_fR = sum(1 for s in i1_steps if word[s] == qR)
    i2_fL = sum(1 for s in i2_steps if word[s] == qL)
    i2_fR = sum(1 for s in i2_steps if word[s] == qR)

    # (L,R) pairs in each interval
    i1_lr = set()
    for s in i1_steps:
        i1_lr.add((configs[s][qL], configs[s][qR]))
    i2_lr = set()
    for s in i2_steps:
        i2_lr.add((configs[s][qL], configs[s][qR]))

    lr1 = (configs[s1][qL], configs[s1][qR])
    lr2 = (configs[s2][qL], configs[s2][qR])

    ovlp = (lr1 in i2_lr) or (lr2 in i1_lr)

    nbr_fire_stats[(i1_fL, i1_fR, i2_fL, i2_fR, len(i1_lr), len(i2_lr), ovlp)] += 1

print("(I1_fL, I1_fR, I2_fL, I2_fR, |I1_lr|, |I2_lr|, overlap): count")
for key, cnt in sorted(nbr_fire_stats.items()):
    print(f"  I1:fL={key[0]} fR={key[1]} I2:fL={key[2]} fR={key[3]} "
          f"|I1_lr|={key[4]} |I2_lr|={key[5]} ovlp={key[6]}: {cnt}")

# KEY: In each interval, both qL and qR fire.
# With 2 binary neighbors each firing k times:
# The (L,R) pair sequence starts at some value and flips L or R at each fire.
# This traces a path on the 2x2 grid {0,1}^2.
# The number of distinct (L,R) pairs = number of distinct vertices visited.

# If qL fires a times and qR fires b times in an interval:
# We visit a+b+1 vertices on the walk... but on {0,1}^2 = 4 vertices total.
# If a >= 1 and b >= 1: we visit at least 3 distinct pairs.
# (Start -> flip L -> flip R gives 3 distinct, or start -> flip R -> flip L gives 3.)
# If a >= 1 and b >= 1: AT LEAST 3 distinct (L,R) pairs in the interval.

# With 4 total possible pairs and >= 3 in each interval:
# |I1_lr| >= 3 and |I2_lr| >= 3. By pigeonhole: |I1_lr ∩ I2_lr| >= 3+3-4 = 2.
# The mover pair lr1 is some element of the 4-element set.
# lr1 could be in I2_lr or not. But with |I2_lr| >= 3 out of 4:
# probability lr1 ∈ I2_lr is at least 3/4... but we need certainty.

# Actually: lr1 is the (L,R) pair at the moment q fires (s1).
# At step s1: the config has already been determined by the walk.
# The START of I2 (step s2+1): lr starts at some specific pair.
# As the walk continues in I2, lr changes with each neighbor firing.
# The END of I2 (step s1): lr ends at lr1 (the config just before q fires).

# Wait! The (L,R) pair at the END of I2 IS lr1!
# Because I2 ends at step s1-1, and after that q fires at s1.
# The config at step s1 = config after step s1-1's mover fires.
# If word[s1-1] = qL: then at step s1-1, configs[s1-1][qL] was some value,
# and after firing: qL becomes (that+1)%2. So configs[s1][qL] differs from s1-1.
# But the (L,R) at the nonmover step s1-1 is (configs[s1-1][qL], configs[s1-1][qR]).
# And lr1 = (configs[s1][qL], configs[s1][qR]).
# These differ in the L component (if word[s1-1]=qL).

# So the LAST step of I2 has lr = predecessor of lr1 (one flip away).
# Not lr1 itself. So lr1 is NOT guaranteed to appear in I2.

# But with >=3 pairs in I2: lr1 might still be there.
# Actually with the walk visiting >=3 of 4 pairs,
# and lr1 being 1 of 4: lr1 might be the missing one.

# When is lr1 the missing pair? Only when I2 visits exactly {0,1}^2 \ {lr1}.
# That means lr1 is NOT visited as nonmover in I2, so no overlap from s1.
# Similarly, lr2 might not be in I1.

# But we need at least ONE of them. Let me check: can BOTH lr1 ∉ I2 and lr2 ∉ I1?

print("\n\nChecking: can both lr1 ∉ I2 and lr2 ∉ I1?")
both_miss = 0
for word in words:
    configs = build_configs(ms, n, word)
    if configs is None: continue
    if not is_wrap_adjacent(word, n): continue
    L = len(word)
    t_steps = [s for s in range(L) if word[s] == t]
    ft = len(t_steps)
    has_11 = False
    for idx in range(ft):
        k1 = t_steps[idx]
        k2 = t_steps[(idx+1)%ft]
        phase = []
        s = (k1+1)%L
        while s != k2:
            phase.append(s)
            s = (s+1)%L
        J = sum(1 for s in phase if word[s] == (t-1)%n)
        K = sum(1 for s in phase if word[s] == (t+1)%n)
        if J == 1 and K == 1: has_11 = True; break
    if not has_11: continue

    q_steps = sorted(s for s in range(L) if word[s] == q)
    if len(q_steps) != 2: continue
    s1, s2 = q_steps

    lr1 = (configs[s1][qL], configs[s1][qR])
    lr2 = (configs[s2][qL], configs[s2][qR])

    i1_lr = set()
    s = (s1+1)%L
    while s != s2:
        i1_lr.add((configs[s][qL], configs[s][qR]))
        s = (s+1)%L

    i2_lr = set()
    s = (s2+1)%L
    while s != s1:
        i2_lr.add((configs[s][qL], configs[s][qR]))
        s = (s+1)%L

    if lr1 not in i2_lr and lr2 not in i1_lr:
        both_miss += 1

print(f"Both miss: {both_miss} (should be 0)")
