#!/usr/bin/env python3
"""
Verify the EXACT mechanism for the proof.

Structure at q (all-binary, fc=2):
- q fires at s1 (value v->1-v) and s2 (value 1-v->v).
- Interval I1 (s1 to s2): q has value 1-v.
- Interval I2 (s2 to s1): q has value v.

From the data:
  Pattern 1: I1 has (fL=0, fR=3-4), I2 has (fL=2, fR=0-1).
  Pattern 2: I1 has (fL=2, fR=0-1), I2 has (fL=0, fR=3-4).

In Pattern 1:
  I1: qL stays fixed, qR flips 3-4 times.
  lr1 = (a, b) where a = qL_val (fixed in I2 too since qL fires 0 times before s1??)
  No wait: in I2, qL fires 2 times. So qL changes.

Hmm, let me recheck. The key is:
  In I1: fL=0 means qL doesn't fire, so L component at q is fixed = configs[s1+1][qL].
  After s1 fires (q changes), qL is unchanged = configs[s1][qL] (since only q changed at s1).
  So in I1: L component = configs[s1][qL] = a (call it).
  lr1 = (a, b) for some b.

In I2: qL fires 2 times. L component flips twice: starts at some value, returns to same.
  So in I2: L component visits old_val and 1-old_val.

The mover lr1 = (a, b). Does (a, b) appear in I2?
In I2: L component visits some value and its complement. The start of I2:
  After s2 fires: qL = configs[s2][qL] (unchanged at s2, since q fires).
  Does qL in I2 ever equal a?

Actually this is getting circular. Let me just verify the PROOF CLAIM:

CLAIM: the (L,R) pair at q's mover step always appears as a nonmover
(L,R) pair in the complementary interval (where q has the same own_value).

This is verified by "Both miss: 0" above. Now let me check if this extends
to n=7.
"""
from collections import Counter
from itertools import product as iproduct

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

# n=5 complete check: all {2,3} systems
n = 5
threshold = 4*3**(n-2)
print(f"n={n}, threshold={threshold}")

grand_total = 0
grand_ec = 0

for ms_tuple in iproduct([2,3], repeat=n):
    ms = list(ms_tuple)
    prod = 1
    for m in ms: prod *= m
    if prod >= threshold: continue
    binary = [p for p in range(n) if ms[p] == 2]
    if len(binary) < 3: continue
    sandwiched = [p for p in range(n) if ms[p]==3 and ms[(p-1)%n]==2 and ms[(p+1)%n]==2]
    if not sandwiched: continue

    canon = min(tuple(ms[i:]+ms[:i]) for i in range(n))
    if list(canon) != ms: continue

    words = enumerate_good_cycles(ms, n, 20)

    for word in words:
        configs = build_configs(ms, n, word)
        if configs is None: continue
        if not is_wrap_adjacent(word, n): continue
        L = len(word)

        has_11 = False
        for t in sandwiched:
            bL, bR = (t-1)%n, (t+1)%n
            t_steps = [s for s in range(L) if word[s] == t]
            for idx in range(len(t_steps)):
                k1 = t_steps[idx]
                k2 = t_steps[(idx+1)%len(t_steps)]
                phase = []
                s = (k1+1)%L
                while s != k2:
                    phase.append(s)
                    s = (s+1)%L
                J = sum(1 for s in phase if word[s] == bL)
                K = sum(1 for s in phase if word[s] == bR)
                if J == 1 and K == 1: has_11 = True; break
            if has_11: break
        if not has_11: continue

        grand_total += 1

        # Check EC at ANY proc
        has_ec = False
        for p in range(n):
            pL, pR = (p-1)%n, (p+1)%n
            mover, nonmover = set(), set()
            for s in range(L):
                ctx = (configs[s][pL], configs[s][p], configs[s][pR])
                if word[s] == p: mover.add(ctx)
                else: nonmover.add(ctx)
            if mover & nonmover:
                has_ec = True
                break
        if has_ec:
            grand_ec += 1
        else:
            print(f"*** EXCEPTION: ms={ms}, word={word}")

print(f"\nn={n} SUMMARY: {grand_total} cycles with (1,1), EC={grand_ec}, exceptions={grand_total - grand_ec}")
print(f"EC rate: {'100.0' if grand_total == grand_ec else f'{100*grand_ec/grand_total:.2f}'}%")
