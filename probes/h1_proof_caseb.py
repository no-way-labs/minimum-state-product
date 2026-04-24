#!/usr/bin/env python3
"""
Case B: ms=[2,3,2,3,2] (alternating). No all-binary-context proc.
Every binary has one ternary neighbor. ctx_space = 12 for all procs.

For EC at sandwiched ternary t: t fires fc(t) times.
Mover contexts at t: fc(t) appearances.
Non-mover contexts at t: L - fc(t) appearances.
ctx_space at t = 2*3*2 = 12.

The (1,1) phase creates 3 non-mover (L,R) pairs in each phase (see earlier analysis).
With fc(t) = 3: three phases, 3 mover contexts.
But mover and nonmover have different middle values, so they CAN match
only if the ternary's state returns to the same value.

Actually t is ternary (m=3). Its value cycles: 0->1->2->0.
Phase 1: t fires at value 0. Middle of phase = 1. Next t-fire at value 1.
Phase 2: t fires at value 1. Middle of phase = 2. Next t-fire at value 2.
Phase 3: t fires at value 2. Middle of phase = 0. Next t-fire at value 0.

Mover contexts: (a0, 0, b0), (a1, 1, b1), (a2, 2, b2).
Phase 1 nonmover: all have middle = 1.
Phase 2 nonmover: all have middle = 2.
Phase 3 nonmover: all have middle = 0.

EC at t: mover (a_i, i, b_i) matches nonmover (a, i, b) = (a_i, i, b_i)
in phase (i-1) mod 3 [which has middle value i].

Wait: phase k has middle value (k+1) mod 3.
Phase 0 (after value 0 firing): middle = 1. Next mover at value 1: ctx = (a1, 1, b1).
Nonmover in phase 0: middle = 1.
EC: (a1, 1, b1) in nonmover of phase 0? I.e., does the END-of-phase-0
context match the MOVER context of the next phase?

From earlier analysis: end of (1,1) phase has (1-a, x+1, 1-b) where
(a, x, b) was the START context at t's firing.

Mover at k1 (phase 0 start): (a0, 0, b0).
After t fires: middle becomes 1.
In phase 0: bL flips a0 -> 1-a0, bR flips b0 -> 1-b0.
End of phase 0 context at t: (1-a0, 1, 1-b0).
Mover at k2 (phase 1 start): (1-a0, 1, 1-b0).

So mctx at phase 1 = (1-a0, 1, 1-b0).
Nonmover in phase 0: all have middle = 1.
Non-mover (L,R) pairs in phase 0 include:
  (a0, b0), then after one side fires: (1-a0, b0) or (a0, 1-b0), then (1-a0, 1-b0).

Mover at k2 = (1-a0, 1, 1-b0) with (L,R) = (1-a0, 1-b0).
This IS one of the nonmover (L,R) pairs in phase 0!
Specifically, it's the pair AFTER both neighbors have fired.

But we showed earlier that this pair only appears at step k2 itself (the mover step),
because there's no gap between the last binary fire and t's next fire.

Wait: that was for ms=[2,3,2,3,2]. The last binary fires right before t.
At step k2-1 (which is the last binary fire):
  Context at t = (pre_last_L, 1, pre_last_R) which is one step away from (1-a0, 1, 1-b0).
At step k2: context = (1-a0, 1, 1-b0) = mover.

But earlier steps in phase 0 DID have (L,R) pairs that could match.
Actually wait: (1-a0, 1-b0) appears after BOTH bL and bR have fired.
If bL fires first at step u, bR fires at step v (v > u in phase):
  Steps after v (before k2): (L,R) = (1-a0, 1-b0). Non-mover context = (1-a0, 1, 1-b0).
  If there exists a step s with u < s < v: impossible, v is the last binary before k2.
  If there exists a step s with v < s < k2 where mover is not t:
  This would give (1-a0, 1, 1-b0) as nonmover. BUT v is the last step before k2.

So no intermediate step. The only appearance of (1-a0, 1, 1-b0) is at k2 itself.
But that's the MOVER context, not nonmover.

So in-phase EC at t does NOT work. Cross-phase EC requires:
(1-a0, 1, 1-b0) appears as nonmover at t in a DIFFERENT phase.
Phase 2 has middle = 2. Phase -1 (i.e., phase 2) has middle = 0.
Wait: nonmover middle = 1 only appears in phase 0.
(1-a0, 1, 1-b0) can only appear as nonmover in phase 0 (or any phase with middle 1).

Hmm, but multiple passes through the same middle value occur if fc(t) = 6.
With fc(t) = 6: six phases, two with each middle value.
EC could come from two different phases with the same middle.

But fc(t) = 3 is the minimum and most common case.

Let me check: for Case B with fc(t) = 3, does EC occur at t?
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

n = 5
ms = [2, 3, 2, 3, 2]
sandwiched = [1, 3]

words = enumerate_good_cycles(ms, n, 20)

print("="*70)
print("CASE B: EC at t analysis")
print("="*70)

ec_at_t = Counter()  # (fc_t, ec_at_this_t, ec_at_other) -> count

for word in words:
    configs = build_configs(ms, n, word)
    if configs is None: continue
    if not is_wrap_adjacent(word, n): continue
    L = len(word)
    fc = Counter(word)

    for t in sandwiched:
        bL, bR = (t-1)%n, (t+1)%n
        t_steps = [s for s in range(L) if word[s] == t]
        has_11 = False
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
        if not has_11: continue

        # Check EC at t
        mover_t = set()
        nonmover_t = set()
        for s in range(L):
            ctx = (configs[s][bL], configs[s][t], configs[s][bR])
            if word[s] == t: mover_t.add(ctx)
            else: nonmover_t.add(ctx)

        ec_t = bool(mover_t & nonmover_t)

        # Check EC at any other proc
        ec_other = False
        for p in range(n):
            if p == t: continue
            pL, pR = (p-1)%n, (p+1)%n
            mover, nonmover = set(), set()
            for s in range(L):
                ctx = (configs[s][pL], configs[s][p], configs[s][pR])
                if word[s] == p: mover.add(ctx)
                else: nonmover.add(ctx)
            if mover & nonmover:
                ec_other = True; break

        ec_at_t[(fc[t], ec_t, ec_other)] += 1

print("(fc_t, ec_at_t, ec_at_other): count")
for key, cnt in sorted(ec_at_t.items()):
    print(f"  fc_t={key[0]}, ec_at_t={key[1]}, ec_other={key[2]}: {cnt}")

# Check: when fc_t=3 and ec_at_t=False, is ec_other always True?
print("\nfc_t=3, no EC at t:")
for key, cnt in sorted(ec_at_t.items()):
    if key[0] == 3 and not key[1]:
        print(f"  ec_other={key[2]}: {cnt}")

# Where does ec_other occur?
print("\n\nWhere does ec_other occur when ec_at_t=False?")
ec_other_loc = Counter()

for word in words:
    configs = build_configs(ms, n, word)
    if configs is None: continue
    if not is_wrap_adjacent(word, n): continue
    L = len(word)
    fc = Counter(word)

    for t in sandwiched:
        bL, bR = (t-1)%n, (t+1)%n
        t_steps = [s for s in range(L) if word[s] == t]
        has_11 = False
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
        if not has_11: continue

        mover_t = set()
        nonmover_t = set()
        for s in range(L):
            ctx = (configs[s][bL], configs[s][t], configs[s][bR])
            if word[s] == t: mover_t.add(ctx)
            else: nonmover_t.add(ctx)
        if mover_t & nonmover_t: continue  # EC at t, skip

        # EC elsewhere
        for p in range(n):
            if p == t: continue
            pL, pR = (p-1)%n, (p+1)%n
            mover, nonmover = set(), set()
            for s in range(L):
                ctx = (configs[s][pL], configs[s][p], configs[s][pR])
                if word[s] == p: mover.add(ctx)
                else: nonmover.add(ctx)
            if mover & nonmover:
                dist = min(abs(p - t2) % n for t2 in sandwiched)
                dist = min(dist, n - dist)
                ec_other_loc[(p, ms[p], dist, fc[p])] += 1

print("(proc, m, dist_from_t, fc): count")
for key, cnt in sorted(ec_other_loc.items()):
    print(f"  p={key[0]} m={key[1]} dist={key[2]} fc={key[3]}: {cnt}")
