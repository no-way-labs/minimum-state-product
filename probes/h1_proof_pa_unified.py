#!/usr/bin/env python3
"""
UNIFIED PROOF: (1,1) phase at sandwiched ternary -> EC.

The (1,1) phase means: between consecutive t-firings, bL fires once, bR fires once.
The walk must traverse from t through one side, around, and back through the other side.

Key structural fact: in a (1,1) phase, the walk visits bL once and bR once.
The walk goes: t -> (bL or bR) -> ... remote procs ... -> (bR or bL) -> t.
Call it "through-walk": the walk passes through t's neighborhood once in each direction.

Phase types (by direction):
Type L: t fires, then walk goes LEFT (bL fires), then remote, then RIGHT (bR fires), then t fires.
Type R: t fires, then walk goes RIGHT (bR fires), then remote, then LEFT (bL fires), then t fires.

In both types, the walk visits ALL remote procs (those not in {t, bL, bR}).
Each remote proc fires at least once between these visits.

The (1,1) phase structure forces a RETURN property on contexts:
When the walk traverses from one side to the other, the context at the
"crossing point" must appear in both the outgoing and incoming parts.

Let me verify: which proc has EC and why.
"""
from collections import Counter
from itertools import product as iproduct

def enumerate_good_cycles(ms, n, max_length=20):
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

def is_wrap_adjacent(word, n):
    return abs(word[-1] - word[0]) % n in (1, n-1)

n = 5
threshold = 4*3**(n-2)

# For each system: find the FIRST proc (by distance from t) where EC occurs.
# And understand the fc at that proc.
print("="*70)
print("EC LOCATION AND fc ANALYSIS (all {2,3} systems)")
print("="*70)

for ms_tuple in iproduct([2,3], repeat=n):
    ms = list(ms_tuple)
    prod = 1
    for m in ms: prod *= m
    if prod >= threshold: continue
    binary = [p for p in range(n) if ms[p] == 2]
    if len(binary) < 3: continue
    sandwiched = [p for p in range(n) if ms[p]==3 and ms[(p-1)%n]==2 and ms[(p+1)%n]==2]
    if not sandwiched: continue

    # Canonical check to avoid duplicates
    canon = min(tuple(ms[i:]+ms[:i]) for i in range(n))
    if list(canon) != ms: continue

    words = enumerate_good_cycles(ms, n, 20)

    # For each cycle with (1,1), find minimum-distance EC proc
    min_dist_ec = Counter()
    fc_at_min = Counter()

    for word in words:
        configs = build_configs(ms, n, word)
        if configs is None: continue
        if not is_wrap_adjacent(word, n): continue

        L = len(word)
        fc = Counter(word)

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
                if J == 1 and K == 1:
                    has_11 = True
                    break
            if has_11: break
        if not has_11: continue

        # Find EC procs
        best_dist = n
        best_proc = None
        for p in range(n):
            pL, pR = (p-1)%n, (p+1)%n
            mover, nonmover = set(), set()
            for s in range(L):
                ctx = (configs[s][pL], configs[s][p], configs[s][pR])
                if word[s] == p: mover.add(ctx)
                else: nonmover.add(ctx)
            if mover & nonmover:
                d = min(abs(p-t)%n for t in sandwiched)
                d = min(d, n-d)
                if d < best_dist:
                    best_dist = d
                    best_proc = p

        if best_proc is not None:
            min_dist_ec[(best_dist, ms[best_proc], ms[(best_proc-1)%n]*ms[best_proc]*ms[(best_proc+1)%n])] += 1
            fc_at_min[(best_dist, fc[best_proc])] += 1

    print(f"\nms={ms}")
    print(f"  Min-dist EC loc: {dict(min_dist_ec)}")
    print(f"  fc at min-dist EC: {dict(fc_at_min)}")

# The key insight: for n=5 alternating (2,3,2,3,2), the EC occurs at
# distance 1 (binary neighbor of t) or distance 0 (t itself).
# For n=5 with 4 binary, EC occurs at distance 2 (the all-binary proc).

# UNIFIED APPROACH:
# Instead of fixing a specific proc, prove that the TOTAL number of
# distinct contexts across all procs exceeds what's possible without EC.

print("\n" + "="*70)
print("TOTAL CONTEXT COUNTING across cycle")
print("="*70)

ms = [2, 3, 2, 3, 2]
sandwiched = [1, 3]
words = enumerate_good_cycles(ms, n, 20)

for word in words[:5]:
    configs = build_configs(ms, n, word)
    if configs is None: continue
    if not is_wrap_adjacent(word, n): continue
    L = len(word)
    fc = Counter(word)

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
            if J == 1 and K == 1:
                has_11 = True
                break
        if has_11: break
    if not has_11: continue

    print(f"\nword={word}, L={L}, fc={dict(fc)}")

    # For each proc: how many distinct mover + nonmover contexts?
    for p in range(n):
        pL, pR = (p-1)%n, (p+1)%n
        mover, nonmover = set(), set()
        for s in range(L):
            ctx = (configs[s][pL], configs[s][p], configs[s][pR])
            if word[s] == p: mover.add(ctx)
            else: nonmover.add(ctx)
        overlap = mover & nonmover
        cs = ms[pL]*ms[p]*ms[pR]
        only_mover = mover - nonmover
        only_nonmover = nonmover - mover
        print(f"  p={p} m={ms[p]} cs={cs} fc={fc[p]}: "
              f"|M|={len(mover)} |N|={len(nonmover)} |M&N|={len(overlap)} "
              f"|M-N|={len(only_mover)} |N-M|={len(only_nonmover)} "
              f"|M∪N|={len(mover|nonmover)}")
