#!/usr/bin/env python3
"""
FINAL PROOF VERIFICATION

The proof has two structural cases:

CASE A: >=3 consecutive binary => exists binary q with all-binary neighbors.
  ctx_space(q) = 8. fc(q) is even (binary). If fc(q)=2: 2 mover + (L-2) nonmover.
  Distinct mover contexts <= 2, distinct nonmover contexts <= 8.
  Need overlap: at least one mover ctx = some nonmover ctx.

  Key lemma: fc(q) = 2 when the cycle has minimum firecount.
  Actually fc(q) can be > 2. Let's check.

CASE B: no 3 consecutive binary => alternating pattern.
  Every binary has exactly one ternary neighbor.
  EC occurs at other processors.

For both cases, the proof relies on the (1,1) phase constraining the cycle structure.

Let me verify the key claim: for cycles with (1,1) phase,
in Case A, the all-binary-context proc ALWAYS has EC.
"""
from collections import Counter
from itertools import product as iproduct

def enumerate_good_cycles(ms, n, max_length=20):
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

def is_wrap_adjacent(word, n):
    return abs(word[-1] - word[0]) % n in (1, n-1)

def find_phases_at_t(word, t, n):
    L = len(word)
    bL, bR = (t-1)%n, (t+1)%n
    t_steps = [s for s in range(L) if word[s] == t]
    if not t_steps: return []
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

# ===== CASE A VERIFICATION =====
print("="*70)
print("CASE A: All-binary-context proc always has EC")
print("="*70)

n = 5
threshold = 4*3**(n-2)

for ms_tuple in iproduct([2,3], repeat=n):
    ms = list(ms_tuple)
    prod = 1
    for m in ms: prod *= m
    if prod >= threshold: continue
    binary = [p for p in range(n) if ms[p] == 2]
    if len(binary) < 3: continue
    sandwiched = [p for p in range(n) if ms[p]==3 and ms[(p-1)%n]==2 and ms[(p+1)%n]==2]
    if not sandwiched: continue

    allbin = [p for p in range(n) if ms[p]==2 and ms[(p-1)%n]==2 and ms[(p+1)%n]==2]
    if not allbin: continue  # Case B

    words = enumerate_good_cycles(ms, n, 20)
    total_11 = 0
    ec_at_allbin = 0
    ec_not_at_allbin = 0

    # Track: fc(q), |mover_distinct|, |nonmover_distinct| at allbin procs
    fc_dist = Counter()

    for word in words:
        configs = build_configs(ms, n, word)
        if configs is None: continue
        if not is_wrap_adjacent(word, n): continue

        has_11 = any(any(J==1 and K==1 for J,K in find_phases_at_t(word, t, n)) for t in sandwiched)
        if not has_11: continue
        total_11 += 1

        L = len(word)
        fc = Counter(word)

        # Check EC at every allbin proc
        found_ec_allbin = False
        for q in allbin:
            qL, qR = (q-1)%n, (q+1)%n
            mover, nonmover = set(), set()
            for s in range(L):
                ctx = (configs[s][qL], configs[s][q], configs[s][qR])
                if word[s] == q: mover.add(ctx)
                else: nonmover.add(ctx)
            fc_dist[fc[q]] += 1
            if mover & nonmover:
                found_ec_allbin = True

        if found_ec_allbin:
            ec_at_allbin += 1
        else:
            ec_not_at_allbin += 1

    print(f"\nms={ms}, allbin={allbin}")
    print(f"  total_11={total_11}, ec_at_allbin={ec_at_allbin}, NOT={ec_not_at_allbin}")
    print(f"  fc distribution at allbin: {dict(fc_dist)}")

# ===== CASE B ANALYSIS: How does EC work without all-binary proc? =====
print("\n" + "="*70)
print("CASE B: No all-binary proc — EC mechanism analysis")
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

    allbin = [p for p in range(n) if ms[p]==2 and ms[(p-1)%n]==2 and ms[(p+1)%n]==2]
    if allbin: continue  # Case A

    words = enumerate_good_cycles(ms, n, 20)
    total_11 = 0
    ec_count = 0

    # For each proc type, track EC
    ec_by_proc = Counter()
    ec_by_type = Counter()
    fc_at_ec_proc = Counter()

    for word in words:
        configs = build_configs(ms, n, word)
        if configs is None: continue
        if not is_wrap_adjacent(word, n): continue

        has_11 = any(any(J==1 and K==1 for J,K in find_phases_at_t(word, t, n)) for t in sandwiched)
        if not has_11: continue
        total_11 += 1

        L = len(word)
        fc = Counter(word)

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
                ec_by_proc[p] += 1
                ptype = f"m{ms[p]}_ctx{ms[pL]*ms[p]*ms[pR]}"
                ec_by_type[ptype] += 1
                fc_at_ec_proc[(ptype, fc[p])] += 1

        if has_ec: ec_count += 1

    if total_11 > 0:
        print(f"\nms={ms}")
        print(f"  total_11={total_11}, ec={ec_count}")
        print(f"  EC by proc: {dict(ec_by_proc)}")
        print(f"  EC by type: {dict(ec_by_type)}")
        print(f"  FC at EC proc: {dict(fc_at_ec_proc)}")

# ===== KEY: Verify the walk adjacency constraint =====
# In a (1,1) phase: bL fires once, bR fires once.
# But who fires BETWEEN bL and bR? Other procs.
# The walk is on the ring graph: consecutive movers are ring-adjacent.
# From t, the walk goes to bL or bR, then continues on the ring.
# After bL fires, the walk must continue to bL-1 or bL+1=t.
# If to bL-1: the walk goes "away" from t.
# If to t: the walk comes back (but t can't fire twice in the same phase).
#
# In a (1,1) phase: the walk starts at t (fires), then traverses...
# Actually: the phase is between two t-firings. The walk during the phase
# passes through t's neighborhood. Since bL fires once and bR fires once,
# the walk visits bL and bR exactly once each.

print("\n" + "="*70)
print("WALK STRUCTURE IN (1,1) PHASES")
print("="*70)

ms = [2, 3, 2, 3, 2]  # Case B
t = 1
bL, bR = 0, 2

words = enumerate_good_cycles(ms, n, 20)
walk_patterns = Counter()

for word in words:
    configs = build_configs(ms, n, word)
    if configs is None: continue
    if not is_wrap_adjacent(word, n): continue
    L = len(word)
    t_steps = [s for s in range(L) if word[s] == t]
    for idx in range(len(t_steps)):
        k1 = t_steps[idx]
        k2 = t_steps[(idx+1) % len(t_steps)]
        phase = []
        s = (k1+1)%L
        while s != k2:
            phase.append(s)
            s = (s+1)%L
        J = sum(1 for s in phase if word[s] == bL)
        K = sum(1 for s in phase if word[s] == bR)
        if J != 1 or K != 1: continue

        movers = tuple(word[s] for s in phase)
        walk_patterns[movers] += 1

print(f"Walk patterns in (1,1) phases at t={t} (ms={ms}):")
for pattern, cnt in sorted(walk_patterns.items(), key=lambda x: -x[1]):
    print(f"  {pattern}: {cnt}")
