#!/usr/bin/env python3
"""
Deep proof mechanism analysis.

For Case A (all-binary-context proc q exists):
- q is binary, both neighbors binary. ctx_space = 2x2x2 = 8.
- fc(q) = 2 (minimum for binary).
- q fires twice as mover: 2 distinct mover contexts.
- q appears L-2 times as nonmover.
- Need to show: at least one mover context also appears as nonmover.

Key question: WHY must a mover context repeat as nonmover?
The mover contexts at q are (L_val, q_val, R_val) when q fires.
Between q's two firings, q's value changes: 0->1 or 1->0.
So the two mover contexts differ in the q_val component.

Non-mover contexts: q_val is fixed between firings of q.
Between q's first and second firing, q_val = (new value after first firing).
q's LEFT and RIGHT neighbors change as THEY fire.

For the (1,1) phase to matter: the (1,1) phase at the sandwiched ternary t
constrains the firing pattern of t's neighbors, which propagates to constrain
the contexts at q.

Let me trace the exact mechanism.
"""
from collections import Counter, defaultdict
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
        phases.append((J, K, steps))
    return phases

# Focus on ms=[2,2,2,2,3] with q=1 or q=2 (all-binary)
n = 5
ms = [2, 2, 2, 2, 3]
t = 4  # sandwiched ternary
bL, bR = 3, 0  # binary neighbors of t

print("="*70)
print(f"DETAILED PROOF MECHANISM: ms={ms}, t={t}, bL={bL}, bR={bR}")
print("="*70)
print(f"All-binary procs: 1, 2")
print(f"Context space at 1: 2x2x2=8, at 2: 2x2x2=8")
print()

words = enumerate_good_cycles(ms, n, 20)

# For each (1,1) cycle, trace the proof mechanism at q=2
# (q=2 has neighbors 1 and 3, all binary)
q = 2
qL, qR = 1, 3

sample_count = 0
for word in words:
    configs = build_configs(ms, n, word)
    if configs is None:
        continue
    if not is_wrap_adjacent(word, n):
        continue

    phases = find_phases_at_t(word, t, n)
    if not any(J==1 and K==1 for (J,K,_) in phases):
        continue

    L = len(word)
    fc = Counter(word)

    # Find q's firing steps
    q_steps = [s for s in range(L) if word[s] == q]

    # Mover contexts at q
    mover_ctxs = [(configs[s][qL], configs[s][q], configs[s][qR]) for s in q_steps]

    # Non-mover contexts at q
    nonmover_ctxs = [(configs[s][qL], configs[s][q], configs[s][qR])
                     for s in range(L) if word[s] != q]

    overlap = set(mover_ctxs) & set(nonmover_ctxs)

    if sample_count < 5:
        print(f"word={word}, L={L}, fc(q)={fc[q]}")
        print(f"  q fires at steps: {q_steps}")
        print(f"  mover contexts: {mover_ctxs}")
        print(f"  nonmover contexts (distinct): {sorted(set(nonmover_ctxs))}")
        print(f"  overlap: {overlap}")

        # Trace what happens between q's firings
        for i in range(len(q_steps)):
            s1 = q_steps[i]
            s2 = q_steps[(i+1) % len(q_steps)]
            print(f"\n  Between q-fire at {s1} and {s2}:")
            print(f"    After q fires at {s1}: q goes {configs[s1][q]} -> {configs[(s1+1)%L][q]}")
            s = (s1+1) % L
            while s != s2:
                ctx = (configs[s][qL], configs[s][q], configs[s][qR])
                is_nm = word[s] != q
                print(f"    step {s}: mover={word[s]}, config[q-1..q+1]={ctx}, "
                      f"{'NONMOVER at q' if is_nm else 'MOVER at q'}")
                s = (s+1)%L
            ctx = (configs[s2][qL], configs[s2][q], configs[s2][qR])
            print(f"    step {s2}: MOVER at q, ctx={ctx}")

        print()
        sample_count += 1

# Now the key structural analysis
print("="*70)
print("KEY STRUCTURAL ANALYSIS: Why does overlap occur?")
print("="*70)

# For binary q with fc(q)=2:
# q fires at steps s1 and s2.
# After s1: q_val flips (0->1 or 1->0).
# After s2: q_val flips back.
#
# Mover context at s1: (a, v, b) where v = q_val before first fire
# Mover context at s2: (c, 1-v, d) where 1-v = q_val before second fire
#
# Between s1 and s2: q_val = 1-v (constant).
# Non-mover contexts during this interval have form (*, 1-v, *)
#
# Between s2 and s1 (next period): q_val = v (constant).
# Non-mover contexts during this interval have form (*, v, *)
#
# So mover context at s1 has middle value v -> non-movers in interval [s2, s1) also have v.
# mover context at s2 has middle value 1-v -> non-movers in interval [s1, s2) also have 1-v.
#
# For overlap: need some non-mover ctx (a, v, b) = mover ctx at s1 = (a', v, b')
# with same L and R values. I.e., q's left and right neighbors have same values
# at step s1 (when q fires) AND at some non-mover step in [s2, s1).

# Count: how many distinct (L, R) pairs appear in each interval?
print("\n(L,R) pair analysis at q:")

lr_stats = defaultdict(list)

for word in words:
    configs = build_configs(ms, n, word)
    if configs is None:
        continue
    if not is_wrap_adjacent(word, n):
        continue
    phases = find_phases_at_t(word, t, n)
    if not any(J==1 and K==1 for (J,K,_) in phases):
        continue

    L = len(word)
    fc = Counter(word)
    q_steps = [s for s in range(L) if word[s] == q]
    assert fc[q] == 2  # binary, should fire exactly 2 times

    s1, s2 = q_steps[0], q_steps[1]

    # Interval 1: (s1, s2) -- q_val = 1-v
    interval1 = []
    s = (s1+1) % L
    while s != s2:
        interval1.append(s)
        s = (s+1) % L

    # Interval 2: (s2, s1) -- q_val = v
    interval2 = []
    s = (s2+1) % L
    while s != s1:
        interval2.append(s)
        s = (s+1) % L

    # LR pairs at mover steps
    lr_s1 = (configs[s1][qL], configs[s1][qR])
    lr_s2 = (configs[s2][qL], configs[s2][qR])

    # LR pairs at non-mover steps in interval 2 (same q_val as s1)
    lr_interval2 = set()
    for s in interval2:
        if word[s] != q:
            lr_interval2.add((configs[s][qL], configs[s][qR]))

    # Does lr_s1 appear in interval 2?
    overlap_from_s1 = lr_s1 in lr_interval2

    # LR pairs at non-mover steps in interval 1 (same q_val as s2)
    lr_interval1 = set()
    for s in interval1:
        if word[s] != q:
            lr_interval1.add((configs[s][qL], configs[s][qR]))

    overlap_from_s2 = lr_s2 in lr_interval1

    lr_stats[(len(lr_interval1), len(lr_interval2))].append(
        (overlap_from_s1, overlap_from_s2, lr_s1, lr_s2, len(interval1), len(interval2))
    )

print(f"\n(|LR_int1|, |LR_int2|) distribution:")
for key in sorted(lr_stats.keys()):
    entries = lr_stats[key]
    both = sum(1 for e in entries if e[0] and e[1])
    s1_only = sum(1 for e in entries if e[0] and not e[1])
    s2_only = sum(1 for e in entries if not e[0] and e[1])
    neither = sum(1 for e in entries if not e[0] and not e[1])
    print(f"  |LR_int1|={key[0]}, |LR_int2|={key[1]}: {len(entries)} cycles. "
          f"both={both}, s1_only={s1_only}, s2_only={s2_only}, NEITHER={neither}")
    if neither > 0:
        print(f"    *** COUNTEREXAMPLE to LR pigeonhole at q ***")
        for e in entries[:3]:
            if not e[0] and not e[1]:
                print(f"      lr_s1={e[2]}, lr_s2={e[3]}, int1_len={e[4]}, int2_len={e[5]}")
