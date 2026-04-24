#!/usr/bin/env python3
"""PA: The Walk Constraint Proof.

THE KEY THEOREM:

For n >= 5, >=3 non-consecutive binary, sub-threshold product,
every good cycle has entry conflict.

PROOF STRUCTURE:

Lemma 1 (Boundary Ternary EC for long arcs):
If there exists a "boundary ternary" t adjacent to binary b, with the OTHER
neighbor of t being ternary (not sandwiched), and cycle length ell >= 2n:
then EC at t or at the ternary-ternary boundary.

This is already proved by phase-dispatch + existing mechanisms.

Lemma 2 (Sandwiched Ternary EC):
If t is sandwiched between binary bL, bR (both binary), M_t = 1:
EC at t iff mover's (L,R) pair at each S-level hits nonmover's (L,R) set.

From the data:
- At n=5 (fully alternating [2,3,2,3,2]):
  24 cycles (out of 1830) dodge EC at ALL boundary ternary.
  But these always have EC at a binary proc (always proc 0).

- At n=7 (fully alternating [2,3,2,3,2,3,2]):
  0 cycles dodge EC at boundary ternary. 100% EC.

- At n=7 (non-alternating [2,3,2,3,2,3,3]):
  100% EC at adj-to-binary ternary. 360,556 cycles.

DISCOVERY: The difference between n=5 and n=7 is the NUMBER of boundary
ternary procs. At n=5 (alternating): 2 sandwiched ternary.
At n=7 (alternating): 3 sandwiched ternary.

With 3+ sandwiched ternary, the collective constraint forces EC.
With only 2, rare dodges are possible (but EC still exists at binary).

PROOF IDEA (for n >= 7, >= 3 sandwiched ternary):
Each sandwiched ternary t_i has context space {0,1}x{0,1,2}x{0,1}.
Mover uses 3 slots, nonmover uses the rest.
For no-EC at t_i: mover must pick (L,R) pairs that nonmover misses.
With 3 ternary procs, this requires 3 simultaneous dodges.
The dodges are CORRELATED through the shared binary proc between them.

If t1 and t2 share a binary neighbor b:
- At t1: b is the R-neighbor. Mover's R at S=0 level is b-value at t1's firing.
- At t2: b is the L-neighbor. Mover's L at S=0 level is b-value at t2's firing.
But t1 and t2 fire at DIFFERENT times. The b-value changes between them.

The constraint: b fires 2K times total. These firings distribute across
t1's phases and t2's phases. The parity of b-firings before each t-firing
determines the b-value at that step.

Let me trace this precisely for the 3-sandwiched case.
"""
from collections import Counter, defaultdict
import itertools


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


# n=5 dodge analysis
n = 5
ms = [2, 3, 2, 3, 2]
max_len = 16
boundary_t = [1, 3]

words = enumerate_mover_words(ms, n, max_len)

print("=" * 70)
print("n=5 DODGE MECHANISM: BINARY PARITY AT FIRING TIME")
print("=" * 70)

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None:
        continue

    ell = len(word)

    # Check if dodges ALL boundary ternary
    all_dodge = True
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
        if mover & nonmover:
            all_dodge = False
            break

    if not all_dodge:
        continue

    # This cycle dodges all boundary ternary.
    # Trace binary parities at each ternary firing.
    fc = Counter(word)
    print(f"\nword={word}")
    print(f"fc={dict(fc)}, ell={ell}")

    for t in boundary_t:
        bL = (t - 1) % n
        bR = (t + 1) % n

        # Find t-firing steps
        t_steps = [s for s in range(ell) if word[s] == t]

        print(f"\n  proc {t} (bL={bL}, bR={bR}):")
        for i, s in enumerate(t_steps):
            # Count binary firings before step s
            bL_fires = sum(1 for j in range(s) if word[j] == bL)
            bR_fires = sum(1 for j in range(s) if word[j] == bR)
            t_fires = sum(1 for j in range(s) if word[j] == t)
            L_val = bL_fires % 2
            S_val = t_fires % 3
            R_val = bR_fires % 2
            ctx = (L_val, S_val, R_val)
            print(f"    firing {i+1}: step {s}, bL_fires={bL_fires}({L_val}), t_fires={t_fires}({S_val}), bR_fires={bR_fires}({R_val}), ctx={ctx}")

    # Also show nonmover contexts at each t
    for t in boundary_t:
        bL = (t - 1) % n
        bR = (t + 1) % n
        print(f"\n  proc {t} nonmover by S-level:")
        for s_val in range(3):
            nm_steps = [s for s in range(ell) if word[s] != t and cycle[s][t] == s_val]
            nm_lrs = set()
            for s in nm_steps:
                nm_lrs.add((cycle[s][bL], cycle[s][bR]))
            print(f"    S={s_val}: {len(nm_steps)} steps, LR={nm_lrs}")

    # Show binary proc EC
    for b in [0, 2, 4]:
        bL = (b - 1) % n
        bR = (b + 1) % n
        mover = set()
        nonmover = set()
        for s in range(ell):
            ctx = (cycle[s][bL], cycle[s][b], cycle[s][bR])
            if word[s] == b:
                mover.add(ctx)
            else:
                nonmover.add(ctx)
        if mover & nonmover:
            print(f"\n  BINARY {b}: EC at {mover & nonmover}")

    break  # Just first dodge cycle


# KEY ANALYSIS: For the dodge to work at boundary ternary,
# the binary parity before each firing must create "lucky" (L,R) pairs.
# How many dodge configurations are possible?
print(f"\n{'='*70}")
print("DODGE COUNTING: How many mover (L,R) triples avoid all nonmover?")
print("=" * 70)

dodges = []
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None:
        continue

    ell = len(word)
    all_dodge = True
    dodge_patterns = {}
    for t in boundary_t:
        bL = (t - 1) % n
        bR = (t + 1) % n
        mover = set()
        nonmover = set()
        m_by_s = {}
        n_by_s = defaultdict(set)
        for s in range(ell):
            L = cycle[s][bL]
            S = cycle[s][t]
            R = cycle[s][bR]
            ctx = (L, S, R)
            if word[s] == t:
                mover.add(ctx)
                m_by_s[S] = (L, R)
            else:
                nonmover.add(ctx)
                n_by_s[S].add((L, R))
        if mover & nonmover:
            all_dodge = False
            break
        dodge_patterns[t] = (m_by_s, dict(n_by_s))

    if all_dodge:
        # Record the dodge pattern: for each t, the 3 mover (L,R) triples
        pattern = {}
        for t in boundary_t:
            m_by_s, n_by_s = dodge_patterns[t]
            pattern[t] = tuple(m_by_s.get(k, None) for k in range(3))
        dodges.append(pattern)

print(f"\n{len(dodges)} dodge cycles at n=5")

# Count distinct dodge patterns
dodge_counter = Counter()
for d in dodges:
    key = tuple(d[t] for t in boundary_t)
    dodge_counter[key] += 1

print(f"\nDistinct dodge patterns:")
for pattern, cnt in dodge_counter.most_common():
    print(f"  {pattern}: {cnt} cycles")
    # For each S-level, what (L,R) does mover pick?
    for i, t in enumerate(boundary_t):
        mlrs = pattern[i]
        print(f"    proc {t}: S=0→{mlrs[0]}, S=1→{mlrs[1]}, S=2→{mlrs[2]}")
