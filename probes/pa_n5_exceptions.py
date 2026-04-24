#!/usr/bin/env python3
"""PA: Deep analysis of the 16 n=5 exceptions — normalForm cycles with no EC
at boundary ternary.

Key question: do these cycles have EC at OTHER procs? Or is EC truly absent?
And are these cycles actually achievable by some transition function?
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


def extract_phases(word, cycle, ms, n, t):
    ell = len(word)
    bL = (t - 1) % n
    bR = (t + 1) % n
    t_steps = [s for s in range(ell) if word[s] == t]
    fc_t = len(t_steps)
    if fc_t == 0:
        return []
    phases = []
    for i in range(fc_t):
        start = (t_steps[i] + 1) % ell
        end = t_steps[(i + 1) % fc_t]
        J, K = 0, 0
        s = start
        while s != end:
            if word[s] == bL:
                J += 1
            elif word[s] == bR:
                K += 1
            s = (s + 1) % ell
        phases.append((J, K))
    return phases


def is_normalForm(J, K):
    return (J, K) in [(1, 0), (0, 1), (1, 1), (2, 1), (1, 2)]


n = 5
ms = [2, 3, 2, 3, 2]
max_len = 16
boundary_t = [1, 3]

words = enumerate_mover_words(ms, n, max_len)
print(f"n=5, ms={ms}: {len(words)} words")

exceptions = []

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None:
        continue

    # Check all phases normalForm
    all_nf = True
    for t in boundary_t:
        phases = extract_phases(word, cycle, ms, n, t)
        for J, K in phases:
            if not is_normalForm(J, K):
                all_nf = False
                break
        if not all_nf:
            break
    if not all_nf:
        continue

    # Check EC at boundary ternary
    ell = len(word)
    has_ec_boundary = False
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
            has_ec_boundary = True

    if has_ec_boundary:
        continue

    # This is an exception: no EC at boundary ternary
    # Check EC ANYWHERE
    has_ec_any = False
    ec_proc = None
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
            has_ec_any = True
            ec_proc = t
            break

    exceptions.append({
        'word': word,
        'fc': dict(Counter(word)),
        'ell': ell,
        'ec_anywhere': has_ec_any,
        'ec_proc': ec_proc,
        'cycle': cycle,
    })

print(f"\nExceptions (normalForm, no EC at boundary ternary): {len(exceptions)}")

for i, ex in enumerate(exceptions):
    word = ex['word']
    cycle = ex['cycle']
    ell = ex['ell']
    print(f"\n--- Exception {i+1} ---")
    print(f"  word={word}")
    print(f"  fc={ex['fc']}, ell={ell}")
    print(f"  EC anywhere: {ex['ec_anywhere']} (proc={ex['ec_proc']})")

    # Print phases
    for t in boundary_t:
        phases = extract_phases(word, cycle, ms, n, t)
        print(f"  proc {t} phases: {phases}")

    # Print full context trace at each proc
    for t in range(n):
        bL = (t - 1) % n
        bR = (t + 1) % n
        mover = {}
        nonmover = {}
        for s in range(ell):
            ctx = (cycle[s][bL], cycle[s][t], cycle[s][bR])
            if word[s] == t:
                mover[s] = ctx
            else:
                nonmover[s] = ctx
        overlap = set(mover.values()) & set(nonmover.values())
        if overlap:
            print(f"  PROC {t} [m={ms[t]}]: EC! overlap={overlap}")
        else:
            print(f"  PROC {t} [m={ms[t]}]: no EC. mover={set(mover.values())} nonmover={set(nonmover.values())}")

    # Check: which binary procs have EC?
    print(f"\n  Binary proc EC check:")
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
        overlap = mover & nonmover
        print(f"    binary {b}: mover={mover} nonmover={nonmover} overlap={overlap}")


# Now: the CRUCIAL question.
# At n>=9, does the ring size force more constraints?
print("\n" + "=" * 70)
print("KEY STRUCTURAL ANALYSIS OF EXCEPTIONS")
print("=" * 70)

# Group exceptions by fc pattern
fc_groups = defaultdict(list)
for ex in exceptions:
    fc_key = tuple(ex['fc'].get(p, 0) for p in range(n))
    fc_groups[fc_key].append(ex)

for fc_key, exs in fc_groups.items():
    print(f"\nFC pattern {fc_key}: {len(exs)} exceptions")
    mult = tuple(fc_key[p] // ms[p] for p in range(n))
    print(f"  Multiplicity: {mult}")

    # What are the phase patterns?
    for ex in exs[:2]:
        word = ex['word']
        cycle = ex['cycle']
        for t in boundary_t:
            phases = extract_phases(word, cycle, ms, n, t)
            print(f"  word={word}, proc {t}: {phases}")
