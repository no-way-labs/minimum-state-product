#!/usr/bin/env python3
"""
Deep analysis of (1,1)-phase EC exceptions.
Focus on the 2 exceptions at ms=[2,2,2,2,3].
Also test more multisets systematically.
"""
from itertools import product as iprod, combinations_with_replacement
from collections import Counter, defaultdict

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

def find_phases_at_t(word, t, n):
    L = len(word)
    bL = (t - 1) % n
    bR = (t + 1) % n
    t_steps = [s for s in range(L) if word[s] == t]
    if len(t_steps) == 0:
        return []
    phases = []
    for idx in range(len(t_steps)):
        s1 = t_steps[idx]
        s2 = t_steps[(idx + 1) % len(t_steps)]
        phase_steps = []
        s = (s1 + 1) % L
        while s != s2:
            phase_steps.append(s)
            s = (s + 1) % L
        J = sum(1 for s in phase_steps if word[s] == bL)
        K = sum(1 for s in phase_steps if word[s] == bR)
        phases.append((s1, s2, J, K, phase_steps))
    return phases

def has_11_phase(word, t, n):
    phases = find_phases_at_t(word, t, n)
    for (s1, s2, J, K, steps) in phases:
        if J == 1 and K == 1:
            return True
    return False

def find_entry_conflicts(word, configs, ms, n):
    L = len(word)
    ec_procs = {}
    for p in range(n):
        mover_ctx = set()
        nonmover_ctx = set()
        pL = (p - 1) % n
        pR = (p + 1) % n
        for s in range(L):
            ctx = (configs[s][pL], configs[s][p], configs[s][pR])
            if word[s] == p:
                mover_ctx.add(ctx)
            else:
                nonmover_ctx.add(ctx)
        overlap = mover_ctx & nonmover_ctx
        if overlap:
            ec_procs[p] = overlap
    return ec_procs

# ===== Analyze the 2 exceptions =====
print("=" * 70)
print("DETAILED ANALYSIS OF EXCEPTIONS at ms=[2,2,2,2,3]")
print("=" * 70)

n = 5
ms = [2, 2, 2, 2, 3]
sandwiched = [p for p in range(n) if ms[p] == 3
              and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]
print(f"sandwiched ternary: {sandwiched}")

words = enumerate_good_cycles(ms, n, 16)
for word in words:
    configs = build_configs(ms, n, word)
    if configs is None:
        continue
    for t in sandwiched:
        if not has_11_phase(word, t, n):
            continue
    ec = find_entry_conflicts(word, configs, ms, n)
    if not ec:
        L = len(word)
        fc = Counter(word)
        print(f"\nException: word={word}, L={L}")
        print(f"  fc={dict(fc)}")
        print(f"  Configs:")
        for s in range(L):
            print(f"    step {s}: mover={word[s]}, config={configs[s]}")

        # Show phases at each sandwiched ternary
        for t in sandwiched:
            phases = find_phases_at_t(word, t, n)
            print(f"\n  Phases at t={t}:")
            for (s1, s2, J, K, steps) in phases:
                print(f"    firing at step {s1} -> next at step {s2}: "
                      f"J={J} K={K} movers_in_phase={[word[s] for s in steps]}")

        # Show ALL contexts at ALL procs
        for p in range(n):
            pL = (p - 1) % n
            pR = (p + 1) % n
            print(f"\n  Proc {p} (m={ms[p]}, nbrs m={ms[pL]},{ms[pR]}), ctx_space={ms[pL]*ms[p]*ms[pR]}:")
            mover_ctx = {}
            nonmover_ctx = {}
            for s in range(L):
                ctx = (configs[s][pL], configs[s][p], configs[s][pR])
                if word[s] == p:
                    mover_ctx[s] = ctx
                else:
                    nonmover_ctx[s] = ctx
            print(f"    mover contexts ({len(mover_ctx)}):")
            for s, ctx in sorted(mover_ctx.items()):
                print(f"      step {s}: {ctx}")
            print(f"    nonmover distinct: {len(set(nonmover_ctx.values()))}")
            print(f"    mover set:    {sorted(set(mover_ctx.values()))}")
            print(f"    nonmover set: {sorted(set(nonmover_ctx.values()))}")
            print(f"    overlap: {set(mover_ctx.values()) & set(nonmover_ctx.values())}")

# ===== Classify: is the word a sweep? =====
print("\n\n" + "=" * 70)
print("SWEEP CLASSIFICATION OF EXCEPTIONS")
print("=" * 70)

for word in words:
    configs = build_configs(ms, n, word)
    if configs is None:
        continue
    has_any_11 = any(has_11_phase(word, t, n) for t in sandwiched)
    if not has_any_11:
        continue
    ec = find_entry_conflicts(word, configs, ms, n)
    if not ec:
        L = len(word)
        # Check if sweep: consecutive movers go around ring
        is_sweep = True
        for i in range(L - 1):
            diff = (word[i+1] - word[i]) % n
            if diff != 1 and diff != n - 1:
                is_sweep = False
                break
        # Also check wrap-around
        if is_sweep:
            diff = (word[0] - word[-1]) % n
            if diff != 1 and diff != n - 1:
                is_sweep = False

        # More specifically: is it a uniform sweep?
        diffs = [(word[(i+1)%L] - word[i]) % n for i in range(L)]
        cw = sum(1 for d in diffs if d == 1)
        ccw = sum(1 for d in diffs if d == n - 1)
        print(f"word={word}")
        print(f"  is_sweep={is_sweep}")
        print(f"  CW steps: {cw}, CCW steps: {ccw}")
        print(f"  diffs: {diffs}")
        print(f"  fc: {dict(Counter(word))}")
