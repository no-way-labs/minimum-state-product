#!/usr/bin/env python3
"""
Analyze ALL exception cycles to find common structure.
Key question: are they all uniform sweeps?
What additional hypothesis excludes them?
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

def find_phases_at_t(word, t, n):
    L = len(word)
    bL = (t - 1) % n
    bR = (t + 1) % n
    t_steps = [s for s in range(L) if word[s] == t]
    if not t_steps:
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
    return any(J == 1 and K == 1 for (_, _, J, K, _) in phases)

def find_entry_conflicts(word, configs, ms, n):
    L = len(word)
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
        if mover_ctx & nonmover_ctx:
            return True
    return False

def is_uniform_sweep(word, n):
    """Check if word is a uniform sweep (all steps in same direction)."""
    L = len(word)
    diffs = [(word[(i+1)%L] - word[i]) % n for i in range(L)]
    cw = all(d == 1 for d in diffs)
    ccw = all(d == n-1 for d in diffs)
    return cw or ccw

def classify_cycle(word, n):
    """Classify cycle type."""
    L = len(word)
    diffs = [(word[(i+1)%L] - word[i]) % n for i in range(L)]
    cw = sum(1 for d in diffs if d == 1)
    ccw = sum(1 for d in diffs if d == n-1)
    if cw == L:
        return "pure_CW_sweep"
    if ccw == L:
        return "pure_CCW_sweep"
    if cw + ccw == L:
        return f"mixed_sweep(CW={cw},CCW={ccw})"
    return "non_sweep"

# Check ms=[2,2,3,2,4] exceptions
print("="*70)
print("EXCEPTIONS at ms=[2,2,3,2,4]")
print("="*70)

n = 5
ms = [2, 2, 3, 2, 4]
sandwiched = [p for p in range(n) if ms[p] == 3
              and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]
print(f"ms={ms}, sandwiched={sandwiched}")

ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
start = tuple(0 for _ in range(n))
words = []
def dfs(word, fc, config):
    if len(word) > 18:
        return
    if len(word) >= n and config == start:
        if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
            words.append(tuple(word))
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

exc_words = []
for word in words:
    configs = build_configs(ms, n, word)
    if configs is None:
        continue
    has_11 = any(has_11_phase(word, t, n) for t in sandwiched)
    if not has_11:
        continue
    if not find_entry_conflicts(word, configs, ms, n):
        exc_words.append(word)
        L = len(word)
        fc = Counter(word)
        ctype = classify_cycle(word, n)
        print(f"  word={word}")
        print(f"    L={L}, fc={dict(fc)}, type={ctype}")

        # Show ALL phase patterns at sandwiched ternary
        for t in sandwiched:
            phases = find_phases_at_t(word, t, n)
            phase_nfs = [(J, K) for (_, _, J, K, _) in phases]
            print(f"    phases at t={t}: {phase_nfs}")
        print()

# Check ms=[2,2,2,2,3] and [2,2,4,2,3] similarly
for ms in [[2, 2, 2, 2, 3], [2, 2, 4, 2, 3]]:
    print(f"\n{'='*70}")
    print(f"EXCEPTIONS at ms={ms}")
    print(f"{'='*70}")

    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]
    print(f"sandwiched={sandwiched}")

    words = []
    def dfs2(word, fc, config):
        if len(word) > 18:
            return
        if len(word) >= n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                words.append(tuple(word))
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            nc = list(config)
            nc[nxt] = (nc[nxt] + 1) % ms[nxt]
            nf = list(fc)
            nf[nxt] += 1
            word.append(nxt)
            dfs2(word, nf, tuple(nc))
            word.pop()
    for p in range(n):
        first = list(start)
        first[p] = (first[p] + 1) % ms[p]
        dfs2([p], [1 if i == p else 0 for i in range(n)], tuple(first))

    for word in words:
        configs = build_configs(ms, n, word)
        if configs is None:
            continue
        has_11 = any(has_11_phase(word, t, n) for t in sandwiched)
        if not has_11:
            continue
        if not find_entry_conflicts(word, configs, ms, n):
            L = len(word)
            fc = Counter(word)
            ctype = classify_cycle(word, n)
            print(f"  word={word}")
            print(f"    L={L}, fc={dict(fc)}, type={ctype}")
            for t in sandwiched:
                phases = find_phases_at_t(word, t, n)
                phase_nfs = [(J, K) for (_, _, J, K, _) in phases]
                print(f"    phases at t={t}: {phase_nfs}")

# KEY QUESTION: Are ALL exceptions uniform sweeps?
print(f"\n{'='*70}")
print("SUMMARY: Are all exceptions uniform sweeps?")
print("="*70)
