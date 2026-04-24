#!/usr/bin/env python3
"""
CRITICAL CHECK: Is "Ring Alternation" (some ternary phase triggers mechanism 1-4)
actually TRUE for all zero-winding non-consecutive cycles?

Our earlier data showed 94.2% per-phase coverage at n=5. But we need 100%
per-CYCLE coverage at the ternary level. If some cycles only have EC at
binary procs, Ring Alternation is the WRONG lemma.
"""
from itertools import product as iproduct
from collections import Counter

n = 5
ms = [2, 3, 2, 3, 2]
start = tuple(0 for _ in range(n))
ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}
sandwiched = [p for p in range(n) if ms[p] == 3 and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]

results = []
def dfs(word, fc, config):
    if len(word) > 16: return
    if len(word) >= 2*n and config == start:
        if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
            results.append(tuple(word))
        return
    remaining = 16 - len(word)
    needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
    if needed > remaining: return
    last = word[-1]
    for nxt in ring_adj[last]:
        word.append(nxt)
        nf = list(fc); nf[nxt] += 1
        nc = list(config); nc[nxt] = (nc[nxt]+1) % ms[nxt]
        dfs(word, nf, tuple(nc))
        word.pop()

for p in range(n):
    first = list(start); first[p] = (first[p]+1) % ms[p]
    dfs([p], [1 if i==p else 0 for i in range(n)], tuple(first))

def winding(word):
    w = 0
    for i in range(len(word)):
        d = (word[(i+1)%len(word)] - word[i]) % n
        if d == 1: w += 1
        elif d == n-1: w -= 1
    return w

def temporal_order(steps, ell):
    if len(steps) <= 1: return steps
    max_gap = 0; start_after = 0
    for i in range(len(steps)):
        nxt = (i+1) % len(steps)
        gap = (steps[nxt] - steps[i]) % ell
        if gap > max_gap: max_gap = gap; start_after = i
    si = (start_after+1) % len(steps)
    return [steps[(si+i) % len(steps)] for i in range(len(steps))]

def any_ternary_phase_triggers(word):
    """Does ANY phase at ANY sandwiched ternary trigger mechanism 1-4?"""
    ell = len(word)
    configs = [list(start)]
    for i in range(ell):
        c = list(configs[-1]); c[word[i]] = (c[word[i]]+1) % ms[word[i]]
        configs.append(c)

    for t in sandwiched:
        bL, bR = (t-1)%n, (t+1)%n
        for k in range(3):
            raw = sorted(s for s in range(ell) if configs[s][t] == k)
            steps = temporal_order(raw, ell)
            M = sum(1 for s in steps if word[s] == t)
            J = sum(1 for s in steps if word[s] == bL)
            K = sum(1 for s in steps if word[s] == bR)

            # Mechanism 1
            if M == 1 and J % 2 == 0 and K % 2 == 0: return True
            # Mechanism 2
            if (J >= 3 and K == 0) or (J == 0 and K >= 3): return True
            # Mechanism 3
            if M == 1 and ((J >= 2 and K == 0) or (J == 0 and K >= 2)): return True
            # Mechanism 4
            if M == 1 and (J, K) in [(2, 1), (1, 2)]:
                single = bR if J == 2 else bL
                for s in steps:
                    if word[s] in (bL, bR):
                        if word[s] == single: return True
                        break
    return False

def has_ec_anywhere(word):
    ell = len(word)
    configs = [list(start)]
    for i in range(ell):
        c = list(configs[-1]); c[word[i]] = (c[word[i]]+1) % ms[word[i]]
        configs.append(c)
    for p in range(n):
        m_ctx, n_ctx = set(), set()
        for s in range(ell):
            ctx = (configs[s][(p-1)%n], configs[s][p], configs[s][(p+1)%n])
            if word[s] == p:
                if ctx in n_ctx: return True, p
                m_ctx.add(ctx)
            else:
                if ctx in m_ctx: return True, p
                n_ctx.add(ctx)
    return False, None

# Check zero-winding cycles only
zw_cycles = [w for w in results if winding(w) == 0]
print(f"n={n}, ms={ms}")
print(f"Zero-winding cycles: {len(zw_cycles)}")

ternary_triggers = 0
no_ternary_trigger = 0
no_ternary_but_has_ec = 0
no_ec_at_all = 0
ec_at_binary_only = []

for word in zw_cycles:
    if any_ternary_phase_triggers(word):
        ternary_triggers += 1
    else:
        no_ternary_trigger += 1
        has, p = has_ec_anywhere(word)
        if has:
            no_ternary_but_has_ec += 1
            if ms[p] == 2:
                ec_at_binary_only.append((word, p))
        else:
            no_ec_at_all += 1

print(f"\nTernary mechanism triggers: {ternary_triggers} ({100*ternary_triggers/len(zw_cycles):.1f}%)")
print(f"No ternary trigger: {no_ternary_trigger}")
print(f"  Of those, has EC elsewhere: {no_ternary_but_has_ec}")
print(f"  Of those, EC at binary proc: {len(ec_at_binary_only)}")
print(f"  No EC at all: {no_ec_at_all}")

if no_ternary_trigger > 0:
    print(f"\n*** RING ALTERNATION IS INSUFFICIENT for {no_ternary_trigger} cycles ***")
    print(f"*** Need fallback mechanism for these cycles ***")
else:
    print(f"\n*** RING ALTERNATION WORKS: all cycles trigger a ternary mechanism ***")
