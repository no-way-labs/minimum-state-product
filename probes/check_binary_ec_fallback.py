#!/usr/bin/env python3
"""What does the binary EC look like for the 120 cycles that don't trigger ternary mechanisms?"""
from itertools import product as iproduct
from collections import Counter

n = 5
ms = [2, 3, 2, 3, 2]
start = tuple(0 for _ in range(n))
ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}
sandwiched = [1, 3]

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
            if M == 1 and J % 2 == 0 and K % 2 == 0: return True
            if (J >= 3 and K == 0) or (J == 0 and K >= 3): return True
            if M == 1 and ((J >= 2 and K == 0) or (J == 0 and K >= 2)): return True
            if M == 1 and (J, K) in [(2, 1), (1, 2)]:
                single = bR if J == 2 else bL
                for s in steps:
                    if word[s] in (bL, bR):
                        if word[s] == single: return True
                        break
    return False

# Find the 120 no-ternary-trigger zero-winding cycles
zw_cycles = [w for w in results if winding(w) == 0]
fallback = [w for w in zw_cycles if not any_ternary_phase_triggers(w)]

print(f"Analyzing {len(fallback)} fallback cycles (no ternary mechanism)")

# For each: where is the EC?
ec_procs = Counter()
ec_details = []
for word in fallback:
    ell = len(word)
    configs = [list(start)]
    for i in range(ell):
        c = list(configs[-1]); c[word[i]] = (c[word[i]]+1) % ms[word[i]]
        configs.append(c)
    for p in range(n):
        m_ctx, n_ctx = set(), set()
        conflict_ctx = None
        for s in range(ell):
            ctx = (configs[s][(p-1)%n], configs[s][p], configs[s][(p+1)%n])
            if word[s] == p:
                if ctx in n_ctx:
                    conflict_ctx = ctx
                    break
                m_ctx.add(ctx)
            else:
                if ctx in m_ctx:
                    conflict_ctx = ctx
                    break
                n_ctx.add(ctx)
        if conflict_ctx:
            ec_procs[p] += 1
            if len(ec_details) < 5:
                fc = Counter(word)
                ec_details.append({
                    'word': word, 'proc': p, 'ctx': conflict_ctx,
                    'fc': dict(fc), 'len': ell,
                    'binary': ms[p] == 2
                })
            break

print(f"\nEC proc distribution: {dict(sorted(ec_procs.items()))}")
for p in sorted(ec_procs):
    print(f"  Proc {p} (m={ms[p]}): {ec_procs[p]}")

print(f"\nExample fallback cycles:")
for d in ec_details:
    print(f"  len={d['len']}, fc={d['fc']}, EC at proc {d['proc']} (binary={d['binary']})")
    print(f"    conflicting ctx={d['ctx']}")
    print(f"    word={d['word']}")

# KEY: what is the STRUCTURE of the binary EC?
# Is it BoundaryShadowEntry-style? MinGap-style? Something else?
print(f"\nBinary EC structure analysis:")
for d in ec_details[:3]:
    word = d['word']
    p = d['proc']
    ell = len(word)
    configs = [list(start)]
    for i in range(ell):
        c = list(configs[-1]); c[word[i]] = (c[word[i]]+1) % ms[word[i]]
        configs.append(c)

    # Find the two steps with matching context
    ctx_target = d['ctx']
    mover_steps = []
    nonmover_steps = []
    for s in range(ell):
        ctx = (configs[s][(p-1)%n], configs[s][p], configs[s][(p+1)%n])
        if ctx == ctx_target:
            if word[s] == p:
                mover_steps.append(s)
            else:
                nonmover_steps.append(s)

    print(f"\n  Proc {p}, ctx={ctx_target}")
    print(f"  Mover steps: {mover_steps}")
    print(f"  Nonmover steps: {nonmover_steps}")
    # Who is firing at the nonmover step?
    for s in nonmover_steps:
        print(f"    At nonmover step {s}: mover=proc {word[s]}, config={configs[s]}")
    for s in mover_steps:
        print(f"    At mover step {s}: proc {p} fires, config={configs[s]}")
