#!/usr/bin/env python3
"""
Deep analysis: for ALL cycles with hno_safe + sandwiched ternary,
what are the (J, K) values for each phase?

Specifically: does exists_ternaryPhase ALWAYS return a phase with J>=2 or K>=2?
And: are there cycles where SOME phase has J<=1 AND K<=1?
"""
import random
from itertools import product as cprod

def left(i, n): return (i-1)%n
def right(i, n): return (i+1)%n

n = 5  # Use n=5 for exhaustive search (smaller state space)
results = []

for binary_set in [[0, 2, 4]]:  # gap-1 placement
    m = [3]*n
    for b in binary_set: m[b] = 2
    t = 1  # sandwiched: left=0 binary, right=2 binary

    for seed in range(100000):
        random.seed(seed)
        f = {}
        for proc in range(n):
            f[proc] = {}
            for L in range(m[left(proc,n)]):
                for S in range(m[proc]):
                    for R in range(m[right(proc,n)]):
                        f[proc][(L,S,R)] = random.randint(0, m[proc]-1)

        all_configs = list(cprod(*[range(m[j]) for j in range(n)]))
        priv = {}
        for c in all_configs:
            privs = [j for j in range(n) if f[j][(c[left(j,n)],c[j],c[right(j,n)])] != c[j]]
            if len(privs) == 1: priv[c] = privs[0]

        visited = set()
        for start in priv:
            if start in visited: continue
            path = [start]; vis = {start}; c = start; ok = False
            for _ in range(5000):
                p = priv[c]; cl = list(c); cl[p] = f[p][(c[left(p,n)],c[p],c[right(p,n)])]; cn = tuple(cl)
                if cn == start: ok = True; break
                if cn not in priv or cn in vis: break
                path.append(cn); vis.add(cn); c = cn
            if not ok or len(path) < 4: continue
            visited.update(path)

            movers = [priv[c] for c in path]
            safe = any(all(mov!=q and mov!=left(q,n) and mov!=right(q,n) for mov in movers) for q in range(n))
            if safe: continue

            fire_steps = [k for k in range(len(path)) if priv[path[k]] == t]
            if len(fire_steps) < 2: continue

            L_cycle = len(path)
            lt, rt = left(t, n), right(t, n)

            # Check ALL phases
            phase_jks = []
            for idx in range(len(fire_steps)):
                s = fire_steps[idx]
                a = (fire_steps[idx-1] + 1) % L_cycle
                if a >= s: continue  # skip wrap for simplicity
                J = sum(1 for k in range(a, s) if priv[path[k]] == lt)
                K = sum(1 for k in range(a, s) if priv[path[k]] == rt)
                phase_jks.append((J, K))

            if phase_jks:
                has_small = any(J <= 1 and K <= 1 for J, K in phase_jks)
                all_small = all(J <= 1 and K <= 1 for J, K in phase_jks)
                fc_t = len(fire_steps)
                fc_l = sum(1 for c in path if priv[c] == lt)
                fc_r = sum(1 for c in path if priv[c] == rt)
                results.append({
                    'seed': seed, 'len': L_cycle, 'fc_t': fc_t, 'fc_l': fc_l, 'fc_r': fc_r,
                    'phases': phase_jks, 'has_small': has_small, 'all_small': all_small
                })

total = len(results)
small = sum(1 for r in results if r['has_small'])
print(f"n={n}: {total} cycles with hno_safe + sandwiched ternary")
print(f"  Any phase with J<=1,K<=1: {small}")
print(f"  All phases J<=1,K<=1: {sum(1 for r in results if r['all_small'])}")
if small > 0:
    for r in results:
        if r['has_small']:
            print(f"    seed={r['seed']} len={r['len']} fc=({r['fc_l']},{r['fc_t']},{r['fc_r']}) phases={r['phases']}")
            if len([x for x in results if x['has_small']]) > 5:
                break
else:
    print("  → J<=1,K<=1 NEVER occurs with hno_safe!")
    # Show typical (J,K) patterns
    for r in results[:5]:
        print(f"    Example: phases={r['phases']} fc=({r['fc_l']},{r['fc_t']},{r['fc_r']})")
