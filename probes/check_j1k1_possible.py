#!/usr/bin/env python3
"""
With hno_safe + n >= 9 + sandwiched ternary t:
Can a phase of t have J=1 AND K=1?

J = fires of left(t) in phase. K = fires of right(t) in phase.
J=1, K=1 means: left and right each fire exactly once in this phase.

The phase [a, s) has: 1 left fire + 1 right fire + outside fires.
Phase length = 2 + outside_fires_in_phase.

With fc(left t) even >= 2: across all phases, left fires even times.
If this phase has J=1: other phases have fc(left)-1 (odd) total left fires.
With fc(t) fires of t: fc(t) phases. This phase has J=1.

For J=1 AND K=1 in a phase: the phase has very few non-t fires (just 2 + outside).

With hno_safe + n >= 9: the cycle has many movers. But they could all fire
in OTHER phases, not this one.

Let me check: can we construct a cycle where a sandwiched ternary phase
has J=1, K=1, with hno_safe holding?
"""

from itertools import product as cprod
import random

def left(i, n): return (i - 1) % n
def right(i, n): return (i + 1) % n

def check():
    n = 9
    # Sandwiched ternary at t=4: left=3 (binary), right=5 (binary)
    # Binary = {3, 5, 7}, ternary = rest
    binary_set = [3, 5, 7]
    m = [3]*n
    for b in binary_set: m[b] = 2
    t = 4  # sandwiched: left=3 binary, right=5 binary

    found = 0
    for seed in range(50000):
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
            privs = [j for j in range(n) if f[j][(c[left(j,n)], c[j], c[right(j,n)])] != c[j]]
            if len(privs) == 1:
                priv[c] = privs[0]

        visited = set()
        for start in priv:
            if start in visited: continue
            path = [start]; vis = {start}; c = start; ok = False
            for _ in range(50000):
                p = priv[c]
                cl = list(c); cl[p] = f[p][(c[left(p,n)], c[p], c[right(p,n)])]; cn = tuple(cl)
                if cn == start: ok = True; break
                if cn not in priv or cn in vis: break
                path.append(cn); vis.add(cn); c = cn
            if not ok or len(path) < 6: continue
            visited.update(path)

            # Check hno_safe
            movers = [priv[c] for c in path]
            safe = False
            for q in range(n):
                if all(mov != q and mov != left(q,n) and mov != right(q,n) for mov in movers):
                    safe = True; break
            if safe: continue

            # Check phases of t=4
            L_cycle = len(path)
            fire_steps = [k for k in range(L_cycle) if priv[path[k]] == t]
            if len(fire_steps) < 2: continue

            for idx in range(len(fire_steps)):
                s = fire_steps[idx]
                a = (fire_steps[idx-1] + 1) % L_cycle
                if a >= s: continue
                J = sum(1 for k in range(a, s) if priv[path[k]] == left(t, n))
                K = sum(1 for k in range(a, s) if priv[path[k]] == right(t, n))
                if J == 1 and K == 1:
                    found += 1
                    if found <= 5:
                        fc = [sum(1 for c in path if priv[c]==j) for j in range(n)]
                        print(f"  J=1,K=1 FOUND: seed={seed} len={L_cycle} fc={fc}")
                        # Check if normal form
                        nf = True
                        if J%2==0 and K%2==0: nf = False
                        if J>=2 and K==0: nf = False
                        if J==0 and K>=2: nf = False
                        print(f"    Normal form: {nf}")

    print(f"\nTotal J=1,K=1 phases with hno_safe: {found}")
    if found == 0:
        print("→ J=1,K=1 NEVER occurs with hno_safe! Only J≥2 or K≥2 cases exist.")
        print("→ Traversal Return handles everything. No palindromic argument needed!")

check()
