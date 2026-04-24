#!/usr/bin/env python3
"""Check if Sol3v1 (ms=(2,3,...,3)) has a safe processor."""
import random

def sol3v1_system(n):
    ms = [2] + [3]*(n-1)
    sys_f = {}
    # P0: binary. f(L,S,R) = (S+1)%2 if L==1 else S
    sys_f[0] = {}
    for L in range(ms[n-1]):
        for S in range(2):
            for R in range(ms[1]):
                sys_f[0][(L,S,R)] = (S+1)%2 if L == 1 else S
    # Pi (i>0): ternary. f(L,S,R) = L if S!=L else S
    for i in range(1, n):
        sys_f[i] = {}
        for L in range(ms[(i-1)%n]):
            for S in range(3):
                for R in range(ms[(i+1)%n]):
                    sys_f[i][(L,S,R)] = L if S != L else S
    return ms, sys_f

def find_cycle(sys_f, ms, n, start, max_steps=50000):
    config = start
    visited = {}
    for step in range(max_steps):
        if config in visited:
            start_idx = visited[config]
            movers = []
            c = config
            for _ in range(step - start_idx):
                privs = [i for i in range(n) if sys_f[i][(c[(i-1)%n], c[i], c[(i+1)%n])] != c[i]]
                if len(privs) != 1: return None
                movers.append(privs[0])
                nc = list(c)
                p = privs[0]
                nc[p] = sys_f[p][(c[(p-1)%n], c[p], c[(p+1)%n])]
                c = tuple(nc)
            return movers
        visited[config] = step
        privs = [i for i in range(n) if sys_f[i][(config[(i-1)%n], config[i], config[(i+1)%n])] != config[i]]
        if len(privs) != 1: return None
        p = privs[0]
        nc = list(config)
        nc[p] = sys_f[p][(config[(p-1)%n], config[p], config[(p+1)%n])]
        config = tuple(nc)
    return None

def check_safe(movers, n):
    """Return list of safe procs."""
    safe = []
    for q in range(n):
        is_safe = all(m != q and m != (q-1)%n and m != (q+1)%n for m in movers)
        if is_safe:
            safe.append(q)
    return safe

for n in [5, 7, 9]:
    ms, sys_f = sol3v1_system(n)
    # Try many starts
    for start_vals in [[0]*n, [1]*n, [1,0]+[0]*(n-2)]:
        start = tuple(start_vals[:n])
        movers = find_cycle(sys_f, ms, n, start)
        if movers:
            safe = check_safe(movers, n)
            fc = [0]*n
            for m in movers: fc[m] += 1
            distinct = sorted(set(movers))
            print(f"n={n} L={len(movers)} distinct={distinct} fc={fc}")
            print(f"  safe procs: {safe}")
            print(f"  movers: {movers[:20]}...")
            break
    else:
        print(f"n={n}: no cycle found")
