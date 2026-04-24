#!/usr/bin/env python3
"""Check: does Sol3 (Dijkstra's Solution 3) satisfy hno_safe?
Sol3: ms=(3,3,...,3), f_0(L,S,R) = (L+1)%3 if S==L else S,
      f_i(L,S,R) = (L+1)%3 if S!=L else S for i>0 (Dijkstra's actual rules)

Actually let me use the known CUP-2 construction or just test Sol3 v1."""
import random

def sol3_v1_transition(n):
    """Sol3 v1: ms=(2,3,...,3).
    f_0(L,S,R) = (S+1)%2 if L==1 else S
    f_i(L,S,R) = L if S!=L else S for i > 0"""
    ms = [2] + [3]*(n-1)
    sys_f = {}

    # P0: binary (m=2)
    sys_f[0] = {}
    for L in range(ms[n-1]):
        for S in range(2):
            for R in range(ms[1]):
                # fires if S != (S+1)%2 when L==1
                if L == 1:
                    sys_f[0][(L,S,R)] = (S+1) % 2
                else:
                    sys_f[0][(L,S,R)] = S

    # Pi for i > 0: ternary (m=3)
    for i in range(1, n):
        sys_f[i] = {}
        for L in range(ms[(i-1)%n]):
            for S in range(3):
                for R in range(ms[(i+1)%n]):
                    if S != L:
                        sys_f[i][(L,S,R)] = L
                    else:
                        sys_f[i][(L,S,R)] = S

    return ms, sys_f

def dijkstra_sol3_transition(n):
    """Dijkstra's Solution 3: ms=(3,3,...,3).
    P0: f(L,S,R) = (S+1)%3 if S==L else S
    Pi>0: f(L,S,R) = L if S!=L else S"""
    ms = [3]*n
    sys_f = {}

    # P0
    sys_f[0] = {}
    for L in range(3):
        for S in range(3):
            for R in range(3):
                if S == L:
                    sys_f[0][(L,S,R)] = (S+1) % 3
                else:
                    sys_f[0][(L,S,R)] = S

    # Pi > 0
    for i in range(1, n):
        sys_f[i] = {}
        for L in range(3):
            for S in range(3):
                for R in range(3):
                    if S != L:
                        sys_f[i][(L,S,R)] = L
                    else:
                        sys_f[i][(L,S,R)] = S

    return ms, sys_f

def find_good_cycle_full(sys_f, ms, n, max_steps=50000):
    """Find good cycle by starting from a known good config."""
    # Start from (0,0,...,0)
    config = tuple(0 for _ in range(n))
    visited = {}
    for step in range(max_steps):
        if config in visited:
            start = visited[config]
            movers = []
            c = config
            for _ in range(step - start):
                privs = [i for i in range(n) if sys_f[i][(c[(i-1)%n], c[i], c[(i+1)%n])] != c[i]]
                if len(privs) != 1:
                    print(f"  step {step-start}: {len(privs)} privileged at {c}")
                    return None
                movers.append(privs[0])
                nc = list(c)
                p = privs[0]
                nc[p] = sys_f[p][(c[(p-1)%n], c[p], c[(p+1)%n])]
                c = tuple(nc)
            return movers
        visited[config] = step
        privs = [i for i in range(n) if sys_f[i][(config[(i-1)%n], config[i], config[(i+1)%n])] != config[i]]
        if len(privs) != 1:
            # Multi-privileged: not single-privileged, can't be good config
            # Try skipping
            if not privs:
                # No privileged: must be "legitimate" (all satisfied).
                # This IS a good config if it's in the cycle.
                # Skip by trying another start
                break
            p = privs[0]  # Just pick one to see where we go
        else:
            p = privs[0]
        nc = list(config)
        nc[p] = sys_f[p][(config[(p-1)%n], config[p], config[(p+1)%n])]
        config = tuple(nc)
    return None

def check_hno_safe(movers, n):
    for q in range(n):
        visited = any(m == q or m == (q-1)%n or m == (q+1)%n for m in movers)
        if not visited:
            return False
    return True

print("=== Sol3 (Dijkstra's Solution 3) ===")
for n in [5, 7, 9]:
    ms, sys_f = dijkstra_sol3_transition(n)
    movers = find_good_cycle_full(sys_f, ms, n)
    if movers:
        L = len(movers)
        fc = [0]*n
        for m in movers:
            fc[m] += 1
        distinct = sorted(set(movers))
        hno_safe = check_hno_safe(movers, n)
        print(f"n={n}: L={L} fc={fc} distinct_movers={distinct} hno_safe={hno_safe}")
    else:
        print(f"n={n}: No good cycle found from (0,...,0)")

print("\n=== Sol3 v1 ===")
for n in [5, 7, 9]:
    ms, sys_f = sol3_v1_transition(n)
    movers = find_good_cycle_full(sys_f, ms, n)
    if movers:
        L = len(movers)
        fc = [0]*n
        for m in movers:
            fc[m] += 1
        distinct = sorted(set(movers))
        hno_safe = check_hno_safe(movers, n)
        print(f"n={n}: L={L} fc={fc} distinct_movers={distinct} hno_safe={hno_safe}")
    else:
        print(f"n={n}: No good cycle found from (0,...,0)")

print("\n=== CUP-2 (ms=(2,3,...,3,2)) ===")
# CUP-2 uses specific tables. For now, let me try the known M_9=8748 witness
# ms=(2,3,3,3,3,3,3,3,2)
# The construction is in clb_witness_8748.py
# For now, let me just check Sol3's hno_safe status

print("\n=== Checking: is hno_safe EVER possible for valid systems at n>=5? ===")
# The known valid systems: Sol3 (ms=(3,...,3)), Sol3v1 (ms=(2,3,...,3)), CUP-2 (ms=(2,3,...,3,2))
# All have movers that DON'T cover all neighborhoods? Let's see.
# Sol3 at n=5 has L=8n-10=30 steps. Distinct movers = ?
