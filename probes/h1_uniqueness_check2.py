"""
H-1 Uniqueness: broader check including CUP-2 and random valid systems.
Focus: can consecutive same-mover happen? Can H-1 fail?
"""
from itertools import product as iprod

def get_good_cycle(ms, tables):
    n = len(ms)
    def fire(config, p):
        L = config[(p-1)%n]; S = config[p]; R = config[(p+1)%n]
        new = list(config); new[p] = tables[p][(L,S,R)]
        return tuple(new)

    def privileged(config):
        privs = []
        for p in range(n):
            L = config[(p-1)%n]; S = config[p]; R = config[(p+1)%n]
            if tables[p][(L,S,R)] != S:
                privs.append(p)
        return privs

    # Find good configs
    good = {}
    for config in iprod(*[range(m) for m in ms]):
        ps = privileged(config)
        if len(ps) == 1:
            good[config] = ps[0]

    if not good:
        return None, None

    start = next(iter(good))
    cycle = [start]
    movers = [good[start]]
    cur = start
    for _ in range(100000):
        nxt = fire(cur, good[cur])
        if nxt == start:
            break
        if nxt not in good:
            return None, None
        cycle.append(nxt)
        movers.append(good[nxt])
        cur = nxt
    else:
        return None, None

    return cycle, movers

def check_h1(ms, tables, label=""):
    cycle, movers = get_good_cycle(ms, tables)
    if cycle is None:
        return None
    CL = len(cycle)
    n = len(ms)

    consec = sum(1 for i in range(CL) if movers[i] == movers[(i+1)%CL])

    nonadj = 0
    for j in range(CL):
        for k in range(j+1, CL):
            diff = sum(1 for i in range(n) if cycle[j][i] != cycle[k][i])
            if diff == 1:
                dist = min(k-j, CL-(k-j))
                if dist > 1:
                    nonadj += 1
                    if nonadj <= 3:
                        p = [i for i in range(n) if cycle[j][i] != cycle[k][i]][0]
                        print(f"  COUNTEREXAMPLE: j={j},k={k},p={p},dist={dist}")
                        print(f"    g_j={cycle[j]} mover_j={movers[j]}")
                        print(f"    g_k={cycle[k]} mover_k={movers[k]}")

    if label:
        print(f"  {label}: CL={CL}, consec_same={consec}, nonadj_h1={nonadj}")
    return nonadj == 0


# CUP-2: ms=(2,3,...,3,2)
def build_cup2(n):
    ms = [2] + [3]*(n-2) + [2]

    # Tables from cup2_final_verify.py
    # T_left (proc 0, binary, L from proc n-1 which is binary)
    # T_right (proc n-1, binary, R from proc 0 which is binary)
    # T_low (proc 1, ternary, L from binary)
    # T_high (proc n-2, ternary, R from binary)
    # T_mid (proc 2..n-3, ternary, L and R from ternary)

    tables = [None]*n

    # Proc 0: binary. L=c[n-1] in {0,1}, S=c[0] in {0,1}, R=c[1] in {0,1,2}
    t0 = {}
    for L in range(2):
        for S in range(2):
            for R in range(3):
                # Privileged when S == L (Dijkstra-like for bottom)
                if S == L:
                    t0[(L,S,R)] = (S+1)%2
                else:
                    t0[(L,S,R)] = S
    tables[0] = t0

    # Proc n-1: binary. L=c[n-2] in {0,1,2}, S=c[n-1] in {0,1}, R=c[0] in {0,1}
    tn = {}
    for L in range(3):
        for S in range(2):
            for R in range(2):
                # Privileged when S == R (mirror of proc 0)
                if S == R:
                    tn[(L,S,R)] = (S+1)%2
                else:
                    tn[(L,S,R)] = S
    tables[n-1] = tn

    # Proc 1: ternary, L from binary (range 2)
    t1 = {}
    for L in range(2):
        for S in range(3):
            for R in range(3):
                if S != L:
                    t1[(L,S,R)] = L
                else:
                    t1[(L,S,R)] = S
    tables[1] = t1

    # Proc n-2: ternary, R from binary (range 2)
    tn2 = {}
    for L in range(3):
        for S in range(3):
            for R in range(2):
                if S != R:
                    tn2[(L,S,R)] = R
                else:
                    tn2[(L,S,R)] = S
    tables[n-2] = tn2

    # Interior procs 2..n-3: ternary, L and R from ternary
    for p in range(2, n-2):
        t = {}
        for L in range(3):
            for S in range(3):
                for R in range(3):
                    if S != L:
                        t[(L,S,R)] = L
                    else:
                        t[(L,S,R)] = S
        tables[p] = t

    return ms, tables


print("=== CUP-2 systems ===")
for n in [4, 5, 6, 7, 8, 9, 10]:
    ms, tables = build_cup2(n)
    check_h1(ms, tables, f"CUP-2 n={n}")

# Dijkstra Sol1 with various K
print("\n=== Dijkstra Sol1 (various K, n) ===")
for n in [3, 4, 5, 6]:
    for K in range(n, min(n+4, 10)):
        ms = [K]*n
        tables = []
        for p in range(n):
            t = {}
            for L in range(K):
                for S in range(K):
                    for R in range(K):
                        if p == 0:
                            t[(L,S,R)] = (S+1)%K if S==L else S
                        else:
                            t[(L,S,R)] = L if S!=L else S
            tables.append(t)
        check_h1(ms, tables, f"Sol1 K={K} n={n}")

# Dijkstra Sol3
print("\n=== Dijkstra Sol3 ===")
for n in [5, 6, 7]:
    K = n
    ms = [K]*n
    tables = []
    for p in range(n):
        t = {}
        for L in range(K):
            for S in range(K):
                for R in range(K):
                    if p == 0:
                        t[(L,S,R)] = (S+1)%K if (S==L and S==R) else S
                    else:
                        t[(L,S,R)] = (S+1)%K if S==L and S!=R else S if S==L else L
        tables.append(t)
    check_h1(ms, tables, f"Sol3 K={K} n={n}")

# CLB witness ms=(2,3,3,3,3,3,3,3,2) for n=9
# Let me try to build it
print("\n=== Sol3v1 (various n) ===")
for n in range(3, 12):
    ms = [2] + [3]*(n-1)
    tables = []
    for p in range(n):
        t = {}
        for L in range(ms[(p-1)%n]):
            for S in range(ms[p]):
                for R in range(ms[(p+1)%n]):
                    if p == 0:
                        t[(L,S,R)] = (S+1)%ms[p] if S==L else S
                    else:
                        t[(L,S,R)] = L if S!=L else S
        tables.append(t)
    check_h1(ms, tables, f"Sol3v1 n={n}")

print("\n=== Random brute-force search for counterexample ===")
# Try building valid systems with small state spaces and checking
import random
random.seed(42)

def random_valid_system(ms, attempts=1000):
    """Try random transition tables, check if system is valid."""
    n = len(ms)
    total = 1
    for m in ms:
        total *= m

    for _ in range(attempts):
        tables = []
        for p in range(n):
            t = {}
            mL = ms[(p-1)%n]; mS = ms[p]; mR = ms[(p+1)%n]
            for L in range(mL):
                for S in range(mS):
                    for R in range(mR):
                        t[(L,S,R)] = random.randrange(mS)
            tables.append(t)

        # Check: every config has exactly one privileged proc? (too strict)
        # Just check if good cycle exists
        cycle, movers = get_good_cycle(ms, tables)
        if cycle is not None and len(cycle) > 2:
            return ms, tables, cycle, movers
    return None

# Try small systems
count = 0
for ms_try in [[2,3,3], [3,3,3], [2,2,3], [2,3,4], [2,2,2,3], [3,3,3,3]]:
    result = random_valid_system(ms_try, 5000)
    if result:
        ms, tables, cycle, movers = result
        ok = check_h1(ms, tables, f"Random {ms}")
        count += 1
        if count >= 10:
            break

print(f"\nTotal random systems tested: {count}")
