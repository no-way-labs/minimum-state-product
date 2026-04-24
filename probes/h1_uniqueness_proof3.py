"""
H-1 Uniqueness is FALSE. Find and analyze counterexamples.
"""
from itertools import product as iprod
import random

def get_good_cycle(ms, tables):
    n = len(ms)
    def fire(config, p):
        L = config[(p-1)%n]; S = config[p]; R = config[(p+1)%n]
        new = list(config); new[p] = tables[p][(L,S,R)]
        return tuple(new)
    good = {}
    for config in iprod(*[range(m) for m in ms]):
        privs = []
        for p in range(n):
            L = config[(p-1)%n]; S = config[p]; R = config[(p+1)%n]
            if tables[p][(L,S,R)] != S:
                privs.append(p)
        if len(privs) == 1:
            good[config] = privs[0]
    if not good: return None, None
    start = next(iter(good))
    cycle = [start]; movers = [good[start]]; cur = start
    for _ in range(100000):
        nxt = fire(cur, good[cur])
        if nxt == start: break
        if nxt not in good: return None, None
        cycle.append(nxt); movers.append(good[nxt]); cur = nxt
    else: return None, None
    return cycle, movers

def find_violations(ms, max_systems=50000):
    n = len(ms)
    random.seed(42)
    results = []
    for trial in range(max_systems):
        tables = []
        for p in range(n):
            t = {}
            mL = ms[(p-1)%n]; mS = ms[p]; mR = ms[(p+1)%n]
            for L in range(mL):
                for S in range(mS):
                    for R in range(mR):
                        t[(L,S,R)] = random.randrange(mS)
            tables.append(t)
        cycle, movers = get_good_cycle(ms, tables)
        if not cycle or len(cycle) <= 2:
            continue
        CL = len(cycle)
        for j in range(CL):
            for k in range(j+1, CL):
                diff = [i for i in range(n) if cycle[j][i] != cycle[k][i]]
                if len(diff) == 1:
                    cdist = min(k-j, CL-(k-j))
                    if cdist != 1:
                        results.append((ms, tables, cycle, movers, j, k, diff[0], cdist))
                        if len(results) >= 5:
                            return results
    return results

# Find counterexamples for ms=[2,3,4]
print("=== ms=[2,3,4] ===")
viols = find_violations([2,3,4], 50000)
for ms, tables, cycle, movers, j, k, p, cdist in viols:
    CL = len(cycle)
    n = len(ms)
    print(f"\nCL={CL}, j={j}, k={k}, p={p}, cyclic_dist={cdist}")
    print(f"  g_j = {cycle[j]}, mover_j = {movers[j]}")
    print(f"  g_k = {cycle[k]}, mover_k = {movers[k]}")
    print(f"  Full cycle:")
    for i in range(CL):
        marker = ""
        if i == j: marker = " <-- j"
        if i == k: marker = " <-- k"
        print(f"    [{i}] {cycle[i]} mover={movers[i]}{marker}")
    # Print tables
    print(f"  Tables:")
    for pp in range(n):
        print(f"    Proc {pp} (m={ms[pp]}):")
        for L in range(ms[(pp-1)%n]):
            for S in range(ms[pp]):
                for R in range(ms[(pp+1)%n]):
                    new = tables[pp][(L,S,R)]
                    if new != S:
                        print(f"      ({L},{S},{R}) -> {new}")
    break  # just first

print("\n=== ms=[2,2,2,3] ===")
viols = find_violations([2,2,2,3], 50000)
for ms, tables, cycle, movers, j, k, p, cdist in viols[:1]:
    CL = len(cycle)
    n = len(ms)
    print(f"\nCL={CL}, j={j}, k={k}, p={p}, cyclic_dist={cdist}")
    print(f"  g_j = {cycle[j]}, mover_j = {movers[j]}")
    print(f"  g_k = {cycle[k]}, mover_k = {movers[k]}")
    print(f"  Full cycle:")
    for i in range(CL):
        marker = ""
        if i == j: marker = " <-- j"
        if i == k: marker = " <-- k"
        print(f"    [{i}] {cycle[i]} mover={movers[i]}{marker}")

print("\n=== ms=[2,3,3,3] ===")
viols = find_violations([2,3,3,3], 50000)
for ms, tables, cycle, movers, j, k, p, cdist in viols[:1]:
    CL = len(cycle)
    n = len(ms)
    print(f"\nCL={CL}, j={j}, k={k}, p={p}, cyclic_dist={cdist}")
    print(f"  g_j = {cycle[j]}, mover_j = {movers[j]}")
    print(f"  g_k = {cycle[k]}, mover_k = {movers[k]}")
    print(f"  Full cycle:")
    for i in range(CL):
        marker = ""
        if i == j: marker = " <-- j"
        if i == k: marker = " <-- k"
        print(f"    [{i}] {cycle[i]} mover={movers[i]}{marker}")
