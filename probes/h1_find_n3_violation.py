"""
Find the n=3, all_fire=True violation.
"""
from itertools import product as iprod
import random

def test_system_verbose(ms, tables):
    n = len(ms)
    def fire(config, p):
        L = config[(p-1)%n]; S = config[p]; R = config[(p+1)%n]
        new = list(config); new[p] = tables[p][(L,S,R)]
        return tuple(new)
    good = {}
    for config in iprod(*[range(m) for m in ms]):
        privs = []
        for pp in range(n):
            L = config[(pp-1)%n]; S = config[pp]; R = config[(pp+1)%n]
            if tables[pp][(L,S,R)] != S:
                privs.append(pp)
        if len(privs) == 1:
            good[config] = privs[0]
    if not good: return None
    start = next(iter(good))
    cycle = [start]; movers = [good[start]]; cur = start
    for _ in range(10000):
        nxt = fire(cur, good[cur])
        if nxt == start: break
        if nxt not in good: return None
        cycle.append(nxt); movers.append(good[nxt]); cur = nxt
    else: return None
    CL = len(cycle)
    if CL <= 2: return None
    fc = [movers.count(p) for p in range(n)]
    all_fire = all(f >= 1 for f in fc)

    has_viol = False
    viol_info = None
    for j in range(CL):
        for k in range(j+1, CL):
            diff = [i for i in range(n) if cycle[j][i] != cycle[k][i]]
            if len(diff) == 1 and min(k-j, CL-(k-j)) > 1:
                has_viol = True
                viol_info = (j, k, diff[0])
                break
        if has_viol: break

    return all_fire, has_viol, fc, CL, cycle, movers, viol_info

random.seed(12345)
# Reproduce the ms lists from previous test
for ms_test in [[2,2,3], [2,3,3], [3,3,3], [2,3,4], [2,3,5], [3,3,5]]:
    n = len(ms_test)
    for trial in range(30000):
        tables = []
        for p in range(n):
            t = {}
            mL = ms_test[(p-1)%n]; mS = ms_test[p]; mR = ms_test[(p+1)%n]
            for L in range(mL):
                for S in range(mS):
                    for R in range(mR):
                        t[(L,S,R)] = random.randrange(mS)
            tables.append(t)
        result = test_system_verbose(ms_test, tables)
        if result is None: continue
        all_fire, has_viol, fc, CL, cycle, movers, viol_info = result
        if all_fire and has_viol:
            j, k, p = viol_info
            print(f"FOUND: ms={ms_test}, CL={CL}, fc={fc}")
            print(f"Violation: j={j}, k={k}, p={p}, cdist={min(k-j, CL-(k-j))}")
            print(f"Movers: {movers}")
            for i in range(CL):
                marker = " <--" if i in [j,k] else ""
                print(f"  [{i}] {cycle[i]} mover={movers[i]}{marker}")
            # Print non-identity transitions
            for pp in range(n):
                print(f"  Proc {pp} (m={ms_test[pp]}) transitions:")
                for ctx in sorted(tables[pp].keys()):
                    if tables[pp][ctx] != ctx[1]:
                        print(f"    {ctx} -> {tables[pp][ctx]}")
            print()
            break
