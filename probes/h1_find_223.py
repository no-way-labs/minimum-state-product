"""Find the ms=[2,2,3] all-fire violation (from seed 42)."""
from itertools import product as iprod
import random

def test(ms, tables):
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
    return cycle, movers

random.seed(42)
ms = [2,2,3]; n = 3
for trial in range(100000):
    tables = []
    for p in range(n):
        t = {}
        mL = ms[(p-1)%n]; mS = ms[p]; mR = ms[(p+1)%n]
        for L in range(mL):
            for S in range(mS):
                for R in range(mR):
                    t[(L,S,R)] = random.randrange(mS)
        tables.append(t)
    result = test(ms, tables)
    if result is None: continue
    cycle, movers = result
    CL = len(cycle)
    fc = [movers.count(p) for p in range(n)]
    all_fire = all(f >= 1 for f in fc)

    has_viol = False
    for j in range(CL):
        for k in range(j+1, CL):
            diff = [i for i in range(n) if cycle[j][i] != cycle[k][i]]
            if len(diff) == 1 and min(k-j, CL-(k-j)) > 1:
                has_viol = True
                pp = diff[0]
                if all_fire:
                    print(f"ALL-FIRE VIOLATION: trial={trial}")
                    print(f"CL={CL}, fc={fc}, j={j}, k={k}, p={pp}, cdist={min(k-j,CL-(k-j))}")
                    print(f"Movers: {movers}")
                    for i in range(CL):
                        marker = " <--" if i in [j,k] else ""
                        print(f"  [{i}] {cycle[i]} mover={movers[i]}{marker}")
                    for ppp in range(n):
                        print(f"  Proc {ppp} (m={ms[ppp]}):")
                        for ctx in sorted(tables[ppp].keys()):
                            if tables[ppp][ctx] != ctx[1]:
                                print(f"    {ctx} -> {tables[ppp][ctx]}")
                break
        if has_viol: break
    if has_viol and all_fire:
        break
