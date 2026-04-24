"""
Examine the ms=[2,2,3] fc=[2,2,2] violation at n=3.
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
        for pp in range(n):
            L = config[(pp-1)%n]; S = config[pp]; R = config[(pp+1)%n]
            if tables[pp][(L,S,R)] != S:
                privs.append(pp)
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

random.seed(42)
ms = [2, 2, 3]; n = 3
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
    cycle, movers = get_good_cycle(ms, tables)
    if not cycle or len(cycle) <= 2: continue
    CL = len(cycle)
    fc = [movers.count(p) for p in range(n)]
    if fc != [2, 2, 2]: continue

    has_viol = False
    for j in range(CL):
        for k in range(j+1, CL):
            diff = [i for i in range(n) if cycle[j][i] != cycle[k][i]]
            if len(diff) == 1 and min(k-j, CL-(k-j)) > 1:
                has_viol = True
                pp = diff[0]
                print(f"CL={CL}, fc={fc}, j={j}, k={k}, p={pp}, cdist={min(k-j,CL-(k-j))}")
                print(f"Movers: {movers}")
                for i in range(CL):
                    marker = " <--" if i in [j,k] else ""
                    print(f"  [{i}] {cycle[i]} mover={movers[i]}{marker}")
                # Tables
                for pp2 in range(n):
                    print(f"  Proc {pp2} (m={ms[pp2]}) transitions:")
                    for ctx in sorted(tables[pp2].keys()):
                        if tables[pp2][ctx] != ctx[1]:
                            print(f"    {ctx} -> {tables[pp2][ctx]}")
                # Check: is this system actually self-stabilizing?
                total = 1
                for m in ms: total *= m
                good_set = set(cycle)
                bad_configs = [c for c in iprod(*[range(m) for m in ms]) if c not in good_set]
                print(f"  #good={len(good_set)}, #bad={len(bad_configs)}, total={total}")
                break
        if has_viol: break
    if has_viol:
        break

# Also: at ms=[2,2,3], fc=[2,2,2], CL=6.
# CL=6 = 2+2+2 = sum(fc). Proc 2 fires 2 times but m_2=3.
# So proc 2 only visits 2 of 3 values. This is NOT a proper system
# in the sense that the good cycle doesn't use all of proc 2's states.

# KEY: For the LB proof, the relevant systems are at or below the threshold
# product. For these systems, the good cycle MUST use all states (otherwise
# the system could use fewer states and have a smaller product).

# Actually, the LB proof considers systems where each proc has EXACTLY m_p
# states. If the good cycle only uses 2 of 3 values at proc 2, then proc 2
# could be replaced by a 2-state proc, reducing the product. So such systems
# are NOT optimal and not relevant to the LB proof.

# So: for the LB proof context, the correct condition is:
# fc(p) = m_p for all p (each proc visits all its states).
# Under this condition, H-1 Uniqueness holds.

# Let me confirm: for fc(p) = m_p, H-1 holds.
print("\n=== Strict fc=m_p check ===")
random.seed(42)
for ms_test in [[2,2,3], [2,3,3], [2,3,4], [3,3,3], [2,2,2,3], [2,3,3,3]]:
    n_val = len(ms_test)
    found = 0; viols = 0
    for trial in range(100000):
        tables = []
        for p in range(n_val):
            t = {}
            mL = ms_test[(p-1)%n_val]; mS = ms_test[p]; mR = ms_test[(p+1)%n_val]
            for L in range(mL):
                for S in range(mS):
                    for R in range(mR):
                        t[(L,S,R)] = random.randrange(mS)
            tables.append(t)
        cycle, movers = get_good_cycle(ms_test, tables)
        if not cycle or len(cycle) <= 2: continue
        CL = len(cycle)
        fc = [movers.count(p) for p in range(n_val)]
        if not all(fc[p] == ms_test[p] for p in range(n_val)): continue
        found += 1
        for j in range(CL):
            for k in range(j+1, CL):
                diff = sum(1 for i in range(n_val) if cycle[j][i] != cycle[k][i])
                if diff == 1 and min(k-j, CL-(k-j)) > 1:
                    viols += 1
                    break
            if viols: break
        if viols and found >= 1:
            break
    print(f"  ms={ms_test}: {found} fc=m_p systems, {viols} violations")
