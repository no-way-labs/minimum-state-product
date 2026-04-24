"""
Focused analysis: when does H-1 fail? Check if it fails for minimal cycles (fc=m_p).
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

random.seed(42)

# Analyze violating systems
for ms in [[2,3,4], [2,2,2,3], [2,3,3,3]]:
    n = len(ms)
    total = 0
    viol_minimal = 0
    viol_nonminimal = 0
    for trial in range(20000):
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
        total += 1

        fc = [0]*n
        for m in movers: fc[m] += 1
        minimal = all(fc[p] == ms[p] for p in range(n))

        has_viol = False
        for j in range(CL):
            for k in range(j+1, CL):
                diff = sum(1 for i in range(n) if cycle[j][i] != cycle[k][i])
                if diff == 1:
                    cdist = min(k-j, CL-(k-j))
                    if cdist != 1:
                        has_viol = True
                        break
            if has_viol: break

        if has_viol:
            if minimal:
                viol_minimal += 1
                if viol_minimal <= 2:
                    print(f"ms={ms}: MINIMAL violation, CL={CL}, fc={fc}, movers={movers}")
                    for i in range(CL):
                        print(f"  [{i}] {cycle[i]} m={movers[i]}")
            else:
                viol_nonminimal += 1

    print(f"ms={ms}: {total} valid, minimal_viol={viol_minimal}, nonminimal_viol={viol_nonminimal}")
    print()

# Key question: in the counterexample ms=[2,2,2,3] CL=5, movers=[0,3,0,3,3]
# fc = [2,0,0,3]. Proc 1 and 2 never fire! This is NOT a valid self-stabilizing system.
# Wait - is it? Let me check more carefully.

print("=== Checking if violating systems are truly self-stabilizing ===")
random.seed(42)
for ms in [[2,2,2,3]]:
    n = len(ms)
    for trial in range(20000):
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

        # Check for violations
        has_viol = False
        for j in range(CL):
            for k in range(j+1, CL):
                diff = sum(1 for i in range(n) if cycle[j][i] != cycle[k][i])
                if diff == 1:
                    cdist = min(k-j, CL-(k-j))
                    if cdist != 1:
                        has_viol = True
                        break
            if has_viol: break

        if has_viol:
            fc = [0]*n
            for m in movers: fc[m] += 1
            # Check: do ALL procs fire at least once?
            all_fire = all(fc[p] >= 1 for p in range(n))
            # fire_count = m_p for all p?
            fc_match = all(fc[p] == ms[p] for p in range(n))

            # Check self-stabilization: every config converges to good cycle
            total_configs = 1
            for m in ms: total_configs *= m
            good_set = set(cycle)

            converges = True
            for config in iprod(*[range(m) for m in ms]):
                if config in good_set: continue
                cur = config
                visited = set()
                while cur not in good_set:
                    if cur in visited:
                        converges = False
                        break
                    visited.add(cur)
                    # Find ANY privileged proc and fire
                    fired = False
                    for p in range(n):
                        L = cur[(p-1)%n]; S = cur[p]; R = cur[(p+1)%n]
                        if tables[p][(L,S,R)] != S:
                            cur_list = list(cur)
                            cur_list[p] = tables[p][(L,S,R)]
                            cur = tuple(cur_list)
                            fired = True
                            break
                    if not fired:
                        converges = False
                        break
                if not converges:
                    break

            print(f"  CL={CL}, fc={fc}, all_fire={all_fire}, fc_match={fc_match}, converges={converges}")
            print(f"  movers={movers}")
            if not all_fire:
                print(f"  *** Not all procs fire - degenerate system! ***")
            break
