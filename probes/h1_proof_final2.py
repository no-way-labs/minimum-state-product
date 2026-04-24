"""
H-1 Uniqueness — Final verification with known valid systems at n >= 3.

We need to verify with systems where fc(p) = m_p (or more precisely,
where CL = sum(m_p) — a "tight" good cycle).

Actually wait: Sol3v1 at n=5 has CL=10 but sum(ms)=14 (ms=[2,3,3,3,3]).
So CL != sum(ms). The fire counts are fc=[2,2,2,2,2], not [2,3,3,3,3].
This means Sol3v1 does NOT have fc=m_p for ternary procs.

Sol1 K=5 n=5 has CL=25 = 5*5 = sum(ms), and fc=[5,5,5,5,5] = ms. ✓

For the LB proof: the theorem is about good cycles of ANY valid system.
Not just fc=m_p systems. Let me reconsider what fc=m_p means.

Actually, fc(p) = m_p would mean each proc fires exactly m_p times per
cycle, visiting all m_p states. This is a very specific condition.

In many systems, fc(p) < m_p (procs don't visit all states in the good cycle).
For example, Sol3v1 ternary procs only visit 2 of 3 values.

So: H-1 Uniqueness might hold in general (for any fc), not just fc=m_p.
We already verified it holds for Sol3v1 (fc != m_p) at n=3..11.

Let me re-examine: is H-1 Uniqueness true for ALL valid systems at n >= 3,
regardless of fc?
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

def check_h1_general(ms, tables, verbose=False):
    """Check H-1 for any good cycle (no fc=m_p requirement)."""
    cycle, movers = get_good_cycle(ms, tables)
    if not cycle or len(cycle) <= 2: return None
    CL = len(cycle); n = len(ms)
    fc = [0]*n
    for m in movers: fc[m] += 1

    for j in range(CL):
        for k in range(j+1, CL):
            diff = sum(1 for i in range(n) if cycle[j][i] != cycle[k][i])
            if diff == 1 and min(k-j, CL-(k-j)) > 1:
                if verbose:
                    p = [i for i in range(n) if cycle[j][i] != cycle[k][i]][0]
                    print(f"  VIOLATION: j={j},k={k},p={p},d={min(k-j,CL-(k-j))}")
                    print(f"  CL={CL}, fc={fc}, movers={movers}")
                return False
    return True

# Test known valid n >= 3 systems (any fc, not just fc=m_p)
print("=== Known valid systems, any fc ===")

# Sol3v1 (fc != m_p for ternary)
for n in range(3, 12):
    ms = [2]+[3]*(n-1)
    tables = []
    for p in range(n):
        t = {}
        for L in range(ms[(p-1)%n]):
            for S in range(ms[p]):
                for R in range(ms[(p+1)%n]):
                    if p == 0: t[(L,S,R)] = (S+1)%ms[p] if S==L else S
                    else: t[(L,S,R)] = L if S!=L else S
        tables.append(t)
    result = check_h1_general(ms, tables)
    cycle, movers = get_good_cycle(ms, tables)
    CL = len(cycle)
    fc = [movers.count(p) for p in range(n)]
    print(f"  Sol3v1 n={n}: CL={CL}, fc={fc}, H-1={'HOLDS' if result else 'FAILS'}")

# Sol1 (fc = m_p = K for all procs)
for K in [3,4,5,6,7,8]:
    for n in [3,5]:
        if K < n: continue
        ms = [K]*n
        tables = []
        for p in range(n):
            t = {}
            for L in range(K):
                for S in range(K):
                    for R in range(K):
                        if p == 0: t[(L,S,R)] = (S+1)%K if S==L else S
                        else: t[(L,S,R)] = L if S!=L else S
            tables.append(t)
        result = check_h1_general(ms, tables)
        cycle, movers = get_good_cycle(ms, tables)
        CL = len(cycle)
        print(f"  Sol1 K={K} n={n}: CL={CL}, H-1={'HOLDS' if result else 'FAILS'}")

# Random valid systems at n >= 3 (any fc)
print("\n=== Random valid systems n >= 3, any fc ===")
random.seed(42)
for ms_test in [[2,3,3], [2,2,3], [2,3,4], [3,3,3], [2,2,2,3], [2,3,3,3]]:
    n = len(ms_test)
    found = 0; viols = 0
    for trial in range(50000):
        tables = []
        for p in range(n):
            t = {}
            mL = ms_test[(p-1)%n]; mS = ms_test[p]; mR = ms_test[(p+1)%n]
            for L in range(mL):
                for S in range(mS):
                    for R in range(mR):
                        t[(L,S,R)] = random.randrange(mS)
            tables.append(t)
        result = check_h1_general(ms_test, tables)
        if result is None: continue
        found += 1
        if result is False:
            viols += 1
            if viols <= 2:
                cycle, movers = get_good_cycle(ms_test, tables)
                CL = len(cycle)
                fc = [movers.count(p) for p in range(n)]
                print(f"  VIOLATION: ms={ms_test}, CL={CL}, fc={fc}")
    print(f"  ms={ms_test}: {found} valid, {viols} violations")

# Check n=2 for comparison
print("\n=== n=2 (any fc) ===")
for ms_test in [[2,3], [3,3], [2,2], [3,5]]:
    n = len(ms_test)
    found = 0; viols = 0
    for trial in range(20000):
        tables = []
        for p in range(n):
            t = {}
            mL = ms_test[(p-1)%n]; mS = ms_test[p]; mR = ms_test[(p+1)%n]
            for L in range(mL):
                for S in range(mS):
                    for R in range(mR):
                        t[(L,S,R)] = random.randrange(mS)
            tables.append(t)
        result = check_h1_general(ms_test, tables)
        if result is None: continue
        found += 1
        if result is False: viols += 1
    print(f"  ms={ms_test}: {found} valid, {viols} violations")
