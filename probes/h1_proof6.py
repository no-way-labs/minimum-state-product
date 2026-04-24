"""
H-1 Uniqueness for PROPER good cycles (fc[p] = m_p for all p).

Proof strategy:
1. Propagation: if (g_j, g_k) are Hamming-1 at p with offset d = k-j mod CL,
   then (g_{j+1}, g_{k+1}) are also Hamming-1 at p (PROVED above).
2. So the H-1 relationship propagates forever: g_i and g_{i+d} are Hamming-1 at p for ALL i.
3. This means: for ALL i, g_i[q] = g_{i+d}[q] for q != p.
   So the sequence of values at position q has period d.
4. Since q fires m_q times in the full cycle (fc = m_q), and the period is d:
   q fires m_q * d / CL times per period, and returns to its start value.
   For this to work: m_q * d / CL must be a positive integer.
5. For p: g_i[p] != g_{i+d}[p] for all i. So in one period of length d,
   p's value must shift to a DIFFERENT value. p fires m_p * d / CL times per period.

Now: CL = sum(m_p) in a minimal cycle (wait, CL = sum of fire counts = sum(m_p) only
if fc[p] = m_p. Actually CL = sum(fc) = sum(m_p) by definition of fc[p]=m_p.

Let me verify CL = sum(ms) for minimal cycles.
"""
from itertools import product as iprod

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

# Check CL = sum(ms) for known systems
def build_sol1(K, n):
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
    return ms, tables

for K in [3,4,5,6]:
    for n in [3,4,5]:
        if K < n: continue
        ms, tables = build_sol1(K, n)
        cycle, movers = get_good_cycle(ms, tables)
        CL = len(cycle)
        fc = [0]*n
        for m in movers: fc[m] += 1
        print(f"Sol1 K={K} n={n}: CL={CL}, sum(ms)={sum(ms)}, fc={fc}, ms={ms}")
        assert CL == sum(ms), "CL != sum(ms)!"

# Sol3v1
for n in range(3,10):
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
    cycle, movers = get_good_cycle(ms, tables)
    CL = len(cycle)
    print(f"Sol3v1 n={n}: CL={CL}, sum(ms)={sum(ms)}")

# NOW: proof argument for fc[p]=m_p case
# If d | CL and every q != p has period d for its values, AND p has period d with a shift:
#
# Consider: the sequence of values at proc q over the cycle is determined by
# when q fires and what it fires to. If q's value sequence has period d < CL,
# then q traverses its m_q values in m_q * d/CL steps, returning to start.
#
# But wait: each proc visits ALL m_q values exactly once (since fc=m_q and
# the values are distinct between consecutive firings). So the value sequence
# at q is: v_0, v_0, ..., v_1, v_1, ..., v_{m_q-1}, v_{m_q-1}, ...
# where each value appears exactly CL/m_q times (not necessarily, but each
# firing changes to a new value).
#
# Actually: fc[q] = m_q means q fires m_q times. Since q has m_q states,
# after m_q firings q returns to its start. So q visits all m_q values.
# Between consecutive firings of q, q's value is constant.
#
# If the value sequence at q has period d:
#   The first occurrence of q firing within [0,d) fires at some step j1.
#   Then q also fires at j1+d, j1+2d, etc.
#   In total: m_q firings, with CL/d repetitions per period.
#   So: m_q * d/CL firings per period = integer.
#
# For p: value differs between g_i and g_{i+d}. So the value at p does NOT
# have period d. But ALL other values do.
#
# Here's the key constraint: look at step j where moverAt(j) = p.
# Then g_{j+1}[p] = f(g_j[p-1], g_j[p], g_j[p+1]).
# And moverAt(j+d) = moverAt(j) (since movers have period d).
# So moverAt(j+d) = p too.
# g_{j+d+1}[p] = f(g_{j+d}[p-1], g_{j+d}[p], g_{j+d}[p+1]).
# g_{j+d}[p-1] = g_j[p-1] (period d for non-p procs).
# g_{j+d}[p+1] = g_j[p+1] (period d for non-p procs).
# g_{j+d}[p] != g_j[p] (no period d for p).
#
# So: f(L, g_j[p], R) and f(L, g_{j+d}[p], R) are the transitions at p.
# The next values are g_{j+1}[p] and g_{j+d+1}[p].
# These must also differ (since g_{j+1} and g_{j+d+1} are Hamming-1 at p).
#
# So the transition function f at p, with the SAME (L,R) context,
# maps two different S values to two different S' values. This is fine.
#
# The real question: can d be anything other than 1 or CL-1?
#
# For d to work: the mover sequence must have period d.
# And CL/d must divide each m_q (so m_q * d/CL is integer).
# Wait: we need m_q * d/CL to be an integer for all q.
# Equivalently: CL/gcd(d, CL) | m_q... no. Let D = CL/d (number of periods).
# Then each q fires m_q/D times per period. So D | m_q for all q.
#
# If D | m_q for all q, and D | m_p, and D >= 2:
# Then m_q >= D >= 2 for all q, and the mover sequence repeats D times.
#
# For the context: in sweep cycles at sub-threshold product,
# some procs are binary (m=2). So D | 2, meaning D in {1, 2}.
# D=1: trivial (d=CL, no real pairing).
# D=2: d=CL/2. Each proc fires m_p/2 times per half.
#   For binary: m_p=2, fires 1 time per half. OK.
#   For ternary: m_p=3, fires 3/2 times per half. NOT integer!
#   So D=2 fails if any proc has odd fire count (m_p odd).
#
# Since ternary procs have m_p=3 (odd), D=2 is impossible when there's any ternary proc.
# For D >= 3: binary procs need D | 2, so D in {1,2}. Contradiction.
#
# Therefore: for any system with at least one binary and one ternary proc,
# d=CL-1 (which equals distance 1) is the ONLY possible offset!
#
# Wait, d can also be CL (trivial). And d=CL-1 gives cyclic distance 1.
# Actually d=1 also gives cyclic distance 1.
# d=CL-1: cyclic distance = min(CL-1, 1) = 1. Yes.
#
# So: the only possible H-1 offsets are d=1 and d=CL-1, both giving cyclic distance 1.

# Let me verify this divisibility argument:
print("\n=== Divisibility check ===")
# For d | CL with d < CL, D = CL/d >= 2.
# Need D | m_q for ALL q.
# If ms contains 2 and 3: gcd(2,3) = 1, so D | 1, D = 1. Contradiction.

# More generally: D | gcd(m_0, m_1, ..., m_{n-1}).
# If gcd(ms) = 1: no D >= 2 works. So only d=1 and d=CL-1 possible.

# When does gcd(ms) > 1? Only if ALL m_p share a common factor.
# E.g., ms = [4,6,8]: gcd = 2. Then D=2 possible.
# Let's test this case.
print("Testing ms=[4,6] (gcd=2)...")
import random
random.seed(42)
n = 2
ms = [4, 6]
violations = 0
found = 0
for trial in range(50000):
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
    fc = [0]*n
    for m in movers: fc[m] += 1
    if not all(fc[p] == ms[p] for p in range(n)): continue
    found += 1
    for j in range(CL):
        for k in range(j+1, CL):
            diff = [i for i in range(n) if cycle[j][i] != cycle[k][i]]
            if len(diff) == 1:
                cdist = min(k-j, CL-(k-j))
                if cdist != 1:
                    violations += 1
                    if violations <= 2:
                        print(f"  VIOLATION: CL={CL}, j={j}, k={k}, dist={cdist}")
                        print(f"  movers={movers}")

print(f"ms={ms}: {found} minimal systems, {violations} violations")

print("\nTesting ms=[4,4,6] (gcd=2)...")
random.seed(42)
n = 3
ms = [4, 4, 6]
violations = 0
found = 0
for trial in range(50000):
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
    fc = [0]*n
    for m in movers: fc[m] += 1
    if not all(fc[p] == ms[p] for p in range(n)): continue
    found += 1
    for j in range(CL):
        for k in range(j+1, CL):
            diff = [i for i in range(n) if cycle[j][i] != cycle[k][i]]
            if len(diff) == 1:
                cdist = min(k-j, CL-(k-j))
                if cdist != 1:
                    violations += 1
                    if violations <= 2:
                        p_diff = diff[0]
                        print(f"  VIOLATION: CL={CL}, j={j}, k={k}, p={p_diff}, dist={cdist}")
                        print(f"  movers={movers}")
                        for i in range(CL):
                            marker = " <--" if i in [j,k] else ""
                            print(f"    [{i}] {cycle[i]} m={movers[i]}{marker}")

print(f"ms={ms}: {found} minimal systems, {violations} violations")

# Also: test ms=[6,6,6] (gcd=6)
print("\nTesting ms=[6,6,6] (gcd=6)...")
random.seed(42)
n = 3
ms = [6, 6, 6]
violations = 0
found = 0
for trial in range(50000):
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
    fc = [0]*n
    for m in movers: fc[m] += 1
    if not all(fc[p] == ms[p] for p in range(n)): continue
    found += 1
    for j in range(CL):
        for k in range(j+1, CL):
            diff = [i for i in range(n) if cycle[j][i] != cycle[k][i]]
            if len(diff) == 1:
                cdist = min(k-j, CL-(k-j))
                if cdist != 1:
                    violations += 1
                    if violations <= 2:
                        p_diff = diff[0]
                        print(f"  VIOLATION: CL={CL}, j={j}, k={k}, p={p_diff}, dist={cdist}")
                        for i in range(CL):
                            marker = " <--" if i in [j,k] else ""
                            print(f"    [{i}] {cycle[i]} m={movers[i]}{marker}")

print(f"ms={ms}: {found} minimal systems, {violations} violations")
