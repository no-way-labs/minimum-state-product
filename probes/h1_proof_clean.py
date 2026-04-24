"""
H-1 Uniqueness Proof for n >= 3 with fc(p) = m_p.

APPROACH: Fiber intersection argument.

Setup:
- Good cycle gc = (g_0, g_1, ..., g_{CL-1}) with CL = sum(m_p).
- Each proc p fires exactly m_p times, visiting all m_p values.
- Position p has m_p "phases": maximal intervals where p holds constant value.
- Phase(p, v) = set of cycle indices where g_i[p] = v.

Key: For two configs g_j, g_k to be Hamming-1 at position p:
  g_j[p] != g_k[p] (different phases)
  g_j[q] = g_k[q] for all q != p (same "fiber" at non-p positions)

The fiber at step i (excluding position p) is:
  fiber_p(i) = (g_i[0], ..., g_i[p-1], g_i[p+1], ..., g_i[n-1])

Hamming-1 at p iff fiber_p(j) = fiber_p(k) and g_j[p] != g_k[p].

CLAIM: In a good cycle with n >= 3 and fc(p) = m_p, the fiber fiber_p takes
CL distinct values. (I.e., fiber_p is injective on cycle indices.)

If the fiber is injective: no two distinct indices have the same fiber.
So no Hamming-1 pairs at p with distance > 1.
But adjacent pairs (j, j+1) where moverAt(j) = p DO have the same fiber
(only p changes). So exactly m_p Hamming-1 pairs at p.
Total Hamming-1 pairs summed over all p = CL. All adjacent. ✓

Wait, but the claim "fiber_p is injective" would mean the fiber at step j
is different from the fiber at step j+1 even when moverAt(j) != p
(since only the mover changes, and if mover != p, then fiber changes at
the mover position). And when moverAt(j) = p: fiber stays the same.

So fiber_p is NOT injective: at each step where p fires, the fiber stays
the same. There are m_p such steps, giving m_p pairs of consecutive indices
with the same fiber.

Let me restate: fiber_p(j) = fiber_p(j+1) iff moverAt(j) = p.
When moverAt(j) = q != p: fiber_p changes at position q.

So: the fiber changes at every step EXCEPT when p fires.

The claim should be: fiber_p(j) = fiber_p(k) for j != k iff they are
"adjacent across a p-firing". I.e., moverAt(min(j,k)) = p and |j-k| = 1.

This is equivalent to: the fiber_p sequence has no repeated values except
at consecutive indices where p fires.

Let me check this computationally.
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

def check_fiber_injectivity(ms, tables, label=""):
    cycle, movers = get_good_cycle(ms, tables)
    if not cycle: return None
    CL = len(cycle); n = len(ms)
    fc = [0]*n
    for m in movers: fc[m] += 1
    if not all(fc[p] == ms[p] for p in range(n)): return None

    # For each position p, compute fiber and check
    for p in range(n):
        fibers = {}  # fiber -> list of indices
        for i in range(CL):
            fib = tuple(cycle[i][q] for q in range(n) if q != p)
            if fib not in fibers:
                fibers[fib] = []
            fibers[fib].append(i)

        for fib, indices in fibers.items():
            if len(indices) > 2:
                print(f"  {label} p={p}: fiber {fib} appears {len(indices)} times at {indices}")
                return False
            if len(indices) == 2:
                j, k = indices
                cdist = min(k-j, CL-(k-j))
                if cdist != 1:
                    print(f"  {label} p={p}: fiber {fib} at {indices}, cdist={cdist}")
                    return False
                # Verify it's a p-firing
                if movers[min(j,k)] != p and movers[max(j,k)-1 if max(j,k)>0 else CL-1] != p:
                    # Check which direction
                    if k == j+1 and movers[j] == p:
                        pass  # OK
                    elif j == 0 and k == CL-1 and movers[CL-1] == p:
                        pass  # OK
                    else:
                        print(f"  {label} p={p}: fiber repeat at {indices} but mover={movers[j]},{movers[k]}")

    return True

# Test with known systems
for K in [3, 4, 5, 6, 7]:
    for n in [3, 4, 5]:
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
        ok = check_fiber_injectivity(ms, tables, f"Sol1 K={K} n={n}")
        if ok is False:
            print(f"  *** FIBER NOT INJECTIVE ***")

for n in range(3, 10):
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
    ok = check_fiber_injectivity(ms, tables, f"Sol3v1 n={n}")
    if ok is False:
        print(f"  *** FIBER NOT INJECTIVE ***")

# Now check n=2 (should find non-injective fibers)
print("\n=== n=2 fiber check ===")
import random
random.seed(42)
ms = [2, 3]; n = 2
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
    if not cycle: continue
    CL = len(cycle)
    fc = [0]*n
    for m in movers: fc[m] += 1
    if not all(fc[p] == ms[p] for p in range(n)): continue

    ok = check_fiber_injectivity(ms, tables, f"n=2 trial {trial}")
    if ok is False:
        print(f"  movers={movers}")
        for i in range(CL):
            print(f"  [{i}] {cycle[i]} m={movers[i]}")
        break

print("Done")
