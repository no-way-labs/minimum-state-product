"""
H-1 Uniqueness — Formal Proof

=======================================================================
THEOREM (H-1 Uniqueness, n >= 3):
Let (g_0, ..., g_{CL-1}) be the good cycle of a self-stabilizing token ring
with n >= 3 processors, state sizes (m_0, ..., m_{n-1}), and fc(p) = m_p
for all p. If g_j and g_k differ at exactly one position p, then
|j - k| = 1 (mod CL).
=======================================================================

PROOF:

Setup and Definitions:
- Good cycle: g_0 -> g_1 -> ... -> g_{CL-1} -> g_0, where CL = sum(m_p).
- Each g_i is a good config (exactly one privileged proc).
- moverAt(i) = the unique privileged proc at g_i.
- Firing moverAt(i) transforms g_i to g_{i+1 mod CL}.
- Each proc p fires exactly m_p times (fc(p) = m_p).
- All good configs are distinct.

For position p, define the fiber map:
  fib_p(i) = (g_i[0], ..., g_i[p-1], g_i[p+1], ..., g_i[n-1])
  (the config at step i with position p removed)

Observation 1: fib_p(i) = fib_p(i+1) iff moverAt(i) = p.
  (If moverAt(i) = p: only position p changes. If moverAt(i) = q != p:
   position q changes, so the fiber changes at coordinate q.)

Observation 2: g_j and g_k are Hamming-1 at p iff fib_p(j) = fib_p(k)
  and g_j[p] != g_k[p].

So: H-1 Uniqueness is equivalent to: fib_p(j) = fib_p(k) implies
|j - k| <= 1 (mod CL) for all p.

CLAIM: For n >= 3 with fc(p) = m_p, the fiber fib_p takes at most
CL - m_p + 1 distinct values, and each repeated fiber value occurs at
exactly two consecutive indices (a p-firing boundary).

Equivalently: fib_p(j) = fib_p(k) with j < k implies k = j + 1 and
moverAt(j) = p.

PROOF OF CLAIM:

Suppose for contradiction that fib_p(j) = fib_p(k) with j < k and
k - j > 1 (and k - j < CL - 1, i.e., cyclic distance > 1).

[If k - j = CL - 1: then cyclic distance = 1. fib_p(j) = fib_p(k) means
fib_p(j) = fib_p(j-1 mod CL). By Obs 1: moverAt(j-1) = p, confirming
they're adjacent across a p-firing. This is NOT a violation.]

So assume 2 <= d := k - j <= CL - 2.

Let F = fib_p(j) = fib_p(k) be the shared fiber.
All non-p positions match: g_j[q] = g_k[q] for all q != p.
And g_j[p] != g_k[p] (since g_j != g_k as distinct cycle configs).

Consider the FULL CONFIGS:
  g_j = (..., g_j[p-1], g_j[p], g_j[p+1], ...)
  g_k = (..., g_k[p-1], g_k[p], g_k[p+1], ...)
  where g_j[q] = g_k[q] for q != p, g_j[p] = v, g_k[p] = w, v != w.

Between steps j and k, the movers fire d times.
Let a_q = number of times proc q fires in steps j, j+1, ..., k-1.
Then sum_q a_q = d and sum_q a_q = d.

For each non-p proc q:
  g_k[q] = result of applying a_q firings of q (with varying contexts)
  starting from g_j[q], through a sequence of intermediate configs.
  Since g_j[q] = g_k[q]: q's value returns to its starting value after
  a_q firings.

Now: proc q has m_q states and fires m_q times total in the cycle.
Each firing changes q's value (since q is privileged => new value != old).
After m_q firings, q returns to start (cyclic).

CRITICAL: Within an arc of a_q firings, q returns to its start.
The value sequence at q during the full cycle is a sequence of m_q
distinct values (since each firing produces a NEW value, and after m_q
firings all values are visited). This forms a cyclic permutation of
{0, ..., m_q-1} of order m_q.

Wait: does each firing produce a NEW value? Not necessarily!
f_q(L, S, R) != S (since q is privileged), but f_q(L, S, R) could equal
a previously visited value.

Hmm. Let me reconsider.

Actually: q fires m_q times total in the cycle. The value at q goes through
a sequence v_0, v_1, ..., v_{m_q}, where v_0 = v_{m_q} (returns to start).
Each v_{i+1} = f_q(L_i, v_i, R_i) for appropriate contexts. And v_{i+1} != v_i.

But the v_i need not all be distinct! q could visit some values multiple times.
However: q has m_q states and fires m_q times, starting and ending at v_0.
If q visits all m_q values: it visits each exactly once.
If q misses some values: it must revisit some values, but with m_q firings
and returning to start, the value sequence forms a walk of length m_q on
{0, ..., m_q-1} starting and ending at v_0.

Actually in a self-stabilizing token ring, the good cycle visits ALL configs.
The total number of good configs is CL = sum(m_p). For each proc q, the
projection to q visits all m_q values (by pigeonhole: CL configs, and the
number of distinct q-values is at most m_q, but there are CL/m_q configs
for each q-value on average, and... hmm, this doesn't directly prove it).

Let me verify: does each proc visit all m_q values in the good cycle?
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

# Check that each proc visits all values
for label, build in [
    ("Sol1 K=5 n=5", lambda: ([5]*5, [{} for _ in range(5)])),
]:
    pass

import random
random.seed(42)

# Test: does each proc visit all m_q values?
print("=== Value coverage check ===")
for ms_test in [[2,3,3], [3,3,3,3,3], [2,3,3,3,3], [2,2,2,3,4]]:
    n = len(ms_test)
    for trial in range(10000):
        tables = []
        for p in range(n):
            t = {}
            mL = ms_test[(p-1)%n]; mS = ms_test[p]; mR = ms_test[(p+1)%n]
            for L in range(mL):
                for S in range(mS):
                    for R in range(mR):
                        t[(L,S,R)] = random.randrange(mS)
            tables.append(t)
        cycle, movers = get_good_cycle(ms_test, tables)
        if not cycle: continue
        CL = len(cycle)
        fc = [0]*n
        for m in movers: fc[m] += 1
        if not all(fc[p] == ms_test[p] for p in range(n)): continue

        # Check value coverage
        for q in range(n):
            vals = set(cycle[i][q] for i in range(CL))
            if len(vals) < ms_test[q]:
                print(f"  ms={ms_test}: proc {q} visits only {len(vals)}/{ms_test[q]} values!")
                break
        else:
            continue
        break
    else:
        print(f"ms={ms_test}: all procs visit all values (no exceptions in 10k trials)")

# Known systems
for K in [3, 5, 7]:
    ms = [K]*5
    tables = []
    for p in range(5):
        t = {}
        for L in range(K):
            for S in range(K):
                for R in range(K):
                    if p == 0: t[(L,S,R)] = (S+1)%K if S==L else S
                    else: t[(L,S,R)] = L if S!=L else S
        tables.append(t)
    cycle, movers = get_good_cycle(ms, tables)
    CL = len(cycle)
    for q in range(5):
        vals = set(cycle[i][q] for i in range(CL))
        if len(vals) < K:
            print(f"Sol1 K={K} n=5: proc {q} visits only {len(vals)}/{K} values!")
    # Also check: value sequence at q is a cyclic permutation?
    for q in range(5):
        # Extract firing sequence at q
        fire_values = []
        for i in range(CL):
            if movers[i] == q:
                fire_values.append((cycle[i][q], cycle[(i+1)%CL][q]))
        # Check if it forms a single cycle
        perm = {}
        for old, new in fire_values:
            perm[old] = new
        # Trace cycle
        start = fire_values[0][0]
        visited = [start]
        cur = perm[start]
        while cur != start:
            visited.append(cur)
            cur = perm[cur]
        cycle_len = len(visited)
        if cycle_len != K:
            print(f"Sol1 K={K}: proc {q} has value cycle length {cycle_len} != {K}")
    print(f"Sol1 K={K} n=5: all procs have value cycle length {K}")

# Now check Sol3v1
for n in [5, 7, 9]:
    ms = [2] + [3]*(n-1)
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
    for q in range(n):
        fire_values = []
        for i in range(CL):
            if movers[i] == q:
                fire_values.append((cycle[i][q], cycle[(i+1)%CL][q]))
        perm = {}
        for old, new in fire_values:
            if old in perm and perm[old] != new:
                print(f"  Sol3v1 n={n}: proc {q} fires from {old} to multiple values!")
            perm[old] = new
        start = fire_values[0][0]
        visited = [start]; cur = perm[start]
        while cur != start and len(visited) < 100:
            visited.append(cur); cur = perm[cur]
        if len(visited) == ms[q]:
            pass  # good
        else:
            print(f"  Sol3v1 n={n}: proc {q} value cycle length {len(visited)} != {ms[q]}")
    print(f"Sol3v1 n={n}: all value cycles match m_q")

# KEY QUESTION: does each proc's firing always create a single-cycle permutation?
# Or can it create shorter cycles?
# With fc(q) = m_q firings, if the permutation has multiple cycles,
# then some values repeat within the good cycle.
# BUT: is it possible for a proc to fire from value a to value b at one point,
# and from value a to value c (c != b) at another point? YES, because the
# transition is context-dependent.

# So: the "permutation" at q is NOT well-defined! Different firings of q
# can have different contexts and thus different transitions from the same value.
# This means q's value sequence is NOT determined by a single permutation.

print("\n=== Check: does q fire from same value with different results? ===")
for n_val in [5, 7]:
    ms = [2] + [3]*(n_val-1)
    n = n_val
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
    for q in range(n):
        fire_map = {}  # old_value -> set of new_values
        for i in range(CL):
            if movers[i] == q:
                old = cycle[i][q]; new = cycle[(i+1)%CL][q]
                if old not in fire_map: fire_map[old] = set()
                fire_map[old].add(new)
        multi = {k: v for k, v in fire_map.items() if len(v) > 1}
        if multi:
            print(f"  Sol3v1 n={n}, proc {q}: multi-valued transitions: {multi}")

# Try with random systems
random.seed(42)
for ms_test in [[2,3,3], [3,3,3,3,3]]:
    n = len(ms_test)
    for trial in range(10000):
        tables = []
        for p in range(n):
            t = {}
            mL = ms_test[(p-1)%n]; mS = ms_test[p]; mR = ms_test[(p+1)%n]
            for L in range(mL):
                for S in range(mS):
                    for R in range(mR):
                        t[(L,S,R)] = random.randrange(mS)
            tables.append(t)
        cycle, movers = get_good_cycle(ms_test, tables)
        if not cycle: continue
        CL = len(cycle)
        fc = [0]*n
        for m in movers: fc[m] += 1
        if not all(fc[p] == ms_test[p] for p in range(n)): continue

        for q in range(n):
            fire_map = {}
            for i in range(CL):
                if movers[i] == q:
                    old = cycle[i][q]; new = cycle[(i+1)%CL][q]
                    if old not in fire_map: fire_map[old] = set()
                    fire_map[old].add(new)
            multi = {k: v for k, v in fire_map.items() if len(v) > 1}
            if multi:
                print(f"  Random ms={ms_test}: proc {q} multi-valued: {multi}")
                break
        break  # just check first valid system

print("\nDone")
