"""
H-1 Uniqueness — Tracking distance evolution.

Key question: if fib_p(j) = fib_p(k) with d = k-j >= 2,
what happens to the "fiber-matching distance" as we step forward?

Three scenarios at each step:
A) Both movers match and fiber propagates: distance preserved (d stays).
B) Movers diverge, j-chain keeps fiber F but k-chain loses it:
   restart with (j+1, k) — distance decreases to d-1.
C) Movers diverge, k-chain keeps fiber F but j-chain loses it:
   restart with (j, k+1) — distance increases to d+1.
D) Both chains lose fiber F: pair destroyed entirely.

If only A and B happen: distance monotonically decreases to 1. DONE.
If C happens: distance can increase. Could it cycle forever?

The distance d is bounded by CL. So it can't increase forever.
But could it oscillate? d -> d+1 -> d -> d+1 -> ...?

Let me trace this computationally for the n=2 counterexample.
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

# n=2 counterexample
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

    # Find violation
    for j0 in range(CL):
        for k0 in range(j0+1, CL):
            diff = [i for i in range(n) if cycle[j0][i] != cycle[k0][i]]
            if len(diff) == 1 and min(k0-j0, CL-(k0-j0)) > 1:
                p = diff[0]
                print(f"n=2 counterexample: CL={CL}, p={p}")
                for i in range(CL):
                    fib = tuple(cycle[i][q] for q in range(n) if q != p)
                    print(f"  [{i}] {cycle[i]} m={movers[i]} fib={fib}")

                # Track fiber matching from (j0, k0)
                print(f"\nTracking from j={j0}, k={k0}:")
                j, k = j0, k0
                for step in range(CL * 2):
                    fib_j = tuple(cycle[j%CL][q] for q in range(n) if q != p)
                    fib_k = tuple(cycle[k%CL][q] for q in range(n) if q != p)
                    d_fwd = (k - j) % CL
                    d_cyc = min(d_fwd, CL - d_fwd)
                    match = "MATCH" if fib_j == fib_k else "DIFF"
                    same_p = cycle[j%CL][p] == cycle[k%CL][p]
                    print(f"  step {step}: j={j%CL}, k={k%CL}, d={d_cyc}, fib {match}, same_p={same_p}")
                    print(f"    g_j={cycle[j%CL]}, m_j={movers[j%CL]}")
                    print(f"    g_k={cycle[k%CL]}, m_k={movers[k%CL]}")

                    if match == "MATCH" and not same_p:
                        # Still a Hamming-1 pair. Step forward.
                        # Both step forward by 1
                        j += 1; k += 1
                    else:
                        print(f"  Pair broken at step {step}")
                        break
                break
            if diff: break
    break

# Now: for n >= 3, can the pair survive? Let me trace hypothetically.
# At n >= 3, the propagation in Cases 1 and 2a preserves the pair.
# Cases 2b, 3 can break it.
# The question: is there a system at n >= 3 where the pair survives
# through enough steps to create a violation?

# At n >= 3 with the propagation, whenever moverAt(j) = moverAt(k):
# the pair propagates. When they diverge: the pair may break or shift.

# KEY INSIGHT: In cases where the pair SURVIVES but moverAt(j) != moverAt(k),
# one of them must be p and the other a neighbor of p.
# This means: the mover sequences at j and k DIVERGE at neighbors of p.
# But: the dynamics are deterministic given the config.
# Two configs that differ only at p WILL generally have different dynamics
# at neighbors of p (since those neighbors see p's value).
# So: at some point, the movers must diverge, and the pair breaks.
# Unless: the transition functions at neighbors of p are insensitive to
# p's value for the specific contexts encountered.

# That is: f_{p+1}(v, S, R) = f_{p+1}(w, S, R) for all encountered (S,R).
# And: f_{p-1}(L, S, v) = f_{p-1}(L, S, w) for all encountered (L,S).
# If these conditions hold at EVERY step: the pair propagates forever
# (moverAt(j) = moverAt(k) always), giving a period-d repetition.

# For n >= 3: this condition means that p's value is IRRELEVANT to its
# neighbors' transitions, for all contexts encountered in the good cycle.
# This is a very strong condition.

# Let me check: does this condition ever hold?
print("\n=== Neighbor insensitivity check ===")
for n_val in [5, 7]:
    ms = [2] + [3]*(n_val-1)
    n = n_val
    tables = []
    for pp in range(n):
        t = {}
        for L in range(ms[(pp-1)%n]):
            for S in range(ms[pp]):
                for R in range(ms[(pp+1)%n]):
                    if pp == 0: t[(L,S,R)] = (S+1)%ms[pp] if S==L else S
                    else: t[(L,S,R)] = L if S!=L else S
        tables.append(t)
    cycle, movers = get_good_cycle(ms, tables)
    CL = len(cycle)

    # For each position p, check if neighbors are insensitive to p's value
    for p in range(n):
        p_minus = (p-1) % n
        p_plus = (p+1) % n

        # Check p_plus: does f_{p+1}(v, S, R) depend on v for encountered (S,R)?
        plus_sensitive = False
        encountered_SR = set()
        for i in range(CL):
            S = cycle[i][p_plus]
            R = cycle[i][(p_plus+1)%n]
            encountered_SR.add((S, R))

        for S, R in encountered_SR:
            vals = set()
            for v in range(ms[p]):
                vals.add(tables[p_plus][(v, S, R)])
            if len(vals) > 1:
                plus_sensitive = True
                break

        # Check p_minus: does f_{p-1}(L, S, v) depend on v for encountered (L,S)?
        minus_sensitive = False
        encountered_LS = set()
        for i in range(CL):
            L = cycle[i][(p_minus-1)%n]
            S = cycle[i][p_minus]
            encountered_LS.add((L, S))

        for L, S in encountered_LS:
            vals = set()
            for v in range(ms[p]):
                vals.add(tables[p_minus][(L, S, v)])
            if len(vals) > 1:
                minus_sensitive = True
                break

        insensitive = not plus_sensitive and not minus_sensitive
        if insensitive:
            print(f"  Sol3v1 n={n}: pos {p} neighbors INSENSITIVE to p's value!")
        # else: print(f"  Sol3v1 n={n}: pos {p} neighbors sensitive (good)")

    print(f"  Sol3v1 n={n}: all positions have sensitive neighbors")
