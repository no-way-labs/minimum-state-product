"""
H-1 Uniqueness proof investigation.

Key insight to explore: if g_j and g_k are Hamming-1 at position p,
then every proc q != p sees the SAME (L,S,R) context in both configs.
So the unique privileged proc is determined by non-p positions.

Case analysis:
1. moverAt(j) = q != p: then q is privileged in g_j.
   Since q != p, q sees same context in g_k => q privileged in g_k too.
   By unique privilege: moverAt(k) = q.
   So both steps fire at q. After firing:
   g_{j+1} and g_{k+1} differ at... p (unchanged, since q fires) and
   q changes by same amount (same context). So g_{j+1} and g_{k+1}
   are STILL Hamming-1 at p!

2. moverAt(j) = p: then p is privileged in g_j.
   In g_k, p has different value but same neighbors => may or may not be privileged.
   If p is privileged in g_k too: moverAt(k) = p.
   If p is NOT privileged in g_k: some other q is. But q sees same context
   in g_j => q is privileged in g_j too. Contradiction with unique privilege
   (g_j has both p and q privileged).
   So: moverAt(k) = p too.

Summary: if g_j, g_k are Hamming-1 at p, then moverAt(j) = moverAt(k).

Now let's trace what happens. Let moverAt(j) = moverAt(k) = q.

Case A: q != p.
  g_{j+1} = fire(g_j, q), g_{k+1} = fire(g_k, q).
  Since q's context is same: g_{j+1}[q] = g_{k+1}[q].
  For i != q, i != p: g_{j+1}[i] = g_j[i] = g_k[i] = g_{k+1}[i].
  For i = p: g_{j+1}[p] = g_j[p] != g_k[p] = g_{k+1}[p].
  So g_{j+1} and g_{k+1} are Hamming-1 at p.

Case B: q = p.
  g_{j+1} = fire(g_j, p), g_{k+1} = fire(g_k, p).
  For i != p: g_{j+1}[i] = g_j[i] = g_k[i] = g_{k+1}[i] (still agree).
  For i = p: g_{j+1}[p] = f(L, g_j[p], R), g_{k+1}[p] = f(L, g_k[p], R)
  where L = g_j[p-1] = g_k[p-1], R = g_j[p+1] = g_k[p+1].

  If g_{j+1}[p] != g_{k+1}[p]: Hamming-1 at p persists.
  If g_{j+1}[p] = g_{k+1}[p]: Hamming-0, i.e., g_{j+1} = g_{k+1}.

  If g_{j+1} = g_{k+1}: this means the cycle visits the same config twice.
  But good configs are DISTINCT in the cycle. So j+1 = k+1 mod CL,
  which means j = k mod CL. But j != k. Contradiction unless they're
  the same index. So: g_{j+1}[p] != g_{k+1}[p].

WAIT. g_{j+1} = g_{k+1} doesn't mean j+1 = k+1. It means the cycle
visits the same config at positions j+1 and k+1. But in a cycle,
each config appears exactly once. So j+1 ≡ k+1 (mod CL), i.e., j ≡ k (mod CL).
Since 0 ≤ j < k < CL: impossible. So indeed g_{j+1}[p] != g_{k+1}[p].

So: the Hamming-1 pair PROPAGATES! If (g_j, g_k) are Hamming-1 at p,
then (g_{j+1}, g_{k+1}) are also Hamming-1 at p.

This means: the relation "Hamming-1 at p" defines a PAIRING of cycle positions
that is preserved by the dynamics. If j pairs with k, then j+1 pairs with k+1,
j+2 pairs with k+2, etc.

So the offset d = k - j (mod CL) is constant: if ANY pair (g_j, g_k) is
Hamming-1 at p with offset d, then ALL (g_{j+t}, g_{k+t}) are also Hamming-1 at p.

This means: EVERY good config g_i is Hamming-1 at p with g_{i+d mod CL}.
So we have CL such pairs.

But how many Hamming-1 pairs at position p can there be?
Config g_i[p] takes values in {0, ..., m_p - 1}.
For g_i and g_{i+d} to be Hamming-1 at p: g_i[p] != g_{i+d}[p] and
g_i[q] = g_{i+d}[q] for all q != p.

The "propagation" argument shows that if ONE pair exists with offset d,
then ALL CL pairs at that offset are Hamming-1 at p.

Now: consider what this means for the mover sequence.
Since moverAt(j) = moverAt(k) = moverAt(j + d) for all j:
the mover sequence is periodic with period d!

If d | CL and the mover sequence has period d:
each proc fires exactly (fire_count_p * CL/d) / CL = fire_count_p / CL * CL
Hmm, let me think about this differently.

The mover sequence has period d. So moverAt(j) = moverAt(j+d) for all j.
The cycle length is CL. So d | CL (period divides cycle length).

Each proc p fires fire_count(p) = m_p times total in the cycle.
With period d: in each period of length d, proc p fires m_p * d / CL times.
Since m_p * d / CL must be an integer: CL | (m_p * d) for all p.

Now: the values at position p form a sequence g_0[p], g_1[p], ..., g_{CL-1}[p].
This sequence changes only when p fires (moverAt(i) = p).
The value at p goes through all m_p values exactly once (since fire_count = m_p
and it must return to start).

With the Hamming-1 pairing: g_i[p] != g_{i+d}[p] for ALL i.
But g_i[q] = g_{i+d}[q] for ALL i, ALL q != p.

For q != p: the sequence g_0[q], g_1[q], ..., g_{CL-1}[q] has period d.
This means: the value at q repeats every d steps.
Since q changes value only when moverAt(i) = q, and the mover sequence
has period d: q fires at the same points within each period.

q's values form a cycle of length m_q that repeats CL/d times within
the overall cycle. So m_q | d (the period of q's values divides d...
actually no: q fires m_q * d / CL times per period, and within that
period, q's value must return to start. So m_q | (m_q * d / CL),
which is always true. The value at q is periodic with period d.

OK let me just verify computationally that propagation works and think
about what values of d are possible.
"""

from itertools import product as iprod

def get_good_cycle(ms, tables):
    n = len(ms)
    def fire(config, p):
        L = config[(p-1)%n]; S = config[p]; R = config[(p+1)%n]
        new = list(config); new[p] = tables[p][(L,S,R)]
        return tuple(new)
    def privileged(config):
        ps = []
        for p in range(n):
            L = config[(p-1)%n]; S = config[p]; R = config[(p+1)%n]
            if tables[p][(L,S,R)] != S:
                ps.append(p)
        return ps
    good = {}
    for config in iprod(*[range(m) for m in ms]):
        ps = privileged(config)
        if len(ps) == 1:
            good[config] = ps[0]
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

# Verify propagation for Sol1 systems
def verify_propagation(ms, tables, label=""):
    cycle, movers = get_good_cycle(ms, tables)
    if not cycle: return
    CL = len(cycle); n = len(ms)

    # Find all H-1 pairs
    h1_by_offset = {}  # offset -> list of (j, p)
    for j in range(CL):
        for d in range(1, CL):
            k = (j + d) % CL
            if k <= j: continue  # avoid double counting
            diff = [i for i in range(n) if cycle[j][i] != cycle[k][i]]
            if len(diff) == 1:
                p = diff[0]
                if d not in h1_by_offset:
                    h1_by_offset[d] = []
                h1_by_offset[d].append((j, p))

    print(f"{label}: CL={CL}")
    if not h1_by_offset:
        # Only adjacent (d=1) pairs
        # Check d=1
        d1_pairs = []
        for j in range(CL):
            k = (j+1) % CL
            diff = [i for i in range(n) if cycle[j][i] != cycle[k][i]]
            if len(diff) == 1:
                d1_pairs.append((j, diff[0]))
        print(f"  d=1 pairs: {len(d1_pairs)} (should be {CL})")
        # Verify mover consistency
        for j, p in d1_pairs:
            assert movers[j] == p, f"d=1 pair at j={j} has p={p} but mover={movers[j]}"
        print(f"  All d=1 pairs have mover=p. GOOD.")
        return

    for d, pairs in sorted(h1_by_offset.items()):
        if d == 1:
            continue  # skip adjacent
        print(f"  *** d={d}: {len(pairs)} pairs ***")
        for j, p in pairs[:5]:
            print(f"    j={j}, p={p}, mover_j={movers[j]}, mover_{(j+d)%CL}={movers[(j+d)%CL]}")

# Test
for K in range(3, 10):
    for n in [3, 4, 5]:
        if K < n: continue
        ms = [K]*n
        tables = []
        for p in range(n):
            t = {}
            for L in range(K):
                for S in range(K):
                    for R in range(K):
                        if p == 0:
                            t[(L,S,R)] = (S+1)%K if S==L else S
                        else:
                            t[(L,S,R)] = L if S!=L else S
            tables.append(t)
        verify_propagation(ms, tables, f"Sol1 K={K} n={n}")

# Sol3v1
print("\n--- Sol3v1 ---")
for n in range(3, 10):
    ms = [2] + [3]*(n-1)
    tables = []
    for p in range(n):
        t = {}
        for L in range(ms[(p-1)%n]):
            for S in range(ms[p]):
                for R in range(ms[(p+1)%n]):
                    if p == 0:
                        t[(L,S,R)] = (S+1)%ms[p] if S==L else S
                    else:
                        t[(L,S,R)] = L if S!=L else S
        tables.append(t)
    verify_propagation(ms, tables, f"Sol3v1 n={n}")
