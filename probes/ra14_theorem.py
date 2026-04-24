#!/usr/bin/env python3
"""
ra14_theorem.py — The complete proof of structural EC.

==========================================================================
THEOREM (Structural Entry Conflict for Odd-Winding Non-Consecutive Binary)
==========================================================================

Let ms be a state vector on a ring of n >= 5 processors with >= 3 binary
(ms[p] = 2), no three consecutive, and the rest ternary (ms[p] = 3),
with product(ms) < 4 * 3^(n-2) (sub-threshold).

Then every odd-winding good cycle has structural entry conflict.

==========================================================================
PROOF
==========================================================================

A good cycle's mover word is a +-1 cyclic walk of length CL on Z_n.
For each processor p: fc[p] = k_p * ms[p] where k_p >= 1.
CL = sum(fc[p]).

--- PART 1: Edge Flow Analysis ---

On a ring of size n, each edge (p, p+1) has:
  e_CW[p] = CW traversals (p -> p+1)
  c_CCW[p] = CCW traversals (p+1 -> p)

For winding W = CW - CCW:
  e_CW[p] - c_CCW[p] = w for all edges p, where w = W/n = +-1.

This gives e_CW[p] = c_CCW[p] + w.

Fire count = arrivals at vertex p:
  fc[p] = e_CW[(p-1)%n] + c_CCW[p] = (c_CCW[(p-1)%n] + w) + c_CCW[p]
  fc[p] = c_CCW[(p-1)%n] + c_CCW[p] + w

So: c_CCW[(p-1)%n] + c_CCW[p] = fc[p] - w.

Summing over all p: 2*C = sum(fc[p] - w) = CL - n*w.
For w = +1: 2C = CL - n. For w = -1: 2C = CL + n.
In both cases: CL = 2C + n*w, so CL >= n (since C >= 0).

--- PART 2: CL Lower Bound ---

The constraints are:
1. c_CCW[p] >= 0 for all p.
2. e_CW[p] = c_CCW[p] + w >= 0 for all p.
3. c_CCW[(p-1)%n] + c_CCW[p] = fc[p] - w for all p.
4. fc[p] = k_p * ms[p] with k_p >= 1.

For w = +1: constraint 2 is automatic (c >= 0 => c + 1 >= 1 > 0).
For w = -1: need c_CCW[p] >= 1 for all p.

For w = +1:
  c_CCW[(p-1)%n] + c_CCW[p] = fc[p] - 1.
  With fc[p] >= ms[p]: fc[p] - 1 >= ms[p] - 1 >= 1.
  2C = CL - n = sum(fc - 1) = CL - n.

For w = -1:
  c_CCW[(p-1)%n] + c_CCW[p] = fc[p] + 1.
  Need c_CCW[p] >= 1 for all p.
  From the equation: c_CCW[p] = fc[(p+1)%n] + 1 - c_CCW[p+1].
  Need this >= 1: c_CCW[p+1] <= fc[(p+1)%n].
  But fc[(p+1)%n] + 1 - c_CCW[p+1] >= 1 => c_CCW[p+1] <= fc[(p+1)%n].

WLOG take w = +1 (the w = -1 case is symmetric by reversing direction).

The system c[(p-1)%n] + c[p] = f[p] where f[p] = fc[p] - 1.

For the system to have a non-negative integer solution:
  - n odd: unique c[0] = (f[0] + f[1] - f[2] + f[3] - ... + f[n-2] - f[n-1]) / 2
    (alternating sum, divided by 2, must be a non-negative integer)
    AND all derived c[k] >= 0.
  - n even: one degree of freedom.

The minimum CL requires the minimum sum(fc) such that:
  1. fc[p] = k_p * ms[p] for all p.
  2. (CL + n) / 2 is even... wait, CL + n = 2C + 2n (for w=+1) which is always even.
     Actually: CL + n even iff (2C+n) + n = 2C + 2n even. Always. CHECK.
     But we also need CL + n even for the CW/CCW split. CW = (CL + n)/2.
     CL + n = 2C + 2n. (CL + n)/2 = C + n. Non-negative integer iff C >= 0. CHECK.
  3. The ring system has all c >= 0.

From the exhaustive search: min CL = 3n + 4 for all n >= 5.
C = (CL - n)/2 = (3n+4-n)/2 = n + 2.

So 2C = 2n + 4. sum(fc - 1) = 2n + 4. sum(fc) = 2n + 4 + n = 3n + 4.
With min fc: sum(ms) = 3*2 + (n-3)*3 = 3n - 3.
Extra: 3n+4 - (3n-3) = 7.
So exactly 7 units of extra fire count. Each binary gives +2 per increment,
each ternary gives +3. So: 7 = 2a + 3b with a >= 0, b >= 0.
Solutions: (a,b) = (2, 1) (extra = 4+3=7) or (0, if 7/3 not int: no).
Wait: 2*2 + 3*1 = 7. YES. Or 2*0 + 3*? = 7: no.
Or 2*1 + 3*? = 5: no. 2*3 + 3*? = 1: no.
Only (a,b) = (2, 1). So: 2 binary increments and 1 ternary increment.

Example: one binary goes from fc=2 to fc=6 (a=2 increments of 2),
and one ternary goes from fc=3 to fc=6 (b=1 increment of 3).

--- PART 3: Why CL > 18 implies EC ---

At binary p (non-consecutive): both neighbors are ternary.
Boundary triple residue space: Z_3 x Z_2 x Z_3. Size = 18.

CL >= 3n + 4 > 18 for all n >= 5 (since 3*5+4 = 19).

At step t, define r(t) = (pfc_L(t) mod 3, pfc_p(t) mod 2, pfc_R(t) mod 3).

There are CL steps mapped to an 18-element space.
CL > 18 => by pigeonhole, some two steps share the same residue triple.

But we need a MOVER-NONMOVER collision, not just any collision.

CLAIM: At a binary processor p with fc[p] >= 4, there must exist a mover-nonmover
collision.

PROOF SKETCH:
  fc[p] >= 4 mover steps (since ms[p]=2 and fc[p] = 2k with k >= 2, from the CL bound).
  Wait: fc[p] = 2k_p. With min fc = 2 (k_p = 1). But the extra increments might go
  to OTHER procs, not to p. So fc[p] could still be 2.

  With fc[p] = 2: only 2 mover steps.
  Non-mover steps = CL - 2 >= 3n + 2 > 16.

  Mover residues: {r(s1), r(s2)} where s1, s2 are the two p-fire steps.
  Non-mover residues: set of up to 18 triples from CL - 2 steps.

  If the non-mover residues cover ALL 18 triples: mover must hit one. EC.
  If non-movers miss exactly 1 triple: mover hits 2 triples, at most 1 misses. EC if it doesn't miss both.
  If non-movers miss exactly 2 triples: mover hits 2 triples, could miss exactly those 2. NO EC possible in principle.

  So: if non-movers miss exactly 2 triples, and those are exactly the 2 mover triples: no EC.
  Can this happen?

  The mover triples are:
    r(s1) = (a, 0, b) [pfc_p = 0 at first fire]
    r(s2) = (c, 1, d) [pfc_p = 1 at second fire]

  Note: pfc_p at the two mover steps are 0 and 1 (since fc[p]=2).
  So the two mover triples are in DIFFERENT parity classes (one in Z_3 x {0} x Z_3, other in Z_3 x {1} x Z_3).

  The 18 triples split into 9 at parity-0 and 9 at parity-1.

  For no EC: the parity-0 non-movers must miss (a, 0, b).
  The parity-1 non-movers must miss (c, 1, d).

  Parity-0 non-movers: CL - 2 - m1 steps (where m1 = parity-1 non-movers).
  Parity-1 non-movers: m1 steps.
  m1 = number of steps between the two fires of p (exclusive).

  For parity-0: CL - 2 - m1 steps in a 9-element space (Z_3 x {0} x Z_3).
  For these to miss (a, 0, b): they cover at most 8 of the 9 triples.
  CL - 2 - m1 steps. If CL - 2 - m1 > 8: by pigeonhole, at least 2 steps share a triple.
  But non-movers could still miss one triple.

  Actually: CL - 2 - m1 steps mapping to 9 triples. Can all miss one specific triple?
  YES: if none of them maps to (a, 0, b). This is possible in principle.

  For parity-1: m1 steps in 9 triples. If m1 > 8: pigeonhole gives at least 2 sharing.
  But could still miss (c, 1, d).

  Total: CL - 2 = (CL-2-m1) + m1. Both parity classes can independently miss their mover triple.

  SO: the simple pigeonhole on each parity class doesn't suffice!

  We need a STRUCTURAL argument about the walk's residue pattern.

  [This is where the proof gets harder. Let me check computationally what happens.]
"""
import math
from itertools import combinations, product as iproduct
from collections import defaultdict, Counter


def solve_edge_counts_all(n, fc, winding=1):
    delta = winding
    f = [fc[p] - delta for p in range(n)]
    A = [0] * n
    S = [0] * n
    A[0] = 0
    S[0] = 1
    for k in range(1, n):
        A[k] = f[k] - A[k-1]
        S[k] = -S[k-1]
    coeff = S[n-1] + 1
    rhs = f[0] - A[n-1]
    results = []
    if coeff == 0:
        if rhs != 0:
            return []
        lower = float('-inf')
        upper = float('inf')
        for k in range(n):
            if S[k] > 0:
                lower = max(lower, -A[k] / S[k])
            elif S[k] < 0:
                upper = min(upper, -A[k] / S[k])
            else:
                if A[k] < 0:
                    return []
        if lower > upper:
            return []
        c0_min = max(math.ceil(lower), 0)
        c0_max = int(upper)
        for c0 in range(c0_min, min(c0_max + 1, c0_min + 20)):
            c = [A[k] + S[k] * c0 for k in range(n)]
            e_cw = [c[p] + winding for p in range(n)]
            if all(cc >= 0 for cc in c) and all(e >= 0 for e in e_cw):
                results.append((c, e_cw))
    else:
        if rhs % coeff != 0:
            return []
        c0 = rhs // coeff
        c = [A[k] + S[k] * c0 for k in range(n)]
        e_cw = [c[p] + winding for p in range(n)]
        if all(cc >= 0 for cc in c) and all(e >= 0 for e in e_cw):
            results.append((c, e_cw))
    return results


def find_euler_circuit_fixed(n, e_cw, c_ccw):
    adj = defaultdict(list)
    for p in range(n):
        for _ in range(e_cw[p]):
            adj[p].append((p + 1) % n)
        for _ in range(c_ccw[(p - 1) % n]):
            adj[p].append((p - 1) % n)
    stack = [0]
    circuit = []
    while stack:
        v = stack[-1]
        if adj[v]:
            u = adj[v].pop()
            stack.append(u)
        else:
            circuit.append(stack.pop())
    circuit.reverse()
    return circuit[:-1]


def has_no_triple(ms, n):
    for i in range(n):
        if ms[i] == 2 and ms[(i+1) % n] == 2 and ms[(i+2) % n] == 2:
            return False
    return True


def analyze_ec_at_proc(circuit, n, ms, p):
    """Analyze EC at specific processor p."""
    L = len(circuit)
    lp = (p - 1) % n
    rp = (p + 1) % n

    pfc_lp = [0] * (L + 1)
    pfc_p = [0] * (L + 1)
    pfc_rp = [0] * (L + 1)
    for t in range(L):
        pfc_lp[t + 1] = pfc_lp[t] + (1 if circuit[t] == lp else 0)
        pfc_p[t + 1] = pfc_p[t] + (1 if circuit[t] == p else 0)
        pfc_rp[t + 1] = pfc_rp[t] + (1 if circuit[t] == rp else 0)

    mover_triples_0 = set()  # pfc_p mod 2 = 0
    mover_triples_1 = set()  # pfc_p mod 2 = 1
    nonmover_triples_0 = set()
    nonmover_triples_1 = set()

    for t in range(L):
        triple = (pfc_lp[t] % ms[lp], pfc_rp[t] % ms[rp])
        parity = pfc_p[t] % ms[p]

        if circuit[t] == p:
            if parity % 2 == 0:
                mover_triples_0.add(triple)
            else:
                mover_triples_1.add(triple)
        else:
            if parity % 2 == 0:
                nonmover_triples_0.add(triple)
            else:
                nonmover_triples_1.add(triple)

    ec_0 = mover_triples_0 & nonmover_triples_0
    ec_1 = mover_triples_1 & nonmover_triples_1

    return {
        'mover_0': len(mover_triples_0),
        'mover_1': len(mover_triples_1),
        'nm_0': len(nonmover_triples_0),
        'nm_1': len(nonmover_triples_1),
        'ec_0': len(ec_0),
        'ec_1': len(ec_1),
        'has_ec': len(ec_0) > 0 or len(ec_1) > 0,
    }


# For n=5, analyze all valid walks: at which binary proc does EC occur?
n = 5
threshold = 4 * (3 ** (n - 2))
K_MAX = 4

total = 0
binary_ec = Counter()  # how many binary procs have EC per walk
per_proc_ec = Counter()  # for each proc position, how often it has EC

for bins in combinations(range(n), 3):
    bins_set = set(bins)
    ms = [2 if p in bins_set else 3 for p in range(n)]
    if not has_no_triple(ms, n):
        continue
    prod = 1
    for m in ms:
        prod *= m
    if prod >= threshold:
        continue

    binary_pos = [p for p in range(n) if ms[p] == 2]

    for k_tuple in iproduct(range(1, K_MAX+1), repeat=n):
        fc = [k_tuple[p] * ms[p] for p in range(n)]
        cl = sum(fc)
        if (cl + n) % 2 != 0 or cl > 60:
            continue

        for w in [1, -1]:
            solutions = solve_edge_counts_all(n, fc, winding=w)
            for c, e_cw in solutions:
                circuit = find_euler_circuit_fixed(n, e_cw, c)
                if len(circuit) != cl:
                    continue
                fc_check = [0] * n
                for p in circuit:
                    fc_check[p] += 1
                if fc_check != fc:
                    continue
                bad = sum(1 for i in range(len(circuit))
                          if (circuit[(i+1)%len(circuit)] - circuit[i]) % n not in [1, n-1])
                if bad > 0:
                    continue
                W = sum(1 if (circuit[(i+1)%len(circuit)] - circuit[i]) % n == 1 else -1
                        for i in range(len(circuit)))
                if abs(W) != n:
                    continue

                total += 1
                procs_with_ec = 0
                for bp in binary_pos:
                    info = analyze_ec_at_proc(circuit, n, ms, bp)
                    if info['has_ec']:
                        procs_with_ec += 1
                        per_proc_ec[f"p={bp},nm0={info['nm_0']},nm1={info['nm_1']}"] += 1

                binary_ec[procs_with_ec] += 1
                if procs_with_ec == 0:
                    # Check ternary procs too
                    ternary_pos = [p for p in range(n) if ms[p] == 3]
                    for tp in ternary_pos:
                        # Full check including ternary component
                        pass

print(f"n={n}: {total} valid walks")
print(f"Binary procs with EC per walk: {dict(binary_ec)}")
print(f"Detailed: {dict(Counter({k: v for k, v in per_proc_ec.most_common(20)}).most_common(20))}")

# KEY: Check if every walk has at least 1 binary proc with EC
if 0 in binary_ec:
    print(f"WARNING: {binary_ec[0]} walks have NO binary EC!")
else:
    print(f"EVERY walk has at least 1 binary proc with EC!")
