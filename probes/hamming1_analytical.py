"""
Analytical proof: H-1 Uniqueness via Arc Return.

The key observation: Lemma 2 says a_q in {0, m_q} for q != p.
This means d = a_p + sum of a SUBSET of {m_q : q != p}.
With a_p in {1,...,m_p-1}.

Question: for which d values does a valid subset exist?

For ms in {2,3}: let b = number of binary procs, t = n-b ternary procs.
CL = 2b + 3t.

d = a_p + 2*|S ∩ binary| + 3*|S ∩ ternary|  (where S is the "fires m_q times" set)

with a_p in {1,...,m_p-1} and S ⊆ {0,...,n-1}\{p}.

If p is binary (m_p=2): a_p = 1.
If p is ternary (m_p=3): a_p in {1, 2}.

So d = a_p + 2s_2 + 3s_3 where s_2 in {0,...,b-1_or_b} (binary procs in S excluding p)
and s_3 in {0,...,t-1_or_t} (ternary procs in S excluding p).

The valid d values are:
  {a_p + 2s_2 + 3s_3 : 0 ≤ s_2 ≤ b', 0 ≤ s_3 ≤ t'}
where b' = b - [p is binary] and t' = t - [p is ternary].

For ADJACENCY: d=1 or d=CL-1.
d=1: a_p=1, s_2=0, s_3=0. Works when m_p >= 2 (always).
d=CL-1: then CL-d = 1, so complement arc has a_p'=m_p-a_p in {1,...,m_p-1},
  and all OTHER procs fire 0 times in complement → fire m_q in the arc.
  So s_2=b', s_3=t'. d = a_p + 2b' + 3t' = a_p + (CL - m_p).
  CL-1 = a_p + CL - m_p → a_p = m_p - 1. Works.

For d=2: a_p + 2s_2 + 3s_3 = 2.
  If a_p=1: 2s_2 + 3s_3 = 1. Only s_2=0,s_3=0 gives 0, too small.
    No s_2, s_3 >= 0 with 2s_2+3s_3 = 1. IMPOSSIBLE.
  If a_p=2 (m_p=3): 2s_2 + 3s_3 = 0. s_2=s_3=0. So d=2 with a_p=2, no others fire.
    This means p fires 2 out of 3 times in 2 steps, all other procs fire 0.
    Both movers in the arc are p. Possible.

  So d=2 requires m_p=3 and p fires twice consecutively.

For d=3: a_p + 2s_2 + 3s_3 = 3.
  a_p=1: 2s_2 + 3s_3 = 2. s_2=1,s_3=0: d=3. Possible if b' >= 1.
  a_p=1: 2s_2 + 3s_3 = 2. s_2=0,s_3=? No solution.
  a_p=2: 2s_2 + 3s_3 = 1. No solution.
  So d=3 is possible only with a_p=1 and s_2=1 (one binary proc fires m_q=2 times).

For d=4: a_p + 2s_2 + 3s_3 = 4.
  a_p=1: 2s_2 + 3s_3 = 3. s_2=0,s_3=1: d=4. Or s_2=1,s_3=? 2+3s_3=3, no.
    Wait: s_3=1 gives 3, so 2s_2=0, s_2=0. d=1+3=4.
    Or: s_2=1, 3s_3=1, no.
  a_p=1: s_2=0,s_3=1: d=4. Possible if t' >= 1.
  a_p=2: 2s_2+3s_3=2. s_2=1,s_3=0: d=4. Possible.

So many d values are reachable. Lemma 2 alone does NOT force d=1.

But the H-1 condition provides additional constraints beyond Lemma 2!
Specifically: not just the FIRE COUNT matters, but the VALUE return.

Actually, Lemma 2 IS about value return. For q != p with a_q in {0, m_q}:
  a_q = 0: q doesn't fire in the arc → q's value is constant → g_j[q] = g_k[q]. ✓
  a_q = m_q: q fires all m_q times → by Value Coverage, visits all values
    and returns to start → g_j[q] = g_k[q]. ✓

So Lemma 2 is necessary and sufficient for value return (given Lemma 1).

The question is: are there constraints BEYOND value return?

YES: the cycle must be a VALID good cycle from a self-stabilizing system.
The transition function f_i(L,S,R) must be deterministic.
Mover uniqueness: at each step, exactly 1 proc is privileged.

BUT the H-1 Uniqueness Lemma as stated only assumes:
  - m_i in {2,3}
  - fc(i) = m_i
  - gcd(ms) = 1
  - good cycle (each config has unique mover)

It does NOT assume a specific transition function.
So if abstract cycles with these properties have non-adjacent H-1 pairs,
the lemma is FALSE for abstract cycles.

Let me check: do the n=2 examples (ms=(2,3)) satisfy ALL conditions?
"""

import itertools
from math import gcd
from functools import reduce

def hamming_distance(c1, c2):
    return sum(1 for a, b in zip(c1, c2) if a != b)

# n=2, ms=(2,3), CL=5
ms = [2, 3]
n = 2
CL = 5
g = reduce(gcd, ms)
print(f"ms={ms}, n={n}, CL={CL}, gcd={g}")

# Generate all valid abstract good cycles
# Cycle: (c_0, m_0), (c_1, m_1), ..., (c_{CL-1}, m_{CL-1})
# where c_{s+1} differs from c_s only at position m_s,
# c_{CL} = c_0, all c_s distinct, fc(i) = m_i.

# Also: each config must have EXACTLY ONE proc that is "the mover".
# In abstract terms: the mover is determined by the config (not by a global rule).
# But for abstract cycles, the mover IS defined by position in the cycle.
# The "exactly one privileged" constraint means: the transition function
# would have exactly one privileged proc at each config.

# For our purposes: the abstract cycle defines a function config → mover.
# This is consistent as long as no config appears twice (already guaranteed by
# all configs distinct).

# So the abstract cycle is fully defined by:
# - mover word (which proc fires at each step)
# - start config
# - value changes at each step

# All 60 cycles we found earlier are valid abstract good cycles.
# They satisfy gcd=1, fc=m_i, all configs distinct.

# The question: do they satisfy Value Coverage (Lemma 1)?

def check_value_coverage(configs, ms):
    n = len(ms)
    for q in range(n):
        vals = set(c[q] for c in configs)
        if len(vals) != ms[q]:
            return False
    return True

# Re-enumerate
def enumerate_mover_words(ms):
    base = []
    for i in range(len(ms)):
        base.extend([i]*ms[i])
    return set(itertools.permutations(base))

all_cfgs = [(a, b) for a in range(2) for b in range(3)]
mover_words = list(enumerate_mover_words(ms))

all_cycles = []
for word in mover_words:
    for start in all_cfgs:
        stack = [(0, start, [start])]
        while stack:
            step, current, path = stack.pop()
            if step == CL:
                if current == start and len(set(path[:CL])) == CL:
                    all_cycles.append((word, path[:CL]))
                continue
            mover = word[step]
            for new_val in range(ms[mover]):
                if new_val != current[mover]:
                    new_cfg = list(current)
                    new_cfg[mover] = new_val
                    stack.append((step+1, tuple(new_cfg), path + [tuple(new_cfg)]))

print(f"Total valid abstract cycles: {len(all_cycles)}")

# Check Value Coverage for all
vc_pass = 0
vc_fail = 0
nonadj_with_vc = 0
nonadj_without_vc = 0

for word, configs in all_cycles:
    vc = check_value_coverage(configs, ms)
    if vc: vc_pass += 1
    else: vc_fail += 1

    # Check for non-adjacent H-1 pairs
    has_nonadj = False
    for j in range(CL):
        for k in range(j+1, CL):
            if hamming_distance(configs[j], configs[k]) == 1:
                d = k - j
                if 1 < d < CL - 1:
                    has_nonadj = True
                    break
        if has_nonadj:
            break

    if has_nonadj:
        if vc:
            nonadj_with_vc += 1
        else:
            nonadj_without_vc += 1

print(f"Value Coverage pass: {vc_pass}, fail: {vc_fail}")
print(f"Non-adj H-1 WITH VC: {nonadj_with_vc}")
print(f"Non-adj H-1 WITHOUT VC: {nonadj_without_vc}")

# Show examples
if nonadj_with_vc > 0:
    print("\n*** Non-adj H-1 pairs WITH Value Coverage exist! ***")
    for word, configs in all_cycles:
        if not check_value_coverage(configs, ms):
            continue
        for j in range(CL):
            for k in range(j+1, CL):
                if hamming_distance(configs[j], configs[k]) == 1:
                    d = k - j
                    if 1 < d < CL - 1:
                        p = [i for i in range(n) if configs[j][i] != configs[k][i]][0]
                        arc_fc = [0]*n
                        for t in range(d):
                            arc_fc[word[(j+t)%CL]] += 1
                        l2 = all(arc_fc[q] in [0, ms[q]] for q in range(n) if q != p)
                        print(f"  word={word}, configs={configs}")
                        print(f"  j={j},k={k},p={p},d={d}, arc_fc={arc_fc}, Lemma2={l2}")
                        # Check Value Coverage per-value
                        for q in range(n):
                            vals = [c[q] for c in configs]
                            print(f"    proc {q}: values={vals} (m={ms[q]})")
                        break
            else:
                continue
            break
        else:
            continue
        break

print("\n" + "=" * 70)
print("DIAGNOSIS: n=2 is degenerate")
print("=" * 70)
print("""
At n=2: each proc has exactly ONE neighbor (the other proc).
The contexts are (c[other], c[self], c[other]) — L and R are the SAME.
This means the ring is equivalent to a 2-node bidirectional link,
not a proper ring.

For n >= 3: each proc has DISTINCT L and R neighbors.
The H-1 condition at position p affects 3 distinct positions: p-1, p, p+1.
The mover divergence analysis with {p-1, p, p+1} as 3 distinct procs
doesn't apply at n=2 where p-1 = p+1.

The LB proof only needs n >= 5 (actually n >= 9).
So n=2 is irrelevant. Let me focus on proving the result for n >= 3.

For n >= 3 with ms containing both 2 and 3 (so gcd = 1):
The question is whether non-adjacent H-1 pairs exist in abstract cycles
satisfying Value Coverage.
""")

# ============================================================
# Key analytical insight for n >= 3
# ============================================================
print("=" * 70)
print("ANALYTICAL PROOF for n >= 3")
print("=" * 70)
print("""
CLAIM: For n >= 3, ms with m_i in {2,3}, gcd(ms) = 1, any good cycle
with fc(i) = m_i satisfying Value Coverage: non-adjacent H-1 pairs
imply mover periodicity, which contradicts gcd = 1.

PROOF:

Let g_j, g_k be H-1 at position p, d = k - j with 1 < d < CL - 1.

By Lemma 2: a_q in {0, m_q} for q != p.
Let S = {q != p : a_q = m_q}.
d = a_p + sum_{q in S} m_q, with 0 < a_p < m_p.

STEP 1: Show moverAt(j+t) = moverAt(k+t) for all t.

Consider configs g_{j+t} and g_{k+t} for t = 0, 1, 2, ...

At t=0: H(g_j, g_k) = 1 at position p.

At t=1: g_{j+1} = fire(g_j, moverAt(j)), g_{k+1} = fire(g_k, moverAt(k)).

If moverAt(j) is not in {p-1, p, p+1}: same context in g_j and g_k,
so moverAt(j) is privileged in both. Since each has exactly 1 mover:
moverAt(k) = moverAt(j). Same proc fires in both, same result (value
changes are identical since all non-p positions agree). So:
  H(g_{j+1}, g_{k+1}) = 1 at SAME position p. (*)

If moverAt(j) IS in {p-1, p, p+1}: the context differs between g_j and g_k.

Case A: moverAt(j) = p.
  In g_j: f_p(a, v, b) != v (privileged). New value v' = f_p(a, v, b).
  In g_k: f_p(a, w, b) — is p privileged? f_p(a, w, b) != w iff p privileged in g_k.

  p's privilege status can differ between g_j and g_k.

  Sub-case A1: p is privileged in both g_j and g_k.
    If moverAt(j) = moverAt(k) = p: both fire p.
    g_{j+1}[p] = f_p(a, v, b) = v' ≠ v.
    g_{k+1}[p] = f_p(a, w, b) = w' ≠ w.
    All other positions unchanged: g_{j+1}[q] = g_j[q] = g_k[q] = g_{k+1}[q].
    So H(g_{j+1}, g_{k+1}) = [v' ≠ w']. If v' = w': H = 0, cycle has period d. ✓
    If v' ≠ w': H = 1 at p. Defect stays. (*)

  Sub-case A2: p privileged in g_j but NOT in g_k.
    Then some OTHER proc must be the mover in g_k. Call it m_d.
    m_d is in {p-1, p, p+1} (since all other procs have same context).
    m_d != p (by assumption). So m_d in {p-1, p+1}.

    For n >= 3: p-1 ≠ p+1 (distinct positions).

    In g_j: only p is privileged. So p-1 and p+1 are NOT privileged in g_j.
    Context of p-1 in g_j: (g_j[p-2], g_j[p-1], g_j[p]) = (g_j[p-2], g_j[p-1], v).
    Context of p-1 in g_k: (g_k[p-2], g_k[p-1], g_k[p]) = (g_j[p-2], g_j[p-1], w).
    p-1 not privileged in g_j: f_{p-1}(g_j[p-2], g_j[p-1], v) = g_j[p-1].
    p-1 privileged in g_k: f_{p-1}(g_j[p-2], g_j[p-1], w) ≠ g_j[p-1].

    If m_d = p-1:
    g_{j+1} fires p: g_{j+1}[p] = v', all else same.
    g_{k+1} fires p-1: g_{k+1}[p-1] = f_{p-1}(..., w) ≠ g_k[p-1].
    g_{k+1}[p] = g_k[p] = w (p didn't fire in g_k).

    Now compare g_{j+1} and g_{k+1}:
    - Position p: v' vs w. May or may not differ.
    - Position p-1: g_j[p-1] vs g_{k+1}[p-1] ≠ g_j[p-1]. DIFFER.
    - All others: same.

    So H(g_{j+1}, g_{k+1}) >= 1 (at p-1).
    If v' ≠ w: H = 2 (at p-1 and p). HAMMING INCREASED.
    If v' = w: H = 1 (only at p-1). DEFECT SHIFTED from p to p-1.

    Similarly for m_d = p+1: H increases or defect shifts to p+1.

Case B: moverAt(j) = p-1.
  Similarly, moverAt(j) = p-1 in g_j.
  Context of p-1 in g_j: (g_j[p-2], g_j[p-1], v). Privileged.
  Context of p-1 in g_k: (g_j[p-2], g_j[p-1], w). May or may not be privileged.

  If privileged in both: both fire p-1, same analysis as above.
  If only in g_j: moverAt(k) must be p or p+1.

Case C: moverAt(j) = p+1. Symmetric to B.

SUMMARY: At each step, either:
(i) Movers agree, defect stays at p (or H drops to 0 → period d). (*)
(ii) Movers disagree, H increases to 2. (**)
(iii) Movers disagree, defect shifts to p±1 (H stays 1). (***)

For the mover-periodicity argument: if (i) holds for ALL t,
then moverAt(s) has period d, and GCD kills it.

For (iii): the defect propagates. After enough steps, the defect
circles back to p. For this to be consistent:
  - The defect must move around the ring (shifting position each step)
  - After n shifts (or 2n, or...), it returns to p
  - The value at the "defect position" must be consistent with the cycle.

The Dijkstra Sol1 examples show this CAN happen with gcd(ms) = n.
But with gcd = 1, can it happen?

THE KEY CONSTRAINT: Lemma 2 applies at EVERY starting point.

If g_{j+t} and g_{k+t} are H-1 at position p_t, then Lemma 2 applies
to the arc from j+t to k+t. So for each q ≠ p_t: the fire count
of q in the arc {j+t, ..., k+t-1} is in {0, m_q}.

But the fire count in the arc {j+t, ..., k+t-1} is the same set
of movers as {j, ..., k-1} shifted by t. The fire count of proc q
in this shifted arc is determined by the mover word.

If the defect position p_t changes with t, then the "excluded proc"
in Lemma 2 changes. This means different procs have the {0, m_q}
constraint at different starting points.

Can this be simultaneously satisfiable? For the Dijkstra Sol1 sweep:
mover word = 0, 1, 2, 0, 1, 2, 0, 1, 2 (periodic with period 3 = n).
H-1 pairs have d=1 (adjacent) or d=CL-1 (anti-adjacent).
For d=1: a_q = 0 for q ≠ moverAt(j). a_p = 1. Lemma 2 trivially OK.
For d=CL-1: a_q = m_q for all q ≠ p, a_p = m_p - 1. Lemma 2 OK.
No non-adjacent H-1 pairs with 1 < d < CL-1.

So even in Dijkstra Sol1, the H-1 Uniqueness holds!
(It only has adjacent pairs.)

But at n=2: we found d=2, 3, 4 (non-adjacent, non-anti-adjacent).
These satisfy Lemma 2 because n=2 is degenerate.
""")

# Verify: for all n=2 cycles, the non-adjacent H-1 pairs ARE adjacent
# in the cyclic sense (d=1 or d=CL-1) or not?
print("\n" + "=" * 70)
print("n=2 non-adjacent H-1 pairs: distances")
print("=" * 70)

for word, configs in all_cycles[:60]:
    for j in range(CL):
        for k in range(j+1, CL):
            if hamming_distance(configs[j], configs[k]) == 1:
                d = k - j
                anti_d = CL - d
                if d > 1 and anti_d > 1:
                    p = [i for i in range(n) if configs[j][i] != configs[k][i]][0]
                    # Show arc fire counts for BOTH arcs
                    arc1_fc = [0]*n
                    for t in range(d):
                        arc1_fc[word[(j+t)%CL]] += 1
                    arc2_fc = [0]*n
                    for t in range(anti_d):
                        arc2_fc[word[(k+t)%CL]] += 1

                    l2_arc1 = all(arc1_fc[q] in [0, ms[q]] for q in range(n) if q != p)
                    l2_arc2 = all(arc2_fc[q] in [0, ms[q]] for q in range(n) if q != p)

                    print(f"  word={word}, d={d}, anti_d={anti_d}, p={p}")
                    print(f"    arc1 fc={arc1_fc} L2={l2_arc1}, arc2 fc={arc2_fc} L2={l2_arc2}")
                    break
        else:
            continue
        break
