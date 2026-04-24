#!/usr/bin/env python3
"""
RA12 Part 4: WHY H-1 uniqueness holds + proof sketch

For good cycles where each proc p fires exactly m_p times:
  Prove that non-adjacent configs cannot be Hamming-1 apart.

Argument: If g_j and g_k differ only at position p, then g_j[p] != g_k[p]
but g_j[i] = g_k[i] for all i != p. Processor p fires m_p times in the
cycle, visiting m_p distinct values (by distinctness of cycle configs:
if p visited the same value twice with the same context, that would mean
two identical configs). Since all m_p values at position p appear in
exactly the configs where p fires, and each firing changes p by one step...

Actually, the argument is simpler:

CLAIM: In any good cycle, H-1 pairs are exactly the adjacent pairs.

PROOF:
Forward direction: Adjacent pairs g_k, g_{k+1} differ at exactly
position moverAt(k) (one proc fires, changing one position).
So adjacent pairs are always H-1. (CL such pairs.)

Backward direction: Suppose g_j and g_k are H-1 at position p,
with j < k. We need j = k-1 or (j=0, k=CL-1).

The cycle visits CL distinct configs. Processor p takes values
g_0[p], g_1[p], ..., g_{CL-1}[p]. Between consecutive configs,
p changes iff it's the mover. So the value sequence at position p
changes only at the m_p mover steps for p.

But the values at ALL OTHER positions are the same for g_j and g_k.
That means: between step j and step k, every move at a position q != p
must be "undone" (the net change at q is zero). And the only change
at p is g_j[p] -> g_k[p].

The number of H-1 pairs at position p: exactly the pairs where only
position p changes. Since p takes m_p distinct values in the cycle
(it fires m_p times, returning to its starting value), the H-1 pairs
at position p correspond to pairs of configs where p has adjacent
values in its firing sequence.

Wait, I need to verify this more carefully by checking whether the
H-1 count at each position equals exactly m_p.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import verify_system, privileged_set, apply_move
from collections import defaultdict


def build_cup2(n):
    ms = [2] + [3] * (n - 2) + [2]
    T_bot = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
    T_low = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
    T_mid = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,(2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):0,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2}
    T_high = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,(2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
    T_top = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}
    def get_table(pos):
        if pos == 0: return T_bot
        if pos == 1: return T_low
        if pos == n-2: return T_high
        if pos == n-1: return T_top
        return T_mid
    fs = []
    for p in range(n):
        tbl = get_table(p)
        def make_f(t): return lambda L,S,R: t[(L,S,R)]
        fs.append(make_f(tbl))
    return ms, fs


def build_sol3(n):
    ms = [3] * n
    def f_bottom(L, S, R):
        if (S + 1) % 3 == R: return (S - 1) % 3
        return S
    def f_top(L, S, R):
        if L == R and (L + 1) % 3 != S: return (L + 1) % 3
        return S
    def f_middle(L, S, R):
        if (S + 1) % 3 == L: return L
        if (S + 1) % 3 == R: return R
        return S
    fs = [f_bottom] + [f_middle] * (n - 2) + [f_top]
    return ms, fs


def h1_proof_analysis(ms, fs, label):
    """Analyze the proof of H-1 uniqueness."""
    n = len(ms)
    result = verify_system(ms, fs)
    if not result['valid']:
        return

    cycle = result['cycle']
    CL = len(cycle)

    # Extract movers
    movers = []
    for idx in range(CL):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % CL]
        for p in range(n):
            if c[p] != c_next[p]:
                movers.append(p)
                break

    # For each position p, extract the "context sequence" at non-p positions
    # when p fires
    print(f"\n{'='*60}")
    print(f"{label}: H-1 proof analysis")
    print(f"  Cycle length: {CL}")

    # For each H-1 pair (g_j, g_k) with j,k not adjacent:
    # they agree at all positions except p.
    # This means: the "context" (all positions except p) is the same.
    # How many distinct contexts appear at each position p?

    for p in range(n):
        # Extract context (config without position p) for each cycle config
        contexts = {}  # context -> list of step indices
        for idx in range(CL):
            ctx = tuple(cycle[idx][i] for i in range(n) if i != p)
            if ctx not in contexts:
                contexts[ctx] = []
            contexts[ctx].append(idx)

        # H-1 pairs at position p = pairs in the same context bucket with different p-values
        h1_at_p = 0
        for ctx, indices in contexts.items():
            vals = [cycle[idx][p] for idx in indices]
            if len(set(vals)) < len(vals):
                # Duplicate values at same context — impossible in a cycle of distinct configs!
                pass
            # Number of H-1 pairs in this bucket = C(len(indices), 2) if all distinct vals
            # But we want: how many of these are ADJACENT in the cycle?
            for i in range(len(indices)):
                for j in range(i + 1, len(indices)):
                    h1_at_p += 1

        fire_count = sum(1 for m in movers if m == p)
        adj_h1_at_p = fire_count  # each firing creates one adjacent H-1 pair

        # The actual total H-1 pairs at this position
        actual_h1 = 0
        for j in range(CL):
            for k in range(j + 1, CL):
                if sum(1 for i in range(n) if cycle[j][i] != cycle[k][i]) == 1:
                    diff_pos = [i for i in range(n) if cycle[j][i] != cycle[k][i]][0]
                    if diff_pos == p:
                        actual_h1 += 1

        # Context buckets with >1 entry (potential H-1 pairs)
        multi_buckets = {ctx: indices for ctx, indices in contexts.items() if len(indices) > 1}

        if p < 3 or h1_at_p != adj_h1_at_p:
            print(f"\n  Position {p} (m_p={ms[p]}):")
            print(f"    Fires: {fire_count} times")
            print(f"    Distinct contexts: {len(contexts)}")
            print(f"    Context buckets with >1 config: {len(multi_buckets)}")
            print(f"    Potential H-1 pairs (same context): {h1_at_p}")
            print(f"    Actual H-1 pairs: {actual_h1}")
            print(f"    Adjacent H-1 pairs: {adj_h1_at_p}")

            if multi_buckets:
                for ctx, indices in sorted(multi_buckets.items())[:3]:
                    vals = [cycle[idx][p] for idx in indices]
                    adj_pairs = []
                    non_adj = []
                    for i in range(len(indices)):
                        for j in range(i + 1, len(indices)):
                            a, b = indices[i], indices[j]
                            is_adj = (b == a + 1) or (a == 0 and b == CL - 1)
                            if is_adj:
                                adj_pairs.append((a, b))
                            else:
                                non_adj.append((a, b))
                    print(f"      Context {ctx}: steps {indices}, vals {vals}")
                    if non_adj:
                        print(f"        NON-ADJACENT: {non_adj}")


# Test with small systems
h1_proof_analysis(*build_cup2(5), "CUP-2 n=5")
h1_proof_analysis(*build_sol3(5), "Sol3 n=5")


# ── The actual proof ──

print("\n" + "=" * 70)
print("PROOF OF H-1 UNIQUENESS")
print("=" * 70)
print("""
THEOREM: In any good cycle of a self-stabilizing token ring,
if g_j and g_k are at Hamming distance 1, then j = k +/- 1 (mod CL).

PROOF:
Let gc = (g_0, g_1, ..., g_{CL-1}) be a good cycle.

Step 1: Adjacent pairs are always H-1.
  g_{k+1} = move(sys, g_k, moverAt(k)). Only position moverAt(k) changes.
  So Hamming(g_k, g_{k+1}) = 1. ✓

Step 2: Show no non-adjacent pair can be H-1.
  Suppose g_j and g_k differ only at position p, with gap > 1.

  Define the "context at position p" of config c as:
    ctx_p(c) = (c[0], ..., c[p-1], c[p+1], ..., c[n-1])

  Since g_j and g_k agree at all positions except p:
    ctx_p(g_j) = ctx_p(g_k)

  Now consider the sequence of configs from g_j to g_k in the cycle:
    g_j, g_{j+1}, ..., g_k

  At each step, one position changes (the mover). The net change
  across all positions from g_j to g_k is: zero at every position
  except p, where it's g_k[p] - g_j[p].

  KEY: For this to happen, every firing at position q != p between
  steps j and k must be "undone" by another firing at q.

  But does this lead to a contradiction? Not necessarily by itself.
  The cycle CAN have a segment where non-p positions cancel out.

  HOWEVER: Consider the step BEFORE g_j in the cycle (step j-1).
  moverAt(j-1) fires, producing g_j. If moverAt(j-1) = p, then
  g_{j-1} and g_j differ at p → g_{j-1} also agrees with g_k at
  all positions except p → g_{j-1} is H-1 from g_k at p.
  So now we have THREE configs (g_{j-1}, g_j, g_k) sharing the
  same context at p, with three potentially different p-values.

  If moverAt(j-1) != p, then g_{j-1} and g_j agree at p but differ
  at some q != p. So ctx_p(g_{j-1}) != ctx_p(g_j) = ctx_p(g_k).

  This doesn't immediately give a contradiction. The proof needs
  a different approach...

ALTERNATIVE PROOF APPROACH:

  All CL configs are distinct. At position p, each config has a value
  in {0, ..., m_p - 1}. By pigeonhole, at most m_p configs can share
  the same context at p (since values are distinct within each context
  bucket, and there are m_p possible values).

  Computationally verified: for CUP-2 and Sol3 at n=5,7,9, the number
  of H-1 pairs at each position p equals EXACTLY m_p, and they are
  ALL adjacent pairs. The number of same-context pairs (potential H-1)
  also equals m_p for well-structured cycles.

  But this is an OBSERVATION, not a proof. The question is whether
  it can fail for some exotic good cycle.

EXPERIMENTAL CONCLUSION:
  H-1 uniqueness holds for ALL tested systems (Sol3, CUP-2, Sol1,
  CLB bounce) at n=5,7,9. Total H-1 pairs always equals CL,
  and they are always adjacent.

  But we do NOT have a general proof. It may depend on cycle structure.
  For the Lean formalization, either:
  (a) Prove it for the specific CUP-2 cycle structure, or
  (b) Bypass it entirely (see below).

BYPASSING H-1 UNIQUENESS:
  forcedSucc_nonGood states: if c is non-good and p is privileged in c,
  then move(sys, c, p) is not good.

  THIS IS FALSE. Multi-priv non-good configs CAN have a privileged proc
  whose firing lands in the good set. (Verified: 99 violations for Sol3 n=5,
  90 for CUP-2 n=5, 297 for CUP-2 n=7, 676 for CUP-2 n=9.)

  All violations are multi-priv (≥2 privileged procs).
  There are ZERO single-priv violations (using the full good set
  including tails).

  The Lean proof should NOT use forcedSucc_nonGood. Instead, use
  convergence directly: the non-good transition graph is a DAG.
""")
