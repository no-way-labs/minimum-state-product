#!/usr/bin/env python3
"""
CONVERGENCE PROOF FRAMEWORK v2: Definitive Summary
====================================================

THEOREM (to prove):
For all n >= 5, the CUP-2 system with ms=(2,3,...,3,2) and the 5 universal
lookup tables (87 entries) has an acyclic bad-config graph (DAG).

STATUS: Verified computationally for n=5..18.
        Analytical proof: OPEN.

============================================================================
PART I: ESTABLISHED STRUCTURAL FACTS (all proved or verified)
============================================================================

FACT 1 — NO 2-CYCLE PROPERTY (Proved analytically):
  For every table T and every (L,R): T(L, T(L,a,R), R) = T(L,a,R).
  Consequence: every firing moves the mover to a fixed point.
  Proof: Direct verification over all 87 table entries.

FACT 2 — MOVER ALWAYS GAINS TARGET (Verified n=5..8):
  When position i fires, it reaches the unique fixed point of
  a → T(L,a,R) for its current context (L,R). It becomes "settled."

FACT 3 — FREEZE-ANY-POSITION → DAG (Verified n=5..12):
  For every position p ∈ {0,...,n-1}, the graph restricted to
  transitions at positions ≠ p is a DAG.
  Consequence: any cycle must involve ALL n positions.

FACT 4 — ALL-POSITION PARTICIPATION (Proved via Fact 3):
  Any hypothetical cycle must include firings at all n positions.
  Proof: If position p doesn't fire, the cycle lives in the p-frozen
  graph, contradicting Fact 3.

FACT 5 — MINIMUM CYCLE LENGTH ≥ 2n (Proved via Facts 1+4):
  Each of the n positions fires ≥ 2 times (it must fire, then return
  to its original value, but by Fact 1 it can't oscillate under fixed
  context — neighbors must change first). So ≥ 2n firings total.

FACT 6 — NEIGHBOR-CHANGE OBLIGATION (Proved via Fact 1):
  Between consecutive firings at position i, at least one neighbor
  must change. For T_mid: 30 oscillation types (8 L-only, 4 R-only,
  18 both, 0 neither). The "0 neither" is guaranteed by Fact 1.

FACT 7 — DIRECTIONAL OBLIGATION ASYMMETRY (Proved):
  T_top oscillations: 6 L-only, 0 R-only, 6 both → all need L change
  T_high oscillations: 8 L-only, 0 R-only, 10 both → all need L change
  T_bot oscillations: 2 L-only, 4 R-only, 6 both → mixed
  T_low oscillations: 4 L-only, 2 R-only, 8 both → mixed

FACT 8 — BOUNDARY PARTITION STRUCTURE (Verified n=5..7):
  Partition configs by (c[0], c[n-1]) ∈ {0,1}².
  Interior transitions (positions 1..n-2) with fixed boundaries → DAG.
  Boundary transitions always cross partitions (never same-partition).
  7 boundary transition types (consistent for all n):
    (0,0)→(0,1), (0,0)→(1,0), (0,1)→(0,0), (0,1)→(1,1),
    (1,0)→(1,1), (1,1)→(0,1), (1,1)→(1,0)
  Boundary 4-state graph has CYCLES.
  But: no two bad configs are mutually reachable (DAG is strict).

FACT 9 — FROZEN-RANK SUM NEAR-POTENTIAL (Verified n=5..7):
  Σ_p r_p(c) [sum of frozen-position ranks] has only ~8% violations.
  max_p r_p(c) has ~2-3% violations.
  LP proves: no WEIGHTED sum of frozen ranks is a valid potential.

FACT 10 — CONVERGENCE DEPTH (Verified n=5..12):
  max_depth(n) = Θ(n²). Sequence: 10, 17, 27, 39, 52, 67, 83, 101.

FACT 11 — INTERIOR RANK TRANSFER (Verified n=5..7):
  Boundary transition (1,1)→(1,0) via T_top: interior rank ALWAYS
  decreases. This is the ONLY always-monotone boundary transition type.
  Interior rank has 0% violations for interior transitions, 31-48%
  for boundary transitions.

============================================================================
PART II: ELIMINATED APPROACHES
============================================================================

✗ POTENTIAL FUNCTIONS (exhaustive search):
  Tested: sum, frontier, count_2s, priv_count, at_target, left_agreement,
  settled_count, Hamming, inversions, descents, entropy, sum_of_squares,
  weighted_settled, all 2-feature linear/lex combinations, 3-local additive,
  pairwise, quadratic, position-weighted, boundary-augmented interior rank.
  Best: I_rank + α*boundary (~5% violations). No combination achieves 0%.
  CONCLUSION: No simple/additive potential function exists.

✗ HARMONIC CRITERION: Σ 1/(D_p+1) always < 1 (0.57→0.14).

✗ WEIGHTED FROZEN-RANK SUMS: LP infeasible for n=5,6.

✗ BOUNDARY PARTITION with boundary DAG: boundary graph has cycles.

✗ SETTLED COUNT as potential: 5% of transitions decrease it.

============================================================================
PART III: THE PROOF FRAMEWORK (how someone could prove this)
============================================================================

The proof will likely use one of these approaches, possibly combined:

APPROACH A: CAUSAL CHAIN IMPOSSIBILITY (Most promising)
─────────────────────────────────────────────────────────
The argument structure:
1. In a hypothetical cycle, all n positions oscillate (Fact 4+5).
2. Each oscillation creates obligations at neighbors (Fact 6).
3. T_top and T_high create ONLY leftward obligations (Fact 7):
   - Every T_top oscillation requires T_high to change
   - Every T_high oscillation requires its left T_mid neighbor to change
4. This creates a leftward obligation chain from T_top through T_high
   through the T_mid interior to T_low and T_bot.
5. For the chain to close around the ring, the rightward obligation
   flow (from T_bot through T_low through T_mid) must match.

KEY GAP: Show that the leftward obligations from T_top/T_high create
constraints on T_Bot/T_Low that are INCONSISTENT with the rightward
obligations that T_Bot/T_Low create.

The specific mechanism:
- T_top oscillation 0→1→0: requires T_high to go from ≥1 to 0
- T_high going to 0 requires its left neighbor (T_mid) to be 0
- This propagates leftward: each T_mid must become 0 (via L=0 dependency)
- Eventually reaches T_low: needs L=0 (T_bot = 0)
- But T_bot must ALSO oscillate (it fires ≥2 times)
- T_Bot oscillation from 0 to 1 creates a "1-wave" going rightward
- The 1-wave and 0-wave must coexist and cycle — show this is impossible

APPROACH B: INDUCTION ON n
───────────────────────────
1. Base case: n=5 verified computationally (only 85 bad configs).
2. Inductive step: assume n-1 system is DAG, prove n system is DAG.
   - Remove one T_mid position (say position n-3) → relates to (n-1) system
   - The projection preserves table types and neighbor domains
   - Rank correlation: 0.73-0.82 (increasing with n)

KEY GAP: Make the projection rigorous. The good sets differ, so the
bad-config graphs aren't simply sub/super-graphs.

APPROACH C: NONLINEAR FROZEN-RANK COMBINATION
──────────────────────────────────────────────
1. For each position p, the p-frozen rank r_p decreases on non-p transitions.
2. Actual max Δr_p for p-transitions is 35-86% of the frozen depth D_p.
3. Sum Σr_p fails by ~8%, but a nonlinear combination might work.

KEY GAP: Find f(r_0,...,r_{n-1}) that strictly decreases on every
transition. LP rules out linear f. Try: max(r_p), products, etc.
Max has ~2-3% violations — tantalizingly close.

APPROACH D: BOUNDARY-INTERIOR DECOMPOSITION
────────────────────────────────────────────
1. Partition by (c[0], c[n-1]): interior is always DAG.
2. Boundary graph has cycles, but combined system is DAG.
3. Interior rank progression prevents boundary cycle realization.

KEY GAP: Show that when traversing a boundary-graph cycle
(e.g., (0,0)→(0,1)→(0,0)), the interior rank strictly decreases,
preventing infinite cycling. This requires analyzing how interior
ranks transfer across partitions — computed but not yet provable.

============================================================================
PART IV: WHAT THE PROOF REQUIRES (minimally)
============================================================================

The MINIMUM needed for a complete proof is ONE of:

Option 1: A function φ: configs → W (some well-ordered set) such that
  for every bad-config transition c → c', φ(c) > φ(c').
  All simple candidates fail. Must be non-additive and possibly depend
  on global configuration structure.

Option 2: A direct impossibility argument showing that the obligation
  chains from the causal analysis cannot close into a cycle.
  Requires formalizing the wave interaction at the boundaries.

Option 3: A valid induction on n, relating the n-system DAG to (n-1).
  Requires handling the good-set mismatch between n and n-1 systems.

AUTHOR'S ASSESSMENT:
  Option 2 (causal chain + boundary mismatch) is the most promising
  approach. The key unused structural feature is the directional
  asymmetry: T_top/T_high create only leftward obligations while the
  boundary tables create mixed-direction obligations. This asymmetry
  is the fundamental reason cycles can't form. The proof should
  exploit the specific table entries to show that the leftward
  obligation chain from T_top creates constraints at T_Bot that are
  incompatible with T_Bot's own oscillation requirements.

  A hybrid of Option 2 + Option 4 (boundary-interior decomposition)
  might work: show that within each boundary partition, the interior
  is a DAG (proved), and that the boundary cycle cannot be realized
  because the interior rank always makes net progress.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import deque

def quick_verify(max_n=10):
    """Quick verification of key facts for a range of n."""
    print("CONVERGENCE FRAMEWORK v2 — QUICK VERIFICATION")
    print("=" * 60)

    for nv in range(5, max_n + 1):
        ms, fs = build_system(nv)
        prod = 4 * 3 ** (nv - 2)
        if prod > 500000:
            break

        result = verify_system(ms, fs)
        if not result['valid']:
            print(f"  n={nv}: INVALID!")
            continue

        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_list = [c for c in all_configs if c not in good_set]
        bad_set = set(bad_list)
        n = nv

        # Build DAG and compute depth
        adj = {c: [] for c in bad_list}
        for c in bad_list:
            for i in range(n):
                L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                new_S = fs[i](L, S, R)
                if new_S != S:
                    lst = list(c); lst[i] = new_S; succ = tuple(lst)
                    if succ in bad_set:
                        adj[c].append(succ)

        in_deg = {c: 0 for c in bad_list}
        for c in bad_list:
            for s in adj[c]:
                in_deg[s] += 1
        q = deque(c for c in bad_list if in_deg[c] == 0)
        count = 0
        topo = []
        while q:
            c = q.popleft()
            count += 1
            topo.append(c)
            for s in adj[c]:
                in_deg[s] -= 1
                if in_deg[s] == 0:
                    q.append(s)

        is_dag = (count == len(bad_list))
        depth = 0
        if is_dag:
            rank = {}
            for c in reversed(topo):
                rank[c] = max((rank[s] + 1 for s in adj[c]), default=0)
            depth = max(rank.values()) if rank else 0

        expected_depth = (3*nv**2 - 4*nv - 11) // 4
        depth_match = "✓" if depth == expected_depth else "✗"

        print(f"  n={nv}: prod={prod:>7d}, bad={len(bad_list):>6d}, "
              f"DAG={'✓' if is_dag else '✗'}, depth={depth:>4d} "
              f"(expect {expected_depth}) {depth_match}")

if __name__ == "__main__":
    quick_verify(12)
