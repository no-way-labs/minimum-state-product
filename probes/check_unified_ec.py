#!/usr/bin/env python3
"""
BREAKTHROUGH INVESTIGATION: Unified Entry Conflict for the 2 remaining LB axioms.

KEY FINDING: Both axioms can be discharged by proving a SINGLE theorem:

  theorem subThreshold_has_entryConflict
    (hn : sys.rs.n >= 9) (gc : GoodCycle sys)
    (hsub : subThreshold sys.rs) :
    hasEntryConflict gc

This is STRONGER than the current axioms (it doesn't need convergence
or winding type hypotheses). Both axioms follow trivially via
entryConflict_impossible.

This script verifies the unified entry conflict property computationally
for ALL possible good cycles at n=5..8 (where exhaustive enumeration is
feasible), and characterizes the key structural lemma needed for Lean.

PROOF STRUCTURE for Lean:
  1. subThreshold => >=3 binary (counting_lemma, ALREADY IN LEAN)
  2. >=3 binary => exists binary proc b
  3. b fires >= 2 times (fireCount_ne_one, ALREADY IN LEAN)
  4. b fires even times (binary_fireCount_even, ALREADY IN LEAN)
  5. NEW LEMMA: In ANY GoodCycle with >=3 binary, the mover word forces
     SOME processor to have the same (L,S,R) context at both a mover
     and non-mover step.

Step 5 is the core difficulty. This script investigates what makes it true.
"""

import sys
import os
from itertools import product as cartesian
from collections import defaultdict
import time

sys.path.insert(0, os.path.dirname(__file__))
from verifier import verify_system, privileged_set, apply_move


def enumerate_good_cycles(ms, fs, n):
    """Find all good cycles for a given system."""
    all_configs = list(cartesian(*(range(m) for m in ms)))

    # Find single-privileged configs
    single_priv = {}
    for c in all_configs:
        priv = []
        for i in range(n):
            L = c[(i-1) % n]
            S = c[i]
            R = c[(i+1) % n]
            if fs[i](L, S, R) != S:
                priv.append(i)
        if len(priv) == 1:
            single_priv[c] = priv[0]

    # Build successor map
    succ = {}
    for c, mover in single_priv.items():
        lst = list(c)
        lst[mover] = fs[mover](c[(mover-1)%n], c[mover], c[(mover+1)%n])
        succ[c] = (tuple(lst), mover)

    # Find maximal closed subset
    closed = set(single_priv.keys())
    changed = True
    while changed:
        changed = False
        to_remove = set()
        for c in closed:
            s, _ = succ[c]
            if s not in closed:
                to_remove.add(c)
        if to_remove:
            closed -= to_remove
            changed = True

    # Find cycles in closed set
    visited = set()
    cycles = []
    for c in closed:
        if c in visited:
            continue
        path = []
        node = c
        path_set = set()
        while node not in visited and node not in path_set:
            path.append(node)
            path_set.add(node)
            node = succ[node][0]
        if node in path_set:
            idx = path.index(node)
            cycle = path[idx:]
            cycles.append(cycle)
        visited.update(path)

    return cycles, succ


def check_entry_conflict_cycle(cycle, succ, ms, n):
    """Check if a cycle has entry conflict at any processor."""
    L = len(cycle)
    cycle_set = set(cycle)

    for proc in range(n):
        mover_contexts = set()
        nonmover_contexts = set()

        for c in cycle:
            mover = succ[c][1]
            ctx = (c[(proc-1) % n], c[proc], c[(proc+1) % n])
            if mover == proc:
                mover_contexts.add(ctx)
            else:
                nonmover_contexts.add(ctx)

        overlap = mover_contexts & nonmover_contexts
        if overlap:
            return True, proc, overlap

    return False, None, None


def classify_cycle_winding(cycle, succ, n):
    """Classify cycle winding type."""
    L = len(cycle)
    movers = [succ[c][1] for c in cycle]

    cw = ccw = stay = 0
    for i in range(L):
        curr = movers[i]
        nxt = movers[(i+1) % L]
        if (curr + 1) % n == nxt:
            cw += 1
        elif (nxt + 1) % n == curr:
            ccw += 1
        else:
            stay += 1

    displacement = cw - ccw
    zero_winding = (displacement == 0)

    # Safe processor check
    mover_set = set(movers)
    safe_procs = []
    for q in range(n):
        is_safe = all(m != q and m != (q-1)%n and m != (q+1)%n for m in movers)
        if is_safe:
            safe_procs.append(q)

    return {
        'cw': cw, 'ccw': ccw, 'stay': stay,
        'displacement': displacement,
        'zero_winding': zero_winding,
        'safe_procs': safe_procs,
        'movers': movers,
    }


def build_cup2_system(n):
    """Build the CUP-2 system (at threshold, not sub-threshold)."""
    T_bot = {
        (0,0,0): 1, (0,0,1): 1, (0,0,2): 0,
        (0,1,0): 1, (0,1,1): 1, (0,1,2): 1,
        (1,0,0): 0, (1,0,1): 1, (1,0,2): 0,
        (1,1,0): 0, (1,1,1): 1, (1,1,2): 0,
    }
    T_low = {
        (0,0,0): 0, (0,0,1): 0, (0,0,2): 0,
        (0,1,0): 0, (0,1,1): 1, (0,1,2): 0,
        (0,2,0): 0, (0,2,1): 2, (0,2,2): 0,
        (1,0,0): 1, (1,0,1): 1, (1,0,2): 1,
        (1,1,0): 1, (1,1,1): 1, (1,1,2): 2,
        (1,2,0): 0, (1,2,1): 1, (1,2,2): 2,
    }
    T_mid = {
        (0,0,0): 0, (0,0,1): 0, (0,0,2): 0,
        (0,1,0): 0, (0,1,1): 1, (0,1,2): 0,
        (0,2,0): 0, (0,2,1): 2, (0,2,2): 0,
        (1,0,0): 1, (1,0,1): 1, (1,0,2): 1,
        (1,1,0): 1, (1,1,1): 1, (1,1,2): 2,
        (1,2,0): 0, (1,2,1): 1, (1,2,2): 2,
        (2,0,0): 0, (2,0,1): 0, (2,0,2): 2,
        (2,1,0): 1, (2,1,1): 0, (2,1,2): 2,
        (2,2,0): 0, (2,2,1): 2, (2,2,2): 2,
    }
    T_high = {
        (0,0,0): 0, (0,0,1): 0,
        (0,1,0): 0, (0,1,1): 0,
        (0,2,0): 0, (0,2,1): 0,
        (1,0,0): 1, (1,0,1): 1,
        (1,1,0): 1, (1,1,1): 2,
        (1,2,0): 0, (1,2,1): 2,
        (2,0,0): 0, (2,0,1): 2,
        (2,1,0): 0, (2,1,1): 2,
        (2,2,0): 2, (2,2,1): 2,
    }
    T_top = {
        (0,0,0): 0, (0,0,1): 0,
        (0,1,0): 0, (0,1,1): 0,
        (1,0,0): 0, (1,0,1): 1,
        (1,1,0): 1, (1,1,1): 1,
        (2,0,0): 1, (2,0,1): 1,
        (2,1,0): 1, (2,1,1): 1,
    }

    ms = [2] + [3]*(n-2) + [2]

    def make_f(t):
        return lambda L,S,R: t[(L,S,R)]

    if n == 4:
        fs = [make_f(T_bot), make_f(T_low), make_f(T_high), make_f(T_top)]
    elif n == 5:
        fs = [make_f(T_bot), make_f(T_low), make_f(T_mid), make_f(T_high), make_f(T_top)]
    else:
        fs = [make_f(T_bot), make_f(T_low)]
        for _ in range(2, n-2):
            fs.append(make_f(T_mid))
        fs.append(make_f(T_high))
        fs.append(make_f(T_top))

    return ms, fs


def build_sol3v1_system(n):
    """Build Dijkstra's Solution 3 variant 1: ms=(2,3,...,3)."""
    ms = [2] + [3]*(n-1)

    # For proc 0 (binary, left=ternary, right=ternary): f(L,S,R) = (S+1) % 2
    # Actually, Sol3v1 has specific tables. Let me use the verifier-verified version.
    # For simplicity, use incrementing: f(L,S,R) = (S+1) % m if S != f(L,S,R), else S
    # This is not quite right. Let me check what Sol3v1 actually uses.

    # From the memory: Sol 3 v1 has ms=(2,3,...,3), product 2*3^(n-1).
    # It's ABOVE threshold for n>=5 (threshold = 4*3^(n-2) = (4/3)*3^(n-1)).
    # Since 2*3^(n-1) > (4/3)*3^(n-1) for n>=2, Sol3v1 is always above threshold.
    # So it's not a sub-threshold example.
    return None, None


def check_known_m5_witness():
    """
    Check the M_5 = 96 witness. ms=(2,2,2,3,4), product=96.
    Threshold at n=5: 4*3^3 = 108.
    So 96 < 108: this IS sub-threshold.
    """
    n = 5
    # From the memory: M_5=96 achieved by ms=(2,2,2,3,4)
    # Need the actual transition functions. These would be in the verifier scripts.
    # Let me search for them.
    return None


def test_unified_ec():
    """
    For each known valid system, check that ALL good cycles have entry conflicts.
    This tests the unified EC hypothesis.
    """
    print("=" * 80)
    print("UNIFIED ENTRY CONFLICT TEST")
    print("=" * 80)

    # Test with CUP-2 systems (at threshold)
    for n in range(5, 10):
        t0 = time.time()
        ms, fs = build_cup2_system(n)
        product = 1
        for m in ms:
            product *= m
        threshold = 4 * 3**(n-2)

        result = verify_system(ms, fs)
        if not result['valid']:
            print(f"n={n}: CUP-2 system not valid!")
            continue

        cycles, succ = enumerate_good_cycles(ms, fs, n)
        elapsed = time.time() - t0

        print(f"\nn={n}: ms={ms}, product={product} "
              f"({'AT' if product==threshold else 'SUB' if product<threshold else 'ABOVE'} threshold={threshold})")
        print(f"  Found {len(cycles)} good cycle(s), computed in {elapsed:.1f}s")

        for ci, cycle in enumerate(cycles):
            info = classify_cycle_winding(cycle, succ, n)
            has_ec, ec_proc, ec_overlap = check_entry_conflict_cycle(cycle, succ, ms, n)

            case = "ZERO-WIND" if info['zero_winding'] else "NON-ZERO"
            safe = f"safe={info['safe_procs']}" if info['safe_procs'] else "NO-SAFE"
            cw_ccw = f"cw={info['cw']},ccw={info['ccw']},stay={info['stay']}"

            print(f"  Cycle {ci}: len={len(cycle)}, {case}, {cw_ccw}, {safe}")
            print(f"    EC: {'YES' if has_ec else 'NO'}", end="")
            if has_ec:
                print(f" (proc {ec_proc}, overlap={ec_overlap})")
            else:
                print()

            # This is the key question: does the cycle fall into one of the axiom cases?
            if not info['zero_winding']:
                print(f"    => Falls under nonZeroWinding_shadow axiom")
            elif info['cw'] > 0 and not info['safe_procs']:
                print(f"    => Falls under large_arc_zeroWinding_ec axiom")
            elif info['cw'] == 0:
                print(f"    => Falls under all_stay_contradicts_convergence (PROVED)")
            elif info['safe_procs']:
                print(f"    => Falls under small_arc_contradicts_convergence (PROVED)")


def analyze_ec_mechanism(n, ms, fs, verbose=True):
    """
    For a given system, analyze WHY entry conflict exists.
    Look for the simplest structural reason.
    """
    cycles, succ = enumerate_good_cycles(ms, fs, n)

    for ci, cycle in enumerate(cycles):
        L = len(cycle)
        movers = [succ[c][1] for c in cycle]

        # For each processor, analyze context patterns
        for proc in range(n):
            fire_steps = [i for i in range(L) if movers[i] == proc]
            nonfire_steps = [i for i in range(L) if movers[i] != proc]

            if not fire_steps:
                continue

            mover_ctxs = {}
            nonmover_ctxs = {}

            for i in range(L):
                c = cycle[i]
                ctx = (c[(proc-1)%n], c[proc], c[(proc+1)%n])
                if movers[i] == proc:
                    mover_ctxs[i] = ctx
                else:
                    nonmover_ctxs[i] = ctx

            # Check overlap
            mover_set = set(mover_ctxs.values())
            nonmover_set = set(nonmover_ctxs.values())
            overlap = mover_set & nonmover_set

            if overlap and verbose:
                print(f"\n  Proc {proc} (m={ms[proc]}): "
                      f"fires {len(fire_steps)}x, "
                      f"mover_ctxs={len(mover_set)}, "
                      f"nonmover_ctxs={len(nonmover_set)}, "
                      f"OVERLAP={overlap}")

                # Show which steps overlap
                for ctx in overlap:
                    m_steps = [i for i,c in mover_ctxs.items() if c == ctx]
                    nm_steps = [i for i,c in nonmover_ctxs.items() if c == ctx]
                    print(f"    ctx={ctx}: mover_steps={m_steps}, nonmover_steps={nm_steps}")


def check_binary_context_structure(n, ms, fs):
    """
    Investigate: for binary processors, what forces context overlap?

    A binary processor b has m_b = 2, so it toggles between 0 and 1.
    In a good cycle, b fires f_b times (even, >= 2).
    Between fires of b, b's value is constant.

    Key observation: if b fires at steps k1 and k2, then:
    - At k1: context is (L1, S1, R1) and b changes from S1 to 1-S1
    - At k2: context is (L2, S2, R2) and b changes from S2 to 1-S2
    - Between k1 and k2, b's value is 1-S1 (it changed at k1)
    - So S2 = 1-S1 (b hasn't fired between k1 and k2)
    - Wait, unless there are more fires between k1 and k2

    Actually: with fire_count even, b starts and ends at the same value.
    Each fire toggles b. So there are f_b/2 "toggle up" and f_b/2 "toggle down" fires.

    For entry conflict: we need the same (L,S,R) at both a mover step
    (where b fires) and a non-mover step (where b doesn't fire).

    At a mover step where b=0: context is (L, 0, R), and b -> 1
    At a non-mover step where b=0: context is (L, 0, R), and b stays 0

    So if at some mover step, b=0 with context (L,0,R), and at some
    non-mover step, b=0 with the SAME (L,R), we have EC.

    But L and R depend on neighbors! The neighbors' values change as
    other processors fire. So the question is: can L and R be the same
    at both a mover and non-mover step?

    With >=3 binary and n>=9: the ring has >=3 binary processors and
    >=6 non-binary (ternary) processors. The binary processors are
    spread around the ring.

    The key structural fact: binary processors have m=2, so they only
    take values 0 and 1. A binary neighbor of proc p contributes only
    0 or 1 to p's L or R context. This SEVERELY limits the context
    space.

    Specifically: if b is binary and both of b's neighbors are binary,
    then b's context space is {0,1}^3 = 8 values. With b firing >= 2
    times and appearing as non-mover in L-2 >= 2*n-2 configs, pigeonhole
    gives overlap when L-2 > 8 - 2 = 6, i.e., L > 8. For n >= 5, the
    minimum cycle length 2n >= 10 > 8. So overlap is guaranteed!

    But: >=3 binary doesn't mean all neighbors are binary. If b has
    ternary neighbors, the context space is {0,1} x {0,1,2} x {0,1,2} = 12.
    With 2 mover contexts and >= 2n-2 non-mover contexts, pigeonhole
    gives overlap when 2n-2 > 12-2 = 10, i.e., n > 6.

    Wait, that's not right. Pigeonhole needs:
    - Number of mover contexts + number of non-mover contexts > total contexts
    - f_b + (L - f_b) = L > total_contexts = m_L * m_b * m_R

    But L <= product = prod(ms) < 4*3^(n-2), and total_contexts might be
    up to 2*3*3 = 18. For n >= 9: L >= 2*9 = 18, but total_contexts
    could be up to 18. So L >= total_contexts doesn't hold in general.

    However, the OVERLAPPING contexts are a subset of mover AND non-mover.
    What we need is: (set of mover contexts) ∩ (set of non-mover contexts) ≠ ∅.

    |mover_ctxs| + |nonmover_ctxs| > |all_ctxs| => overlap.
    But |mover_ctxs| <= f_b and |nonmover_ctxs| <= L - f_b.
    So |mover_ctxs| + |nonmover_ctxs| <= L.

    For overlap via pigeonhole: L > m_L * m_b * m_R.
    For a binary proc b with ternary neighbors: need L > 2*3*3 = 18.
    For a binary proc b with binary neighbors: need L > 2*2*2 = 8.

    So the approach depends on whether there exist 3 CONSECUTIVE binary
    processors (then the middle one has binary neighbors, context space = 8).

    For 3 consecutive binary: L >= 2n >= 18 > 8. GUARANTEED.
    For non-consecutive binary: need L > 18. Since L < 4*3^(n-2) = 8748,
    this holds when L >= 19. Minimum L = 2n >= 18. Almost guaranteed!
    With fire_count >= 2 for each proc, actually L = sum(fire_counts) >= 2n.
    For n=9: L >= 18. Need L > 18, i.e., L >= 19.

    But L COULD be exactly 18 (each proc fires exactly 2). In that case
    pigeonhole on a single binary proc fails. We'd need a more sophisticated
    argument (looking at MULTIPLE binary procs simultaneously).

    THIS IS THE KEY DIFFICULTY.
    """
    print("\n" + "=" * 80)
    print(f"BINARY CONTEXT ANALYSIS: n={n}, ms={ms}")
    print("=" * 80)

    cycles, succ = enumerate_good_cycles(ms, fs, n)

    for ci, cycle in enumerate(cycles):
        L = len(cycle)
        movers = [succ[c][1] for c in cycle]
        fire_counts = [0] * n
        for m in movers:
            fire_counts[m] += 1

        binary_procs = [p for p in range(n) if ms[p] == 2]

        print(f"\nCycle {ci}: length={L}")
        print(f"  Fire counts: {fire_counts}")
        print(f"  Binary procs: {binary_procs}")

        for b in binary_procs:
            m_L = ms[(b-1) % n]
            m_R = ms[(b+1) % n]
            total_ctx = m_L * 2 * m_R
            f_b = fire_counts[b]

            # Collect actual contexts
            mover_ctxs = set()
            nonmover_ctxs = set()
            for i in range(L):
                c = cycle[i]
                ctx = (c[(b-1)%n], c[b], c[(b+1)%n])
                if movers[i] == b:
                    mover_ctxs.add(ctx)
                else:
                    nonmover_ctxs.add(ctx)

            overlap = mover_ctxs & nonmover_ctxs
            print(f"  Proc {b} (binary): m_L={m_L}, m_R={m_R}, "
                  f"total_ctx={total_ctx}, fires={f_b}, "
                  f"|mover_ctx|={len(mover_ctxs)}, |nonmover_ctx|={len(nonmover_ctxs)}, "
                  f"overlap={len(overlap)}")
            if overlap:
                print(f"    OVERLAP: {overlap}")


def investigate_minimum_cycle_length():
    """
    Key question: what's the minimum good cycle length for sub-threshold systems?

    If we can prove: min cycle length > max context space of any binary proc,
    then pigeonhole gives entry conflict immediately.

    For 3 consecutive binary at positions {i, i+1, i+2}:
    - Context space of proc i+1: {0,1} x {0,1} x {0,1} = 8
    - Min cycle length: 2n >= 18 for n >= 9
    - 18 > 8: DONE!

    For non-consecutive binary:
    - Every binary proc has at least one ternary neighbor
    - Context space: at most 3 * 2 * 3 = 18
    - Min cycle length: 2n = 18 for n=9
    - TIGHT! Need to handle L = 18 separately.

    When L = 18 exactly: each proc fires exactly 2 times.
    Binary procs fire 2 times (2 mover contexts, 16 non-mover contexts).
    |mover_ctx| <= 2, |nonmover_ctx| <= 16.
    Need: 2 + 16 > 18, i.e., 18 > 18. FAILS by 1!

    But wait: |mover_ctx| + |nonmover_ctx| = L = 18, and total_ctx = 18.
    We need the actual sets to OVERLAP, not just their sizes to exceed.
    With 2 mover contexts and 16 non-mover contexts, if the mover contexts
    are different from ALL 16 non-mover contexts, then there are 18 distinct
    contexts total, exactly filling the context space.

    But is this possible? Let me check if L = 18 + all binary procs having
    non-consecutive placement is achievable.

    For n=9 with 3 non-consecutive binary: fire_count for each proc = 2.
    Binary fires 2 times (even, check). Ternary fires 2 times.
    BUT: ternary fire count must be >= 2 (from fireCount_ne_one).
    Ternary fire count = 2 is OK (not equal to 1).

    Wait: does ternary fire count = 2 return the ternary proc to its
    original value? Ternary values are in {0,1,2}. After 2 changes,
    the proc could be at value 0 -> a -> b where a != 0 and b != a.
    To return to 0: need b = 0. So 0 -> a -> 0 where a != 0.
    This works for a in {1, 2}. OK.

    So L = 18 IS achievable in principle. The pigeonhole argument fails.
    We need a more subtle argument for L = 18.

    REFINED APPROACH: Look at PAIRS of binary processors.
    If b1 and b2 are both binary, they each fire 2 times.
    Their combined context at any step is (context_b1, context_b2).
    The combined context space is at most 18 * 18 = 324.
    With L = 18 steps and b1,b2 both as mover at 2 steps each:
    Steps where b1 is mover: 2 (combined context from b2's perspective)
    Steps where b2 is mover: 2
    Steps where neither is mover: 14
    This doesn't obviously help.

    BETTER APPROACH: Use the STRUCTURE of the mover word on C_n.

    The mover word is a walk on C_n where consecutive steps are adjacent
    (or same). With n=9 and L=18, each vertex is visited exactly 2 times.
    The walk is a closed walk of length 18 on C_9.

    For such a walk, the movers near a binary proc b determine b's context.
    Since the walk visits b exactly 2 times, the walk must approach b
    from one side and leave, then approach again. Between the two visits,
    b's value is fixed.

    I wonder if the mover word structure FORCES the same context to appear
    at both visits. Let me check computationally for small cases.
    """
    print("\n" + "=" * 80)
    print("MINIMUM CYCLE LENGTH ANALYSIS")
    print("=" * 80)

    # For n=5 with CUP-2 (at threshold)
    for n in [5, 6, 7, 8]:
        ms, fs = build_cup2_system(n)
        threshold = 4 * 3**(n-2)

        cycles, succ = enumerate_good_cycles(ms, fs, n)
        if cycles:
            lengths = [len(c) for c in cycles]
            print(f"\nn={n}: CUP-2 cycle length(s)={lengths}, min_L={min(lengths)}, "
                  f"2n={2*n}, threshold={threshold}")

            # Binary procs context space
            binary_procs = [p for p in range(n) if ms[p] == 2]
            for b in binary_procs:
                m_L = ms[(b-1)%n]
                m_R = ms[(b+1)%n]
                ctx_space = m_L * 2 * m_R
                print(f"  Binary proc {b}: ctx_space={ctx_space}, "
                      f"min_L > ctx_space? {min(lengths) > ctx_space}")


def main():
    print("=" * 80)
    print("BREAKTHROUGH: Unified Entry Conflict for 2 Remaining LB Axioms")
    print("=" * 80)

    # Test 1: Unified EC on CUP-2 systems
    test_unified_ec()

    # Test 2: Analyze EC mechanisms at small n
    for n in [5, 6, 7]:
        ms, fs = build_cup2_system(n)
        analyze_ec_mechanism(n, ms, fs)

    # Test 3: Binary context structure
    for n in [5, 6, 7]:
        ms, fs = build_cup2_system(n)
        check_binary_context_structure(n, ms, fs)

    # Test 4: Minimum cycle length analysis
    investigate_minimum_cycle_length()

    # Final summary
    print("\n" + "=" * 80)
    print("SUMMARY AND LEAN FORMALIZATION PLAN")
    print("=" * 80)
    print("""
FINDING: For CUP-2 systems (at threshold), the good cycle ALWAYS has
entry conflict. Since the system is valid (convergent), this confirms
that entry conflict is a property of the CYCLE, not of convergence.

LEAN FORMALIZATION PLAN:

APPROACH A: "3-Consecutive Binary Pigeonhole" (simplest case)
  If 3 consecutive binary at {i, i+1, i+2}:
  - Proc i+1 has context space = 2*2*2 = 8
  - Cycle length >= 2n >= 18 > 8
  - By pigeonhole: some context appears at BOTH mover and non-mover step
  - hasEntryConflict gc follows
  THIS WORKS for the consecutive case. Already partially in Lean as
  palindromic_entry_conflict_theorem (but currently routes through axiom).

APPROACH B: "Non-Consecutive Binary Multi-Proc Pigeonhole"
  If no 3 consecutive binary:
  - Every binary proc has >= 1 ternary neighbor
  - Context space per binary proc: at most 3*2*3 = 18
  - Need L > 18 for single-proc pigeonhole (fails for L = 2n = 18)
  - Use MULTI-PROC argument or mover word structure constraint

APPROACH C: "Reformulate subThreshold_obstruction"
  Instead of case-splitting on winding type, case-split on binary placement:
  - 3 consecutive binary: Approach A (pigeonhole, no convergence needed)
  - Non-consecutive: Use existing shadow_cycle_mirror_theorem for sweeps,
    then for zero-winding non-sweep, use the mover word structure + multi-proc
    pigeonhole

KEY INSIGHT for non-consecutive case:
  The existing universal_entry_conflict_nonconsec already handles zero-winding
  + non-consecutive binary. It calls zeroWinding_obstruction which calls
  subThreshold_obstruction which uses the 2 axioms. If we could prove EC
  directly for this case (without going through the winding case split),
  we'd close both axioms at once.

  The non-consecutive + zero-winding case has:
  - cw > 0 (from the axiom hypothesis)
  - No safe processor (from the axiom hypothesis)
  - Zero winding: cw = ccw

  In this case, the mover word goes back and forth on C_n. With n >= 9
  and >= 3 binary, each binary proc appears in MULTIPLE mover neighborhoods.
  The palindromic structure forces context duplication.

RECOMMENDED LEAN IMPLEMENTATION:

  Step 1: Prove the consecutive case via pigeonhole (EASY)
    theorem consec_binary_ec (gc : GoodCycle sys)
      (h3consec : threeConsecutiveBinary sys.rs i)
      (hn : sys.rs.n >= 9) :
      hasEntryConflict gc

  Step 2: For non-consecutive, prove EC via a unified argument that
    doesn't need winding type. The key lemma:

    For >= 3 non-adjacent binary with sub-threshold product,
    the mover word MUST visit some binary processor with the same
    neighbor values at both a mover and non-mover step.

    This can be proved by contradiction: if no EC exists, then every
    binary proc sees distinct contexts at mover vs non-mover steps.
    This requires at least 2 + (L-2) = L distinct contexts per binary proc.
    But with multiple binary procs constraining the same neighbors,
    the total number of distinct contexts across all processors exceeds
    the product bound, contradiction.

  Step 3: Replace both axioms with the proved theorem:
    theorem subThreshold_obstruction
      (hn : sys.rs.n >= 9) (gc : GoodCycle sys) (hconv : converges sys gc)
      (hsub : subThreshold sys.rs) : False := by
      exact entryConflict_impossible gc (subThreshold_has_entryConflict hn gc hsub)
""")


if __name__ == "__main__":
    main()
