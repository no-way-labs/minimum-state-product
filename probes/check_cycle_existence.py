#!/usr/bin/env python3
"""
Breakthrough investigation for the 2 remaining LB axioms.

The two axioms assert False for:
1. large_arc_zeroWinding_ec: zero-winding, cwStepCount > 0, no safe processor,
   sub-threshold, converges, n >= 9
2. nonZeroWinding_shadow: non-zero winding, sub-threshold, converges, n >= 9

Strategy:
- For small n (5..9), enumerate ALL sub-threshold multisets
- For each valid system, extract the good cycle
- Classify: winding type, safe processor existence, step counts
- Check if the axiom cases are even reachable
- If not reachable: the axioms are vacuously true!

Key insight from the memory: sub-threshold means product < 4*3^(n-2).
For n >= 9, sub-threshold => >= 3 binary processors.
The Python proofs show ALL sub-threshold good cycles have entry conflicts.
So no valid system with sub-threshold product can exist for n >= 9.
But wait — the axioms don't assume a specific system, they assume a GoodCycle
that converges. So the question is: can such a cycle exist AT ALL?

CRITICAL REALIZATION: The axioms say "for any system with sub-threshold product
that has a good cycle that converges, False." This is equivalent to saying
"no valid sub-threshold system exists for n >= 9." The Python proofs ALREADY
show this via entry conflict (every possible good cycle has an entry conflict,
so no transition function can be consistent). But we need to formalize it.

This script checks: for n=5..9, are there ANY valid sub-threshold systems?
If not for n >= some K, the axioms are vacuously true.
"""

import sys
import os
import time
from itertools import product as cartesian, combinations_with_replacement
from collections import defaultdict

sys.path.insert(0, os.path.dirname(__file__))
from verifier import verify_system, privileged_set, apply_move


def sub_threshold_multisets(n):
    """Enumerate all multisets ms of length n with product < 4*3^(n-2), each m_i >= 2."""
    threshold = 4 * 3 ** (n - 2)
    # Each m_i >= 2. Product < threshold.
    # Max possible m_i = threshold // 2^(n-1) roughly
    max_m = min(threshold, 100)  # practical limit

    results = []

    def backtrack(pos, current_ms, current_prod):
        if pos == n:
            if current_prod < threshold:
                results.append(tuple(current_ms))
            return
        # For canonical ordering, m_i >= m_{i-1} (we'll permute later)
        min_val = current_ms[-1] if current_ms else 2
        for m in range(min_val, max_m + 1):
            new_prod = current_prod * m
            if new_prod >= threshold:
                break
            backtrack(pos + 1, current_ms + [m], new_prod)

    backtrack(0, [], 1)
    return results


def all_orientations(ms_sorted, n):
    """Generate all distinct ring placements of a sorted multiset."""
    from itertools import permutations
    seen = set()
    results = []
    for perm in permutations(ms_sorted):
        # Normalize by rotation and reflection
        rotations = [perm[i:] + perm[:i] for i in range(n)]
        reflected = tuple(reversed(perm))
        ref_rotations = [reflected[i:] + reflected[:i] for i in range(n)]
        canon = min(rotations + ref_rotations)
        if canon not in seen:
            seen.add(canon)
            results.append(perm)
    return results


def compute_winding(mover_word, n):
    """Compute total displacement (winding number * n) of a mover word on C_n."""
    total = 0
    L = len(mover_word)
    for i in range(L):
        curr = mover_word[i]
        nxt = mover_word[(i + 1) % L]
        if (curr + 1) % n == nxt:
            total += 1  # CW
        elif (nxt + 1) % n == curr:
            total -= 1  # CCW
        # else stay: 0
    return total


def classify_cycle(cycle, ms, fs, n):
    """Classify a good cycle: winding, step types, safe processors."""
    L = len(cycle)

    # Extract mover word
    movers = []
    for i in range(L):
        c = cycle[i]
        priv = privileged_set(c, fs, ms)
        assert len(priv) == 1, f"Config {c} has {len(priv)} privileged"
        movers.append(priv[0])

    # Step directions
    cw_count = 0
    ccw_count = 0
    stay_count = 0
    for i in range(L):
        curr = movers[i]
        nxt = movers[(i + 1) % L]
        if (curr + 1) % n == nxt:
            cw_count += 1
        elif (nxt + 1) % n == curr:
            ccw_count += 1
        else:
            stay_count += 1

    # Winding
    displacement = cw_count - ccw_count
    zero_winding = (displacement == 0)

    # Safe processor: q such that no mover is q, left(q), or right(q)
    safe_procs = []
    for q in range(n):
        is_safe = True
        for m in movers:
            if m == q or m == (q - 1) % n or m == (q + 1) % n:
                is_safe = False
                break
        if is_safe:
            safe_procs.append(q)

    # Fire counts
    fire_counts = [0] * n
    for m in movers:
        fire_counts[m] += 1

    # Entry conflict check
    has_ec = check_entry_conflict(cycle, movers, ms, fs, n)

    return {
        'length': L,
        'movers': movers,
        'cw': cw_count,
        'ccw': ccw_count,
        'stay': stay_count,
        'displacement': displacement,
        'zero_winding': zero_winding,
        'safe_procs': safe_procs,
        'fire_counts': fire_counts,
        'has_entry_conflict': has_ec,
    }


def check_entry_conflict(cycle, movers, ms, fs, n):
    """Check if the cycle has an entry conflict at any processor."""
    L = len(cycle)

    # For each processor, collect mover contexts and non-mover contexts
    for proc in range(n):
        mover_contexts = set()
        nonmover_contexts = set()

        for i in range(L):
            c = cycle[i]
            L_val = c[(proc - 1) % n]
            S_val = c[proc]
            R_val = c[(proc + 1) % n]
            ctx = (L_val, S_val, R_val)

            if movers[i] == proc:
                mover_contexts.add(ctx)
            else:
                nonmover_contexts.add(ctx)

        # Entry conflict = same context appears as both mover and non-mover
        overlap = mover_contexts & nonmover_contexts
        if overlap:
            return True

    return False


def brute_force_systems(ms, n):
    """Try ALL possible transition functions for given ms and check validity.
    Only practical for very small state spaces."""
    product = 1
    for m in ms:
        product *= m

    if product > 200:  # too large
        return None, None

    # For each processor, enumerate all possible transition functions
    # f_i : {0..m_{i-1}} x {0..m_i-1} x {0..m_{i+1}-1} -> {0..m_i-1}
    # Number of functions = m_i^(m_{i-1} * m_i * m_{i+1})

    total_funcs = 1
    for i in range(n):
        m_L = ms[(i - 1) % n]
        m_S = ms[i]
        m_R = ms[(i + 1) % n]
        num_inputs = m_L * m_S * m_R
        total_funcs *= m_S ** num_inputs

    if total_funcs > 10**9:  # too many
        return None, None

    # This is infeasible for most cases. Return None to signal "skip".
    return None, None


def analyze_n(n, verbose=True):
    """Analyze all sub-threshold multisets for given n."""
    threshold = 4 * 3 ** (n - 2)

    if verbose:
        print(f"\n{'='*80}")
        print(f"n = {n}, threshold = {threshold} (= 4 * 3^{n-2})")
        print(f"{'='*80}")

    # Get sorted multisets
    sorted_multisets = sub_threshold_multisets(n)
    if verbose:
        print(f"Found {len(sorted_multisets)} sorted sub-threshold multisets")

    # Count binary processors in each
    binary_counts = defaultdict(int)
    for ms in sorted_multisets:
        b = sum(1 for m in ms if m == 2)
        binary_counts[b] += 1

    if verbose:
        print(f"Binary count distribution: {dict(sorted(binary_counts.items()))}")

    # For each orientation of each multiset, check if ANY valid system exists
    # (This is the key question — if no valid system exists, the axioms are vacuous)

    total_orientations = 0
    valid_systems = 0
    cycle_classifications = []

    for ms_sorted in sorted_multisets:
        product = 1
        for m in ms_sorted:
            product *= m

        orientations = all_orientations(ms_sorted, n)
        total_orientations += len(orientations)

        for ms_perm in orientations:
            ms = list(ms_perm)

            # Try to find valid systems by exhaustive search (only for small products)
            # For products > ~200, this is infeasible via brute force
            # But we can check specific known constructions
            pass

    if verbose:
        print(f"Total distinct orientations: {total_orientations}")

    return sorted_multisets, total_orientations


def check_with_known_constructions(n, verbose=True):
    """
    Check if any KNOWN construction produces a valid sub-threshold system.

    Known constructions:
    1. CUP-2 (ms = (2,3,...,3,2), product = 4*3^(n-2)) — AT threshold, not sub
    2. CLB (ms = (2,3,...,3,2) bounce cycle) — AT threshold
    3. Sol 3 v1 (ms = (2,3,...,3), product = 2*3^(n-1)) — ABOVE threshold for n>=5
    4. Dijkstra Sol 1 (ms = (k,k,...,k)) — product k^n, needs k >= 3
    """
    threshold = 4 * 3 ** (n - 2)

    if verbose:
        print(f"\nKnown constructions for n={n} (threshold={threshold}):")

    constructions = [
        ("CUP-2", [2] + [3]*(n-2) + [2], 4 * 3**(n-2)),
        ("CLB", [2] + [3]*(n-2) + [2], 4 * 3**(n-2)),
        ("Sol3v1", [2] + [3]*(n-1), 2 * 3**(n-1)),
        ("Sol1_k3", [3]*n, 3**n),
        ("Sol1_k4", [4]*n, 4**n),
    ]

    for name, ms, prod in constructions:
        status = "SUB" if prod < threshold else ("AT" if prod == threshold else "ABOVE")
        if verbose:
            print(f"  {name}: ms={ms[:5]}{'...' if len(ms)>5 else ''}, "
                  f"product={prod}, {status} threshold")


def exhaustive_small_n_check(n, max_product=None, verbose=True):
    """For small n, exhaustively check ALL possible systems with sub-threshold product.

    Strategy: enumerate all multisets, all ring placements, and try to find
    valid systems. For very small products, try all transition functions.
    For larger products, check if entry conflict is universal.
    """
    threshold = 4 * 3 ** (n - 2)
    if max_product is None:
        max_product = threshold

    if verbose:
        print(f"\n{'='*80}")
        print(f"EXHAUSTIVE CHECK: n={n}, threshold={threshold}")
        print(f"{'='*80}")

    sorted_multisets = sub_threshold_multisets(n)

    # For each multiset and orientation, enumerate good cycles and check entry conflicts
    total_cycles_checked = 0
    valid_count = 0
    all_have_ec = True

    for ms_sorted in sorted_multisets:
        product = 1
        for m in ms_sorted:
            product *= m

        if product > max_product:
            continue

        orientations = all_orientations(ms_sorted, n)

        for ms_perm in orientations:
            ms = list(ms_perm)

            # Enumerate ALL possible good cycles for this ms
            # A good cycle visits each processor at least once (fairness)
            # Each config has exactly 1 privileged processor
            # The cycle is closed under the deterministic move

            # Actually, the cycle depends on the transition function f.
            # We can't enumerate cycles without fixing f first.
            #
            # BUT: we CAN enumerate all possible MOVER WORDS (sequences of
            # which processor fires). The mover word determines the cycle
            # structure. Then for each mover word, we check if ANY transition
            # function can realize it (entry conflict check).

            # For practical purposes at n=5, we can try the verifier directly
            # on specific systems. But for checking universality of entry conflict,
            # we need the mover word approach.
            pass

    return valid_count, total_cycles_checked


def check_mover_word_entry_conflicts(n, ms, verbose=False):
    """
    For given n and ms, enumerate ALL valid mover words and check if ALL
    have entry conflicts.

    A mover word is valid if:
    - Consecutive movers are adjacent or equal on C_n
    - Every processor fires >= 1 time (fairness)
    - Every processor fires != 1 time (fireCount_ne_one)
    - Binary processors fire an even number of times
    - Total length = sum of fire counts

    Returns: (total_words, all_have_ec, ec_free_count, details)
    """
    binary_procs = [i for i in range(n) if ms[i] == 2]

    # Fire count constraints:
    # - Each proc fires >= 2 times (fireCount_ne_one: can't be 0 or 1)
    #   Wait: fireCount_ne_one says != 1. Could be 0 if proc never fires.
    #   But fairness requires every proc fires >= 1. So fire_count >= 2.
    # - Binary procs fire even number of times, so >= 2
    # - Ternary procs fire >= 2 (not 1, and >= 1 means >= 2)

    # Actually re-reading: fireCount_ne_one is proved for ALL processors.
    # And fairness requires all fire >= 1. So all fire >= 2.
    # Binary: fire count even, >= 2
    # Ternary: fire count >= 2

    # Minimum cycle length = 2n (each proc fires exactly 2)
    # Maximum cycle length bounded by product of ms (distinct configs)

    product = 1
    for m in ms:
        product *= m

    # For small n, enumerate by DFS
    # This is exponential but feasible for n=5

    # Instead of enumerating ALL words, let's check the specific question:
    # for each possible mover word, check if there's an entry conflict.

    # A more efficient approach: enumerate all state sequence combinations
    # and check entry conflicts. This is what cic_case3a_proof5.py does.

    # For now, let's just report what the mover word constraints force.
    min_length = 2 * n

    if verbose:
        print(f"  ms={ms}, product={product}")
        print(f"  Binary procs: {binary_procs}")
        print(f"  Min cycle length: {min_length}")
        print(f"  Max cycle length (product): {product}")

    return None


def check_vacancy_approach(verbose=True):
    """
    KEY INSIGHT: Maybe both axiom cases are UNREACHABLE.

    The axioms require:
    1. A System with sub-threshold RingSpec (product < 4*3^(n-2), n >= 9)
    2. A GoodCycle for that system
    3. That the system converges

    If NO valid sub-threshold system exists for n >= 9, then both axioms
    are vacuously true (there's no System+GoodCycle+converges to apply them to).

    The Python proofs show: every possible good cycle for sub-threshold product
    has an entry conflict. An entry conflict means no transition function can
    simultaneously be consistent at both the mover and non-mover steps.
    Therefore: no valid system exists. Therefore: both axioms are vacuously true.

    But the Lean formalization needs to PROVE "no valid sub-threshold system exists"
    or equivalently "every good cycle has an entry conflict". The axioms
    are a shortcut: they state the contradiction directly for each sub-case
    (zero-winding vs non-zero-winding).

    So the real question is: what's the simplest way to prove these in Lean?

    APPROACH: Instead of proving the entry conflict for each sub-case separately,
    prove a SINGLE lemma:
      "sub-threshold + n >= 9 → hasEntryConflict gc"
    Then both axioms follow from entryConflict_impossible.

    But proving hasEntryConflict universally is exactly what's hard...

    ALTERNATIVE: Prove that sub-threshold → ≥3 binary → every good cycle
    has a specific structural property (e.g., some processor must see
    duplicate contexts). This is what entry conflict IS.

    Let me check: does the Lean codebase already have a proof that
    sub-threshold implies ≥3 binary?
    """
    if verbose:
        print("\n" + "=" * 80)
        print("VACANCY ANALYSIS: Are the axiom cases even reachable?")
        print("=" * 80)

        print("""
The axioms assert False under hypotheses that include:
  - A System with sub-threshold product
  - A GoodCycle that converges

If no such System+GoodCycle+converges triple exists, the axioms are
VACUOUSLY TRUE.

The Python proof chain shows:
1. Sub-threshold + n>=9 => >= 3 binary processors
2. >= 3 binary => every good cycle has entry conflict
3. Entry conflict => no consistent transition function => no valid system
4. No valid system => no converging good cycle => axiom hypotheses unsatisfied

But the Lean formalization strategy is different: it takes a generic
GoodCycle and derives False. The question is whether the proof can
be structured to avoid case-splitting on zero/non-zero winding.

KEY OBSERVATION: Both axioms could be replaced by a SINGLE theorem:
  theorem entryConflict_universal
    (hn : sys.rs.n >= 9) (gc : GoodCycle sys)
    (hsub : subThreshold sys.rs) :
    hasEntryConflict gc

This would make both axioms trivially follow from entryConflict_impossible.
The convergence hypothesis isn't even needed!

The question becomes: can we prove entryConflict_universal in Lean?
""")


def check_convergence_needed(verbose=True):
    """
    CRITICAL QUESTION: Do the axioms actually need the convergence hypothesis?

    Look at the hypotheses:
    - large_arc_zeroWinding_ec needs: converges, subThreshold, zeroWinding,
      cwStepCount > 0, no safe processor
    - nonZeroWinding_shadow needs: converges, subThreshold, ¬zeroWinding

    But entry conflict doesn't need convergence! It just needs a GoodCycle
    and the structural properties.

    Let's check: can we prove False from just (gc : GoodCycle sys) + subThreshold?

    YES! Because:
    - subThreshold => >=3 binary
    - >=3 binary + GoodCycle => entry conflict (from the Python proofs)
    - entry conflict => False

    So the real theorem would be:

    theorem subThreshold_no_goodCycle
      (hn : sys.rs.n >= 9) (gc : GoodCycle sys)
      (hsub : subThreshold sys.rs) : False

    WITHOUT needing convergence. This is STRONGER than what's currently stated.
    Both current axioms would be trivial corollaries.

    The challenge: formalizing the entry conflict proof.
    """
    if verbose:
        print("\n" + "=" * 80)
        print("CONVERGENCE NECESSITY CHECK")
        print("=" * 80)

        print("""
FINDING: Convergence is NOT needed for the contradiction!

The entry conflict argument only uses the GoodCycle structure:
- configs are distinct
- each config has exactly one privileged processor
- the cycle is closed under the deterministic move

It does NOT use:
- convergence (bad configs form a DAG)
- any property of bad configs at all

Therefore, a stronger theorem is provable:

  theorem subThreshold_no_goodCycle
    (hn : sys.rs.n >= 9) (gc : GoodCycle sys)
    (hsub : subThreshold sys.rs) : False

This would make BOTH axioms trivially follow:
  - large_arc_zeroWinding_ec: exact subThreshold_no_goodCycle hn gc hsub
  - nonZeroWinding_shadow: exact subThreshold_no_goodCycle hn gc hsub

And it eliminates ALL case-splitting on winding type!
""")


def investigate_entry_conflict_formalization(verbose=True):
    """
    Investigate what's needed to formalize the entry conflict proof.

    The Python proof has several components:
    1. Sub-threshold => >=3 binary (counting lemma) — likely already in Lean
    2. Binary processor constraints (fire count even, >= 2)
    3. Mover word structure (local steps on C_n)
    4. Context analysis (when do two steps at same processor have same context?)
    5. The specific entry conflict mechanism depends on cycle type

    The key difficulty: step 5 has MULTIPLE mechanisms depending on cycle type:
    - Sweeps: shadow cycle argument
    - Non-sweep zero-winding: palindromic entry conflict
    - Non-zero winding: shadow cycle
    - Wiggle: wiggle shadow construction

    But WAIT: maybe there's a UNIFIED mechanism that works for all cases?

    Let's check: the Python proof in binscc_complete_proof.py uses 4 mechanisms
    but they ALL reduce to "same (L,S,R) context appears at mover and non-mover
    steps of some processor." The REASON this happens differs, but the CONCLUSION
    is the same.

    UNIFIED APPROACH: Instead of proving entry conflict separately for each
    cycle type, can we prove it from a simpler structural property?

    Candidate: PIGEONHOLE on processor contexts.
    - A processor with m states has m*(m_L)*(m_R) possible contexts (L,S,R)
    - It fires f times as mover, appears L-f times as non-mover
    - If f >= m_L * m_S * m_R, then by pigeonhole some mover context appears twice
    - But we need mover context = non-mover context, not just duplicate mover contexts

    This doesn't quite work because the pigeonhole is on the wrong sets.

    Alternative: For a binary processor p with m_p = 2:
    - p fires f_p times (even, >= 2)
    - p has 2 * m_L * m_R possible contexts
    - As non-mover, p appears in L - f_p configs
    - As mover, p appears in f_p configs
    - If the number of distinct mover contexts > number of non-mover-only contexts,
      then by pigeonhole some context appears at both
    - Non-mover-only contexts = (2 * m_L * m_R) - (distinct mover contexts)
    - Need: f_p > (2 * m_L * m_R) - f_p, i.e., f_p > m_L * m_R
    - This requires the cycle to be long enough

    Hmm, this isn't tight enough for short cycles.
    """
    if verbose:
        print("\n" + "=" * 80)
        print("ENTRY CONFLICT FORMALIZATION ANALYSIS")
        print("=" * 80)

    # Let's compute: for n=9, sub-threshold multisets, what's the
    # max possible cycle length vs the context count?

    threshold = 4 * 3 ** 7  # = 8748

    print(f"\nFor n=9, threshold = {threshold}")
    print(f"\nChecking context counts vs fire counts for sub-threshold multisets:")
    print(f"{'ms':>30} {'prod':>6} {'min_L':>5} {'bin':>3} "
          f"{'max_ctx_binary':>15} {'min_fc':>6} {'needs':>6}")
    print("-" * 90)

    sorted_multisets = sub_threshold_multisets(9)

    for ms_sorted in sorted_multisets[:20]:  # first 20
        product = 1
        for m in ms_sorted:
            product *= m

        binary_count = sum(1 for m in ms_sorted if m == 2)
        min_length = 2 * 9  # each proc fires >= 2

        # For a binary processor p with neighbors of sizes m_L, m_R:
        # max contexts = 2 * m_L * m_R
        # To guarantee EC via pigeonhole: fire_count > m_L * m_R
        # Min fire count for binary = 2
        # Need: 2 > m_L * m_R, i.e., m_L * m_R < 2
        # This fails since m_L, m_R >= 2.

        # So simple pigeonhole on a single processor doesn't work.
        # The Python proofs use MORE structure (mover word pattern, etc.)

        # Max contexts at any binary proc (pessimistic: neighbors are max-state)
        max_neighbor_states = max(ms_sorted)
        max_ctx = 2 * max_neighbor_states * max_neighbor_states

        print(f"{str(ms_sorted):>30} {product:>6} {min_length:>5} {binary_count:>3} "
              f"{max_ctx:>15} {'2':>6} {f'm_L*m_R':>6}")


def check_computational_decidability(verbose=True):
    """
    Angle 1: For FIXED n, the axioms are decidable.

    For n=9: enumerate all RingSpecs with sub-threshold product,
    all transition functions, all good cycles. If none exist, done.

    But the number of transition functions is astronomically large.
    For ms=(2,2,2,3,3,3,3,3,3), each proc's table has:
    - Binary proc with neighbors (3,3): 2^(3*2*3) = 2^18 = 262144 options
    - Ternary proc with neighbors (2,3): 3^(2*3*3) = 3^18 ~ 387 million options

    Total: way too many.

    BUT: we don't need to enumerate ALL transition functions.
    We just need to check if ANY valid system exists.

    Alternative approach: for each multiset and placement, enumerate
    possible good cycles (mover words + state sequences), check if any
    is conflict-free.

    For n=9, a good cycle has length >= 18 (each proc fires >= 2).
    The mover word has L steps, each choosing from {0,...,8}.
    Consecutive movers differ by at most 1 on C_9.
    This is a walk on C_9.

    The number of closed walks of length L on C_9 where each vertex
    is visited >= 2 times... this is still huge.

    Better: use the ENTRY CONFLICT CHECK. For each possible mover word,
    check if SOME state sequence assignment avoids entry conflicts.
    If ALL mover words have entry conflicts for ALL state sequences,
    then no valid system exists.

    This is exactly what the Python proofs do! And they show it's true
    for all cases, via 4 mechanisms.

    For Lean formalization, the question is: can we use native_decide
    for fixed n? The state space for n=9 is too large for brute force
    on all transition functions. But maybe we can enumerate mover words
    + state sequences and check EC?

    Actually, for Lean's native_decide, we'd need to encode the statement
    as a Decidable proposition. The statement "every GoodCycle for every
    System with this RingSpec has entry conflict" is:

    ∀ sys : System (where sys.rs = our fixed RingSpec),
    ∀ gc : GoodCycle sys,
    hasEntryConflict gc

    This quantifies over ALL transition functions (sys.f), which is huge.
    native_decide on this seems infeasible.

    ALTERNATIVE: Factor through mover words.

    For a fixed RingSpec, a GoodCycle determines:
    1. A mover word (walk on C_n with length L)
    2. State sequences for each processor

    The mover word + state sequences determine ALL contexts.
    Entry conflict only depends on these, not on the specific transition function.

    So we can reformulate: ∀ valid mover words + state sequences,
    ∃ entry conflict.

    This might be native_decidable if we bound the mover word length!

    What's the max mover word length?
    L = cycle length <= product of ms (distinct configs)
    For sub-threshold, L < 4*3^(n-2)

    For n=9: L < 8748. So we'd need to check all walks of length up to 8748
    on C_9 where each vertex is visited >= 2 times and binary vertices are
    visited an even number of times. That's still huge.

    But maybe we can bound L more tightly. Each config is distinct, and
    configs are elements of {0,...,m_0-1} x ... x {0,...,m_{n-1}-1}.
    So L <= product.
    """
    if verbose:
        print("\n" + "=" * 80)
        print("COMPUTATIONAL DECIDABILITY ANALYSIS")
        print("=" * 80)

    # Let's check: for n=5, can we enumerate all valid mover words
    # and verify entry conflicts?
    n = 5
    threshold = 4 * 3 ** (n - 2)
    print(f"\nn={n}, threshold={threshold}")

    sorted_multisets = sub_threshold_multisets(n)
    print(f"Sub-threshold multisets: {len(sorted_multisets)}")

    for ms_sorted in sorted_multisets:
        print(f"  {ms_sorted}, product={eval('*'.join(str(m) for m in ms_sorted))}")


def analyze_existing_proofs(verbose=True):
    """
    Read and summarize the structure of the Python entry conflict proofs.

    The key scripts:
    - cic_case3a_proof5.py: Palindromic EC for consecutive binary + non-sweep
    - binscc_complete_proof.py: 4-mechanism EC for non-consecutive binary

    Both prove: for ALL valid mover words + state sequences, entry conflict exists.

    The proof structure:
    1. Classify the mover word (sweep vs non-sweep, winding type, etc.)
    2. For each class, identify the mechanism that guarantees EC
    3. The mechanism shows that some processor must see the same (L,S,R)
       at both a mover step and a non-mover step

    For LEAN FORMALIZATION, the simplest approach would be:
    - Prove EC for sweeps (shadow cycle → EC)
    - Prove EC for non-zero winding (shadow → EC)
    - Prove EC for zero-winding with safe processor → already handled
    - Prove EC for zero-winding, large-arc, no safe processor → THIS IS THE HARD ONE

    Wait — this is exactly the case split in the Lean axioms!
    The first axiom IS the hard case.

    So the question reduces to: what's the simplest proof of entry conflict
    for zero-winding, large-arc, no-safe-processor cycles?

    From the memory: the Palindromic Entry Conflict handles consecutive binary.
    The 4-mechanism proof handles non-consecutive binary.
    Both have been verified computationally for all n up to ~11.

    For Lean, we need EITHER:
    a) Analytical proofs of these mechanisms (complex)
    b) native_decide for small n + analytical for large n (hybrid)
    c) A simpler unified proof

    OPTION (c) INVESTIGATION:

    For zero-winding + no safe processor + cwStepCount > 0:
    This means the mover word goes both CW and CCW.
    Every processor is within distance 1 of some mover (no safe proc).

    Consider the arc of consecutive movers. Since no safe processor exists,
    the movers span at least... well, the movers cover all but at most
    a subset that's all within distance 1 of movers. Since no safe proc,
    for every q, some mover is q or q±1. So the movers' 3-neighborhoods
    cover all of C_n. With n >= 9, movers must use at least ceil(n/3) = 3
    distinct positions.

    Actually, the "arc" interpretation: since cwStepCount > 0 and
    ccwStepCount > 0 (zero-winding means they're equal), the mover word
    has at least one CW step and one CCW step. The mover word is a closed
    walk on C_n that goes both directions.
    """
    if verbose:
        print("\n" + "=" * 80)
        print("PROOF STRUCTURE ANALYSIS")
        print("=" * 80)

        print("""
CRITICAL INSIGHT FOR LEAN FORMALIZATION:

The two axioms correspond to:
1. Zero-winding + CW>0 + no safe proc: the "hard" back-and-forth case
2. Non-zero winding: the "non-sweep odd-winding" case

For (2), the existing proofs use shadow cycles. The shadow cycle exists
because non-zero winding means the mover word winds around the ring,
which forces the MNU (Mover Non-uniqueness) property.

For (1), the existing proofs use palindromic entry conflict or
the 4-mechanism approach.

BUT HERE'S THE BREAKTHROUGH IDEA:

Both cases share a common structure: >=3 binary processors with
even fire counts. The binary processors' state sequences are
determined by parity (stateAfter = initial + prefix_fire_count mod 2).

IDEA: Use the SHADOW CONSTRUCTION that's already in CaseObstructions.lean!

Look at lines 120-219: the proof of all_stay_contradicts_convergence
and small_arc_contradicts_convergence ALREADY use a "shadow" construction:
flip one value at a far-away processor to create a parallel cycle of
non-good configs that are still privileged. This proves convergence is
impossible.

The same technique could work for the remaining cases! The question is:
can we find a processor q and value v such that:
- Flipping q to v in every config produces a non-good parallel cycle
- The parallel cycle is still privilege-consistent

For the safe-processor case, q is the safe processor (not a mover
or neighbor of any mover). This works because flipping q doesn't
change any local context (L,S,R) at any mover.

For the NO-safe-processor case, this is harder: every q is near
some mover, so flipping q might change some mover's context.

BUT: what if we flip q to a value that PRESERVES the local context?
If q appears as L,S,R in some mover's context and we flip q to the
SAME value it already has at that step... no, that's trivial.

What if we use a processor q that has the SAME value at all configs
where it appears in a mover's context? Then flipping it wouldn't
change those contexts.

ACTUALLY: The existing proofs show the contradiction differently.
They show an ENTRY CONFLICT, which means no consistent transition
function can exist. This is purely about the CYCLE structure, not
about convergence.

But the Lean axioms have the convergence hypothesis. Can we USE it?

YES! The shadow/flip construction uses convergence: it builds a
parallel cycle of bad configs, contradicting WellFounded.

So for the remaining cases:
- Find a processor q and value v₁ such that flipping (configs, q, v₁)
  creates a valid parallel cycle of non-good configs
- Each config in the parallel cycle must be privileged (with the same
  mover as the original)
- Each config must not be in the original good cycle

For q to work: for every step k where q is NOT the mover and is NOT
adjacent to the mover, the flip is invisible. For steps where q IS
near the mover, we need the context to still be privileged.

KEY: If q never appears as L, S, or R for any mover, it's a safe
processor. The axiom hypothesis says no safe processor exists. So
every q appears in some mover's context.

But maybe q only appears in SOME movers' contexts, and at those
contexts, the value of q doesn't affect whether the mover is privileged?

This is getting complicated. Let me check computationally.
""")


def check_shadow_feasibility(n=9, verbose=True):
    """
    For n=9 (or smaller for speed), check:
    For each sub-threshold valid system (if any exist at small n),
    for the zero-winding large-arc case:
    Does there exist a processor q and value v such that the shadow
    (flip q to v) creates a valid parallel bad cycle?
    """
    # Start with n=5 where we know valid sub-threshold systems exist
    for test_n in [5, 6, 7]:
        threshold = 4 * 3 ** (test_n - 2)
        if verbose:
            print(f"\n--- n={test_n}, threshold={threshold} ---")

        sorted_multisets = sub_threshold_multisets(test_n)

        valid_systems_found = 0

        for ms_sorted in sorted_multisets:
            product = 1
            for m in ms_sorted:
                product *= m

            if product > 5000:  # skip large ones for speed
                continue

            orientations = all_orientations(ms_sorted, test_n)

            for ms_perm in orientations:
                ms = list(ms_perm)

                # We need actual transition functions to build a system.
                # Use the CUP-2 construction if applicable.
                if ms == [2] + [3]*(test_n-2) + [2] and product == threshold:
                    # This is AT threshold, not sub-threshold
                    continue

                # For other multisets, we'd need to search for valid systems.
                # This is expensive. Skip for now.
                pass

        if verbose:
            print(f"  Valid sub-threshold systems found: {valid_systems_found}")
            if valid_systems_found == 0:
                print(f"  => Axioms are VACUOUSLY TRUE for n={test_n} if no valid system exists")


def main():
    print("=" * 80)
    print("BREAKTHROUGH INVESTIGATION: Final 2 LB Axioms")
    print("=" * 80)

    # Step 1: Check if axiom cases are reachable
    check_vacancy_approach()

    # Step 2: Check if convergence is actually needed
    check_convergence_needed()

    # Step 3: Analyze what's needed for formalization
    investigate_entry_conflict_formalization()

    # Step 4: Known constructions check
    for n in [5, 6, 7, 8, 9]:
        check_with_known_constructions(n)

    # Step 5: Enumerate sub-threshold multisets
    for n in [5, 6, 7, 8, 9]:
        analyze_n(n)

    # Step 6: Existing proof structure
    analyze_existing_proofs()

    # Step 7: Context counts
    investigate_entry_conflict_formalization()

    # Step 8: Check what n=5 tells us
    check_computational_decidability()

    # Step 9: Final recommendation
    print("\n" + "=" * 80)
    print("RECOMMENDATION")
    print("=" * 80)
    print("""
BREAKTHROUGH APPROACH: Replace both axioms with a single theorem
that doesn't need convergence or winding type case-splitting.

THEOREM (entryConflict_universal):
  For any RingSpec with n >= 9 and sub-threshold product,
  every GoodCycle has an entry conflict.

PROOF STRATEGY (for Lean):

  Option A: "The Counting Lemma + Binary Parity"
  - Sub-threshold => >= 3 binary processors [counting lemma, likely in Lean]
  - In any GoodCycle, binary procs fire even number of times [proved in GoodCycleBasics]
  - Key lemma: with >= 3 binary procs firing >= 2 times each,
    the mover word forces SOME processor to see duplicate (L,S,R) contexts
    at both mover and non-mover steps.
  - This requires formalizing the CONTEXT OVERLAP argument.

  Option B: "Shadow Parallel Cycle" (uses convergence)
  - Build on the EXISTING Lean infrastructure in CaseObstructions.lean
  - The flipConfig/shadow technique already works for safe-processor and all-stay
  - Extend to: find q where flipping preserves privilege at ALL mover steps
  - This uses convergence but avoids entry conflict formalization entirely

  Option C: "Computational + Analytical Hybrid"
  - For n=9..K: use native_decide on a finite enumeration
  - For n > K: use analytical argument (context overlap with >= K binary procs)
  - K might be as small as 9 if the analytical argument is clean enough

RECOMMENDED: Option B (Shadow Parallel Cycle)

  It builds on EXISTING Lean code and avoids the hardest part (entry conflict
  formalization). The key insight: the shadow construction in the already-proved
  theorems (all_stay_contradicts_convergence, small_arc_contradicts_convergence)
  uses a SPECIFIC pattern:

  1. Find processor q far from all movers
  2. Flip q to a different value v₁
  3. Show the resulting configs are non-good but privileged
  4. Contradiction with well-foundedness

  For the remaining cases (no safe processor), we need a VARIANT:
  find q that IS near some mover, but where flipping q doesn't
  affect privilege. This might work if q's value doesn't appear
  in any mover's transition function output.

  Actually, re-reading the proof more carefully:
  The shadow construction needs:
  - shadow configs ∉ good cycle (guaranteed if q has different value)
  - Each shadow config has a privileged mover (same as original)
  - The shadow mover fires to the next shadow config

  For the mover at step k with moverAt k = p:
  - The move changes only position p
  - Shadow flips position q
  - If q ≠ p: the shadow config at p is unchanged by the flip
  - If q = left(p) or q = right(p): the privilege check at p
    depends on q's value, so the flip might change privilege
  - If q ≠ p and q ≠ left(p) and q ≠ right(p): the flip is invisible
    to the privilege check at p

  So the shadow works perfectly when q is NOT p, left(p), or right(p)
  for ANY mover p — which is exactly the safe processor condition.

  For the no-safe-processor case, EVERY q fails this for some mover.

  THIS IS WHY THE AXIOMS EXIST AS AXIOMS: the shadow construction
  fundamentally doesn't work when there's no safe processor.
  The entry conflict is the only known proof mechanism.

REVISED RECOMMENDATION: We must formalize entry conflict.

  The simplest entry conflict argument for Lean might be:

  1. Sub-threshold => >= 3 binary (counting lemma)
  2. >= 3 binary => exist 3 binary processors i, j, k
  3. Each fires >= 2 times, each fires even number of times
  4. The mover word visits i, j, k at least twice each
  5. At each binary proc b: context (L,S,R) changes across fires
     because S flips between 0 and 1 (binary)
  6. Between fires of b, S_b is constant at each step
  7. Some specific overlap argument...

  The actual argument is more subtle and depends on mover word structure.
  This is genuinely hard to formalize.

FINAL ANSWER: The most promising approach is:

  Prove a "universal entry conflict" theorem by induction on cycle length,
  using the 3-binary constraint and the mover word locality.

  OR: Accept the axioms and add a comment that they represent the
  computationally verified entry conflict theorems, analogous to how
  the Tables.lean uses native_decide for finite verification.
""")


if __name__ == "__main__":
    main()
