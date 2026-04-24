"""
ra11_odd_winding_isolated.py — Investigate odd-winding non-uniform cycles
with isolated binary firings in sub-threshold systems with ≥3 non-consecutive binary.

Goal: find a DIRECT proof that isolated binary firings + odd-winding + non-uniform → False,
eliminating the recursion through subThreshold_binary_core_false_residual.

Key questions:
1. Do such cycles even exist?
2. If they have EC, what mechanism produces it?
3. Is procMinGap_hasEntryConflict always applicable with binary p + fc≥2 + gap≥2?
"""
import itertools
from collections import Counter

def make_ring(n):
    """Return left/right functions for ring of size n."""
    def left(p):
        return (p - 1) % n
    def right(p):
        return (p + 1) % n
    return left, right

def generate_good_cycles(n, ms, max_len=None):
    """
    Generate ALL good cycles for ring system with state sizes ms.
    A good cycle is a sequence of (config, mover) pairs that:
    - Forms a cycle (last config transitions back to first)
    - Each config is "good" (all processors see distinct neighbors or self)
    - At each step, exactly one processor fires

    For efficiency, we use DFS from each starting config.
    """
    left, right = make_ring(n)

    if max_len is None:
        max_len = 4 * n  # reasonable bound for small n

    # Generate all configs
    ranges = [range(m) for m in ms]
    all_configs = list(itertools.product(*ranges))

    def is_good(config):
        """A config is good if it could appear in a valid system's good cycle.
        For token ring: exactly the configs where some processor has a 'token'.
        Actually for our purposes, any config can appear; goodness is a system property.
        We'll just generate all reachable cycles."""
        return True

    def apply_move(config, mover, ms):
        """Apply one step: mover fires, changing its state.
        For a general system, the transition depends on (left_val, self_val, right_val).
        But we don't have a fixed transition function - we're looking for ANY good cycle.
        So we enumerate all possible next states for the mover."""
        results = []
        c = list(config)
        for new_val in range(ms[mover]):
            if new_val != c[mover]:  # must change state
                c2 = list(c)
                c2[mover] = new_val
                results.append(tuple(c2))
        return results

    # This is too expensive for n=9. Let's focus on n=5 first.
    cycles = []

    for start_config in all_configs:
        # DFS to find cycles back to start_config
        # State: (current_config, path_of_movers, path_of_configs)
        stack = [(start_config, [], [start_config])]
        while stack:
            curr, movers, configs = stack.pop()
            if len(movers) >= max_len:
                continue
            for mover in range(n):
                for next_config in apply_move(curr, mover, ms):
                    if next_config == start_config and len(movers) >= 2:
                        # Found a cycle!
                        cycles.append((configs, movers + [mover]))
                    elif len(movers) < max_len - 1:
                        stack.append((next_config, movers + [mover], configs + [next_config]))

    return cycles

def total_displacement(movers, n):
    """Compute total displacement of a cycle.
    Each mover p moves in direction right (+1) or left (-1).
    But actually, the mover just changes its own state - displacement
    is about the walk on the ring of which processor fires.

    total displacement = sum of (mover[i+1] - mover[i]) mod n, with sign.
    Actually: W = sum of direction(step i), where direction is
    +1 if mover moves right, -1 if left, 0 if stay.

    For mover word: direction at step i is:
    d_i = (mover[i+1] - mover[i]) mod n, mapped to {-floor(n/2)..ceil(n/2)}
    """
    W = 0
    L = len(movers)
    for i in range(L):
        diff = (movers[(i+1) % L] - movers[i]) % n
        if diff == 0:
            pass  # stay
        elif diff <= n // 2:
            W += diff  # rightward
        else:
            W -= (n - diff)  # leftward
    return W

def step_directions(movers, n):
    """Return list of step directions: +1 (right), -1 (left), 0 (stay)."""
    L = len(movers)
    dirs = []
    for i in range(L):
        diff = (movers[(i+1) % L] - movers[i]) % n
        if diff == 0:
            dirs.append(0)
        elif diff <= n // 2:
            dirs.append(1)
        else:
            dirs.append(-1)
    return dirs

def is_odd_winding(movers, n):
    """
    |totalDisplacement| = n (wraps exactly once around the ring).
    """
    W = total_displacement(movers, n)
    return abs(W) == n

def is_uniform_direction(movers, n):
    """All non-stay steps go the same direction."""
    dirs = step_directions(movers, n)
    non_stay = [d for d in dirs if d != 0]
    if not non_stay:
        return True  # vacuously
    return all(d == non_stay[0] for d in non_stay)

def fire_count(movers, n):
    """Return fire count per processor."""
    fc = [0] * n
    for m in movers:
        fc[m] += 1
    return fc

def has_isolated_firings(movers, p):
    """Check if processor p has only isolated firings (no consecutive fires)."""
    L = len(movers)
    for i in range(L):
        if movers[i] == p and movers[(i+1) % L] == p:
            return False
    return True

def is_permanent_mover(movers, p):
    """Check if p fires at every step."""
    return all(m == p for m in movers)

def has_entry_conflict_at_proc(configs, movers, p, n):
    """
    Check if there's an entry conflict at processor p:
    Two steps s1 (mover=p) and s2 (mover≠p) with same (L,S,R) context.
    At mover step: p changes state, so context at step = config BEFORE the move.
    At non-mover step: p doesn't change, context = config at that step.

    Entry conflict: config[s1][left(p)] = config[s2][left(p)] AND
                    config[s1][p] = config[s2][p] AND
                    config[s1][right(p)] = config[s2][right(p)]
    where s1 has mover=p and s2 has mover≠p.
    """
    left_p = (p - 1) % n
    right_p = (p + 1) % n

    mover_contexts = set()
    nonmover_contexts = set()

    for i, m in enumerate(movers):
        ctx = (configs[i][left_p], configs[i][p], configs[i][right_p])
        if m == p:
            mover_contexts.add(ctx)
        else:
            nonmover_contexts.add(ctx)

    return len(mover_contexts & nonmover_contexts) > 0

def has_entry_conflict(configs, movers, n):
    """Check if there's an entry conflict at ANY processor."""
    for p in range(n):
        if has_entry_conflict_at_proc(configs, movers, p, n):
            return True
    return False

def min_firing_gap(movers, p):
    """
    Find the minimum gap between consecutive firings of p.
    Gap = distance (in steps) between consecutive fires.
    Returns (min_gap, a, b) where a and b are step indices of the min-gap pair.
    """
    fire_steps = [i for i, m in enumerate(movers) if m == p]
    if len(fire_steps) < 2:
        return None

    L = len(movers)
    min_gap = L + 1
    best_a, best_b = -1, -1

    for idx in range(len(fire_steps)):
        a = fire_steps[idx]
        b = fire_steps[(idx + 1) % len(fire_steps)]
        if idx + 1 < len(fire_steps):
            gap = b - a
        else:
            gap = L - a + b  # wrap around
        if gap < min_gap:
            min_gap = gap
            best_a, best_b = a, b

    return min_gap, best_a, best_b


def prefix_fire_count(movers, p, t):
    """Number of times p fires in steps 0..t-1."""
    return sum(1 for i in range(t) if movers[i] == p)


def check_mingap_ec(configs, movers, p, n, ms):
    """
    Check if procMinGap_hasEntryConflict applies:
    - p has MinFiringGap with gap ≥ 2
    - Left and right neighbors have even prefix fire count change across gap

    For this to produce EC, we need:
    - 3 consecutive binary at (left(p), p, right(p))
    - gap ≥ 2
    - L-parity and R-parity conditions
    """
    left_p = (p - 1) % n
    right_p = (p + 1) % n

    # Check 3 consecutive binary
    if ms[left_p] != 2 or ms[p] != 2 or ms[right_p] != 2:
        return False, "not 3 consecutive binary"

    result = min_firing_gap(movers, p)
    if result is None:
        return False, "< 2 firings"

    gap, a, b = result
    if gap < 2:
        return False, f"gap={gap} < 2"

    # Check parity conditions for neighbors
    # At step a+1 (first non-mover step after a fires) and step b (next fire)
    # L-parity: prefixFireCount(left_p, a+1) % 2 == prefixFireCount(left_p, b) % 2
    L = len(movers)

    # For non-wrapping gap
    if b > a:
        pfc_L_a1 = prefix_fire_count(movers, left_p, a + 1)
        pfc_L_b = prefix_fire_count(movers, left_p, b)
        pfc_R_a1 = prefix_fire_count(movers, right_p, a + 1)
        pfc_R_b = prefix_fire_count(movers, right_p, b)

        L_parity_match = (pfc_L_a1 % 2 == pfc_L_b % 2)
        R_parity_match = (pfc_R_a1 % 2 == pfc_R_b % 2)

        if L_parity_match and R_parity_match:
            return True, f"mingap EC: gap={gap}, a={a}, b={b}"
        else:
            return False, f"parity mismatch: L={L_parity_match}, R={R_parity_match}, gap={gap}"
    else:
        # Wrapping gap - more complex
        return False, "wrapping gap (skipped)"


def check_any_gap_ec(configs, movers, p, n, ms):
    """
    Check if ANY mover/non-mover pair for p produces entry conflict.
    This is the general_parity_entry_conflict check.

    For 3 consecutive binary (i, p, q):
    Any step t where p doesn't fire, and step b where p fires,
    if all three parities match → EC.
    """
    i = (p - 1) % n  # left of p
    q = (p + 1) % n  # right of p

    # Need 3 consecutive binary
    if ms[i] != 2 or ms[p] != 2 or ms[q] != 2:
        return False, "not 3 consecutive binary at p"

    L = len(movers)
    fire_steps = [s for s in range(L) if movers[s] == p]
    nonfire_steps = [s for s in range(L) if movers[s] != p]

    for b in fire_steps:
        for t in nonfire_steps:
            # Check parity match for all 3 processors
            pfc_i_t = prefix_fire_count(movers, i, t)
            pfc_i_b = prefix_fire_count(movers, i, b)
            pfc_p_t = prefix_fire_count(movers, p, t)
            pfc_p_b = prefix_fire_count(movers, p, b)
            pfc_q_t = prefix_fire_count(movers, q, t)
            pfc_q_b = prefix_fire_count(movers, q, b)

            if (pfc_i_t % 2 == pfc_i_b % 2 and
                pfc_p_t % 2 == pfc_p_b % 2 and
                pfc_q_t % 2 == pfc_q_b % 2):
                return True, f"parity EC: b={b}, t={t}"

    return False, "no parity match found"


# ============================================================
# APPROACH 2: Work directly with mover words (no configs needed)
# The entry conflict is about the CONFIG context, but for binary
# processors the config is determined by prefix fire parity.
# So we only need to check parity conditions on the mover word.
# ============================================================

def generate_mover_words(n, max_len, ms):
    """
    Generate mover words (sequences of processor indices) that could be
    valid good cycles.

    Constraints:
    - fire_count(p) is a multiple of ms[p] for each p (cycle returns to start)
    - Actually for binary: fire_count must be even
    - For ternary: fire_count must be a multiple of 3

    For odd-winding: |totalDisplacement| = n
    For non-uniform: not all non-stay steps same direction
    """
    # This is still exponential. Instead, let's enumerate small cases
    # or use the verifier approach.
    pass


def enumerate_odd_winding_nonuniform_isolated(n, ms, max_len=None):
    """
    Enumerate mover words that are:
    1. Odd-winding (|W| = n)
    2. Non-uniform direction
    3. Have a non-consecutive binary processor p with:
       - fire_count(p) >= 2
       - All firings isolated (no consecutive)
    4. fire_count(q) is a multiple of ms[q] for all q

    For small n, enumerate by DFS on mover words.
    """
    if max_len is None:
        max_len = 3 * n

    # Identify binary processors
    binary_procs = [p for p in range(n) if ms[p] == 2]

    # Check ≥3 non-consecutive binary
    def has_3_nonconsec_binary():
        if len(binary_procs) < 3:
            return False
        # Check no 3 consecutive
        for p in range(n):
            if ms[p] == 2 and ms[(p+1)%n] == 2 and ms[(p+2)%n] == 2:
                return True  # has 3 consecutive - we want NON-consecutive case
        return True  # ≥3 binary but no 3 consecutive

    def no_three_consecutive():
        for p in range(n):
            if ms[p] == 2 and ms[(p+1)%n] == 2 and ms[(p+2)%n] == 2:
                return False
        return True

    if len(binary_procs) < 3 or not no_three_consecutive():
        return []

    results = []

    # DFS enumeration of mover words
    def dfs(word, fc, displacement):
        L = len(word)

        # Pruning: if displacement is too far from ±n, give up
        if L > 0 and abs(displacement) > n + (max_len - L) * 1:
            return

        if L >= 2:
            # Check if this could be a valid cycle
            # fire_count divisibility check
            valid_fc = all(fc[p] % ms[p] == 0 for p in range(n))

            if valid_fc and abs(displacement) == n:
                # Check non-uniform
                dirs = step_directions(word, n)
                non_stay = [d for d in dirs if d != 0]
                if non_stay and not all(d == non_stay[0] for d in non_stay):
                    # Check isolated firings for some binary proc
                    for p in binary_procs:
                        if fc[p] >= 2 and has_isolated_firings(word, p) and not is_permanent_mover(word, p):
                            results.append(list(word))
                            return  # found one, don't need duplicates from this branch

        if L >= max_len:
            return

        for mover in range(n):
            # Compute direction
            if L == 0:
                d = 0  # first step, no direction yet
            else:
                diff = (mover - word[-1]) % n
                if diff == 0:
                    d = 0
                elif diff <= n // 2:
                    d = diff
                else:
                    d = -(n - diff)

            fc[mover] += 1
            word.append(mover)
            dfs(word, fc, displacement + d)
            word.pop()
            fc[mover] -= 1

    # This is too slow for n=9. Let's try n=5 first.
    fc = [0] * n
    dfs([], fc, 0)
    return results


def quick_check_small_n():
    """Check at n=5 with ms=(2,3,2,3,2) — 3 non-consecutive binary."""
    n = 5
    # Non-consecutive binary: positions 0, 2, 4 are binary, 1, 3 are ternary
    ms = [2, 3, 2, 3, 2]

    print(f"=== n={n}, ms={ms} ===")
    print(f"Binary procs: {[p for p in range(n) if ms[p] == 2]}")
    print(f"Product: {eval('*'.join(str(m) for m in ms))}")
    print(f"Sub-threshold (< 4*3^{n-2} = {4*3**(n-2)})? {eval('*'.join(str(m) for m in ms)) < 4*3**(n-2)}")
    print()

    # For n=5 with non-consecutive binary, try to find odd-winding non-uniform
    # cycles with isolated binary firings.

    # Constraint: |W| = 5, non-uniform, each binary fires even times,
    # each ternary fires multiple-of-3 times.

    # Minimum cycle length: each proc must fire ≥ once for odd winding
    # (every edge traversed > 0). Binary fires ≥ 2. So min length ≥ 2*3 + 3*1 = 9?
    # Actually ternary fires multiples of 3, so ≥ 3 each. Binary ≥ 2 each.
    # Min: 3*2 + 2*3 = 12.

    print("Searching for odd-winding non-uniform words with isolated binary firings...")
    print("(This may take a while for larger max_len)")

    for max_len in [12, 14, 16]:
        results = enumerate_odd_winding_nonuniform_isolated(n, ms, max_len=max_len)
        print(f"  max_len={max_len}: found {len(results)} words")
        if results:
            for w in results[:5]:
                fc_w = fire_count(w, n)
                W = total_displacement(w, n)
                dirs = step_directions(w, n)
                print(f"    word={w}, len={len(w)}, fc={fc_w}, W={W}")
                print(f"    dirs={dirs}")

                # Check EC via parity for each binary proc
                for p in [0, 2, 4]:
                    if fc_w[p] >= 2 and has_isolated_firings(w, p):
                        ec, reason = check_any_gap_ec(None, w, p, n, ms)
                        print(f"    Binary {p}: isolated, fc={fc_w[p]}, parity_EC={ec} ({reason})")
            break


def approach_mingap_universal():
    """
    Key theoretical question: for a binary processor p with fc ≥ 2 and all
    isolated firings, does the min-gap always produce EC?

    With isolated firings, gap ≥ 2 at every gap (from allIsolated_gap_ge2).
    The min gap has a pair (a, b) with p firing at both a and b.
    Between a and b (exclusive), p doesn't fire.

    For 3 consecutive binary (i, p, q):
    - S-parity: p doesn't fire in (a,b), so pfc(p,a+1) % 2 = pfc(p,b) % 2 ✓
    - L-parity: need pfc(i, a+1) % 2 = pfc(i, b) % 2
    - R-parity: need pfc(q, a+1) % 2 = pfc(q, b) % 2

    L-parity fails iff i fires an odd number of times in [a+1, b).
    R-parity fails iff q fires an odd number of times in [a+1, b).

    For non-consecutive binary with isolated firings:
    There's no "3 consecutive binary" to use! The parity argument requires
    3 consecutive binary processors.

    BUT: for non-consecutive binary, we have ≥3 binary with no 3 consecutive.
    So we CAN'T use procMinGap_hasEntryConflict directly.

    Wait - let me re-read the problem. The non-consecutive case in the Lean code
    picks a binary p from exists_binary_nonadjacent_pair. The key issue is:
    for a GENERAL binary processor (not necessarily with binary neighbors),
    the parity argument doesn't work because the neighbors might be ternary.

    So the question becomes: what mechanism kills isolated firings of a binary
    processor whose neighbors are ternary?
    """
    print("=== Analysis: MinGap EC applicability ===")
    print()
    print("For procMinGap_hasEntryConflict, we need:")
    print("  - threeConsecutiveBinary sys.rs i  (3 consecutive binary at i, i+1, i+2)")
    print("  - MinFiringGap for right(i) = middle of the triple")
    print("  - gap ≥ 2")
    print("  - L-parity and R-parity conditions")
    print()
    print("For non-consecutive binary case:")
    print("  - We have ≥3 binary, but NO 3 consecutive")
    print("  - So any binary p has at least one non-binary neighbor")
    print("  - The parity argument for CONFIG equality fails at non-binary neighbors")
    print("  - We CANNOT use procMinGap_hasEntryConflict")
    print()
    print("This means we need a DIFFERENT mechanism for the non-consecutive case.")
    print("The current code routes through subThreshold_binary_core_false_residual")
    print("which is the full global dispatch (the recursion we want to eliminate).")


def check_real_ec_mechanism():
    """
    For non-consecutive binary with isolated firings:
    What actually produces the contradiction?

    The UEC 4-mechanism proof works on good cycles directly:
    1. Both-Even Return
    2. Toggle-FR
    3. Zero-Side EC
    4. Traversal Return

    These work on the actual configs, not just mover words.
    They need ≥3 non-adjacent binary at sub-threshold.

    Let's check: given a mover word with isolated binary firings + odd winding
    + non-uniform, can we always find EC via one of these mechanisms
    WITHOUT going through the global dispatch?

    The answer might be: the isolated firings condition is itself enough
    to produce EC directly, because:

    For binary p with isolated firings and fc ≥ 2:
    - At each fire step a, the next step a+1 has a different mover
    - So at step a+1, p is a non-mover with context (L, S', R) where S' = new value
    - At step a, p was a mover with context (L_a, S_a, R_a)
    - After firing, p's value changes: S' ≠ S_a
    - But the NEXT time p fires (step b), its context is (L_b, S_b, R_b)
    - If S_b = S_a (binary returns after even gap), and L_b = L_a, R_b = R_a,
    -   then we have EC between step a (mover) and some non-mover step with same context.

    Wait, this IS the parity argument but it requires binary neighbors.

    For ternary neighbors: the context includes ternary values, so we need
    a different approach.
    """
    print("\n=== Checking: what works for non-consecutive binary isolated ===")
    print()
    print("The key insight for non-consecutive binary p with ternary neighbors:")
    print("  - p fires at steps a and b with gap ≥ 2")
    print("  - Between a and b, some other procs fire")
    print("  - The ternary neighbors' values are NOT determined by parity alone")
    print()
    print("BUT: odd-winding gives us |W| = n ≥ 9")
    print("Every processor fires ≥ 1 time (from edge traversal > 0)")
    print("Binary procs fire ≥ 2 times (even)")
    print()
    print("Permanent mover is already eliminated (→ W=0, contradicts |W|=n).")
    print("So we have isolated firings.")
    print()
    print("The crucial question: can we get EC from isolated firings alone,")
    print("using properties of odd-winding + non-uniform?")
    print()
    print("ALTERNATIVE APPROACH: odd-winding + non-uniform implies the mover word")
    print("has both CW and CCW steps. This creates a 'reversal' somewhere.")
    print("At a reversal, the mover goes ...p, p+1, p, ... or similar.")
    print("If the middle step is a binary processor, this creates an EC opportunity.")


def systematic_mover_word_search():
    """
    Systematically search for mover words at small n that satisfy:
    1. ≥3 non-consecutive binary (no 3 consecutive)
    2. Odd-winding (|W| = n)
    3. Non-uniform direction
    4. All fire counts divisible by state sizes
    5. Some binary p has fc ≥ 2, isolated firings, NOT permanent

    Use constraint-based approach: fix fc vector, enumerate orderings.
    """
    n = 5
    ms = [2, 3, 2, 3, 2]  # binary at 0,2,4; ternary at 1,3

    print(f"\n=== Systematic search at n={n}, ms={ms} ===")

    # Fire count must satisfy:
    # fc[p] % ms[p] == 0 for all p
    # sum(fc) = L (cycle length)
    # Binary fires: multiples of 2 (≥ 2 for odd winding)
    # Ternary fires: multiples of 3 (≥ 3 for odd winding)

    # Minimum: fc = [2, 3, 2, 3, 2] → L = 12
    # But |W| = 5, which is hard to achieve with L=12...

    # W = sum of step directions. Each step contributes ±1 or 0.
    # |W| = n = 5 means net displacement is exactly 5.
    # With L steps, we need net = 5.
    # If R steps go right and L_steps go left, R - L_steps = ±5, R + L_steps ≤ L.
    # Non-uniform: both R > 0 and L_steps > 0 (or stays involved).

    # Actually non-uniform means not all non-stay steps go the same direction.
    # So we need at least one CW step and one CCW step.

    # For |W| = 5 (say W = 5): we need 5 more rightward than leftward.
    # With both directions present: R ≥ 1, L ≥ 1, R - L = 5, so R = L + 5.
    # Min: L=1, R=6, total non-stay = 7 ≤ 12. OK.

    # But directions are determined by consecutive mover positions, not freely chosen.
    # mover[i] → mover[i+1]: direction is (mover[i+1] - mover[i]) mod n.

    # For n=5: right = +1, left = -1 (mod 5), but +2 is also "right" and -2 is also "left".
    # Actually for n=5: +1,+2 are right (mapped to +1,+2); -1,-2 are left (mapped to -1,-2).
    # Wait, the standard: diff in {1,...,floor(n/2)} → right, else left.
    # For n=5: floor(5/2)=2. So diff=1,2 → right (+1,+2), diff=3,4 → left (-2,-1).

    # Hmm, this means steps can contribute ±1 or ±2 to displacement.
    # So |W| = 5 doesn't require 5 net unit steps.

    print("Fire count vectors (fc[0..4]):")

    found_words = []

    # Try small fc vectors
    for fc0 in range(2, 8, 2):
        for fc1 in range(3, 10, 3):
            for fc2 in range(2, 8, 2):
                for fc3 in range(3, 10, 3):
                    for fc4 in range(2, 8, 2):
                        L = fc0 + fc1 + fc2 + fc3 + fc4
                        if L > 20:  # keep it manageable
                            continue
                        if L < n:
                            continue

                        fc = [fc0, fc1, fc2, fc3, fc4]

                        # Quick check: can |W| = 5?
                        # Each step contributes at most 2 to displacement
                        # So |W| ≤ 2*L. Since |W| = 5 ≤ 2*L always for L ≥ 3. OK.

                        # Enumerate some random orderings to check feasibility
                        import random

                        word_template = []
                        for p in range(n):
                            word_template.extend([p] * fc[p])

                        # Try random shuffles
                        for trial in range(200):
                            word = list(word_template)
                            random.shuffle(word)

                            W = total_displacement(word, n)
                            if abs(W) != n:
                                continue

                            dirs = step_directions(word, n)
                            non_stay = [d for d in dirs if d != 0]
                            if not non_stay or all(d == non_stay[0] for d in non_stay):
                                continue  # uniform

                            # Check isolated binary
                            for p in [0, 2, 4]:
                                if fc[p] >= 2 and has_isolated_firings(word, p):
                                    found_words.append((list(word), p))
                                    break

                        if len(found_words) >= 50:
                            break
                    if len(found_words) >= 50:
                        break
                if len(found_words) >= 50:
                    break
            if len(found_words) >= 50:
                break
        if len(found_words) >= 50:
            break

    print(f"Found {len(found_words)} candidate mover words")

    if found_words:
        # Now check: for each, does parity-based EC work?
        ec_count = 0
        no_ec_count = 0

        for word, p in found_words:
            ec, reason = check_any_gap_ec(None, word, p, n, ms)
            if ec:
                ec_count += 1
            else:
                no_ec_count += 1
                if no_ec_count <= 3:
                    fc_w = fire_count(word, n)
                    print(f"  NO parity EC: word={word}, p={p}, fc={fc_w}")
                    print(f"    reason: {reason}")
                    # Check if any OTHER binary proc has 3-consec and EC
                    for p2 in [0, 2, 4]:
                        if p2 != p and fc_w[p2] >= 2:
                            ec2, reason2 = check_any_gap_ec(None, word, p2, n, ms)
                            print(f"    Alt binary {p2}: fc={fc_w[p2]}, parity_EC={ec2}")

        print(f"\nParity EC: {ec_count}/{len(found_words)}")
        print(f"No parity EC: {no_ec_count}/{len(found_words)}")

    return found_words


def main():
    print("=" * 70)
    print("Investigation: odd-winding non-uniform + isolated binary firings")
    print("=" * 70)
    print()

    approach_mingap_universal()
    check_real_ec_mechanism()

    print("\n" + "=" * 70)
    print("Part 2: Systematic mover word search")
    print("=" * 70)

    found = systematic_mover_word_search()

    print("\n" + "=" * 70)
    print("Part 3: Key theoretical observations")
    print("=" * 70)
    print()
    print("CRITICAL OBSERVATION:")
    print("For non-consecutive binary, procMinGap_hasEntryConflict CANNOT be used")
    print("because it requires threeConsecutiveBinary. The neighbors are ternary.")
    print()
    print("The consecutive case (lines 1073-1089) handles isolated firings via")
    print("consecutive_binary_isolated_false, which IS sorry-free.")
    print()
    print("The non-consecutive case (lines 1104-1119) is the problem.")
    print("It routes through the full global dispatch.")
    print()
    print("POSSIBLE DIRECT PROOF STRATEGIES:")
    print()
    print("Strategy 1: Use odd-winding structure directly")
    print("  - |W| = n means every edge traversed ≥ 1 time")
    print("  - Non-uniform: ∃ CW step AND ∃ CCW step")
    print("  - At the 'reversal' point, the mover direction changes")
    print("  - This reversal point may create an EC opportunity")
    print()
    print("Strategy 2: Binary isolated + ternary neighbor counting")
    print("  - Binary p fires even times, all isolated (gap ≥ 2)")
    print("  - In each gap, some ternary neighbor must fire")
    print("  - Total ternary fires = 3k, distributed across gaps")
    print("  - Pigeonhole: some gap has ternary neighbor firing ≡ 0 mod 2")
    print("  - Combined with p's return (binary parity): context match → EC")
    print()
    print("Strategy 3: Leverage no_safeProcessor")
    print("  - From oddWinding: every proc fires ≥ 1")
    print("  - ¬safeProcessor: every proc is within distance 1 of some mover")
    print("  - This is derivable from oddWinding (already done in the code)")
    print("  - Then apply the SAME mechanism as the zero-winding case")


if __name__ == "__main__":
    import random
    random.seed(42)
    main()
