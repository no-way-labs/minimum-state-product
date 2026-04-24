#!/usr/bin/env python3
"""
ra14_clean_proof.py — Clean proof of structural EC for odd-winding
non-uniform mover words with >= 3 non-consecutive binary.

=== THEOREM ===

Let gc be a good cycle in a system with state vector ms having:
- n >= 5 processors on a ring
- >= 3 binary processors (ms[p] = 2), no three consecutive
- (n-3) ternary processors (ms[p] = 3)
- product(ms) < 4 * 3^(n-2) (sub-threshold)

If gc has odd winding (|totalDisplacement| = n), then gc has
structural entry conflict.

=== PROOF ===

The mover word is a +-1 cyclic walk of length CL on the ring Z_n.
Fire count fc[p] = (number of times p appears in the mover word).
Each fc[p] is a positive multiple of ms[p] (state returns after full cycle).
CL = sum(fc[p]) = 2A + 3B, where:
  A = sum of binary fire count multipliers (fc_binary / 2)
  B = sum of ternary fire count multipliers (fc_ternary / 3)

=== Step 1: Parity analysis ===

For a +-1 cyclic walk of length CL with winding W = CW - CCW:
  CW + CCW = CL
  |CW - CCW| = n
  => CW = (CL + n)/2 or (CL - n)/2
  => CL + n must be even.

CL + n = 2A + 3B + n. Mod 2: CL + n ≡ B + n (mod 2).
So CL + n even iff B ≡ n (mod 2).

=== Step 2: B parity forces large CL ===

B_min = (n-3) (each ternary fires exactly ms[p] = 3 times, multiplier 1).
B_min mod 2 = (n-3) mod 2 = (n+1) mod 2 (opposite parity to n).

If B ≡ B_min (mod 2): CL + n is odd, winding +-n is impossible. Case vacuous.

If B ≢ B_min (mod 2): at least one ternary multiplier increased.
  The minimum such B = B_min + 1 = n - 2.
  CL >= CL_min + 3 = 3(n-1) + 3 = 3n.

For n >= 7: CL >= 3n >= 21.

=== Step 3: Pigeonhole at binary processor (n >= 7) ===

Pick any binary processor p with ms[p] = 2 (non-consecutive: both neighbors ternary).
Boundary triple residue space R_p = Z_{ms[L]} x Z_{ms[p]} x Z_{ms[R]} = Z_3 x Z_2 x Z_3.
|R_p| = 18.

Each step t of the walk maps to a residue triple:
  r(t) = (pfc_L(t) mod 3, pfc_p(t) mod 2, pfc_R(t) mod 3).

Steps split into: mover steps (word[t] = p, fc[p] of them) and non-mover steps (CL - fc[p]).

CLAIM: For CL > 18 (which holds since CL >= 21 > 18 for n >= 7):
  the residue mapping r: {0,...,CL-1} -> R_p has at least one mover-nonmover collision.

PROOF of CLAIM:
  CL > 18 = |R_p|. By pigeonhole, some residue triple is hit by >= 2 steps.
  We need: SOME triple is hit by both a mover and a non-mover step.

  Suppose for contradiction: every triple hit by a mover is NOT hit by any non-mover.
  Then the mover set and non-mover set have disjoint residue images.
  |mover image| + |non-mover image| <= |R_p| = 18.
  |mover image| <= fc[p]. |non-mover image| <= CL - fc[p].
  But also: |mover image| + |non-mover image| <= 18.

  Now: each residue triple in the non-mover image is hit by >= 1 non-mover step.
  Total non-mover steps = CL - fc[p].
  |non-mover image| <= min(CL - fc[p], 18).

  The constraint is: |mover image| <= 18 - |non-mover image|.

  This is satisfiable if fc[p] <= 18 - |non-mover image|, which is possible.

  So the direct pigeonhole argument doesn't force cross-type collision. FAIL.

  We need a STRUCTURAL argument for cross-type collision.

=== Step 4: Structural cross-type collision ===

Decompose by pfc_p mod 2:
  - Parity-0 subspace: (pfc_L mod 3, 0, pfc_R mod 3). Size 9.
  - Parity-1 subspace: (pfc_L mod 3, 1, pfc_R mod 3). Size 9.

Mover at fire 1 (pfc_p = 0): in parity-0. Pair (a1, b1).
Mover at fire 2 (pfc_p = 1): in parity-1. Pair (a2, b2).

Non-movers: split between parity-0 and parity-1.

For EC: need (a1, b1) among parity-0 non-mover pairs, OR (a2, b2) among parity-1 non-mover pairs.

The pair (pfc_L mod 3, pfc_R mod 3) at step t depends only on how many L-fires and R-fires
occurred before step t. Let's write it as (fL(t) mod 3, fR(t) mod 3) where fL(t) = #{s < t : word[s] = L}.

At step 0: (0, 0).
At step s1 (first fire of p): (fL(s1) mod 3, fR(s1) mod 3) = (a1, b1).
At step s2 (second fire of p): (fL(s2) mod 3, fR(s2) mod 3) = (a2, b2).
After full cycle: (fc_L mod 3, fc_R mod 3) = (0, 0).

The walk visits p twice: at s1 and s2. Between these visits:
The walk leaves p, traverses some subpath, and returns to p.
On this subpath: L is visited some d_L times, R is visited d_R times.
fL(s2) = fL(s1) + d_L. fR(s2) = fR(s1) + d_R.
a2 = (a1 + d_L) mod 3. b2 = (b1 + d_R) mod 3.

After s2 and wrapping back to s1: L is visited fc_L - fL(s1) - d_L more times,
R is visited fc_R - fR(s1) - d_R more times.

In the parity-0 segment (steps not between s1 and s2):
- Before s1: fL goes from 0 to fL(s1), fR goes from 0 to fR(s1).
  L fires fL(s1) times, R fires fR(s1) times.
- After s2: fL goes from fL(s2)+? to fc_L (wrapping), fR similarly.
  Wait, after s2: the walk continues from position (s2+1) and wraps around.
  fL at the start of the wrap = fL(s2) + (1 if word[s2] = L... no, fL counts fires of L).
  After step s2: fL(s2+1) = fL(s2) + (1 if word[s2] = L else 0).
  But word[s2] = p (p fires at s2), and p != L. So fL(s2+1) = fL(s2).
  Similarly fR(s2+1) = fR(s2).
  Then fL goes from fL(s2) to fc_L and fR from fR(s2) to fc_R.
  In mod 3: from (a2 + residual_L, b2 + residual_R) to (0, 0).
  Where residual_L = fL(s1) + d_L ... let me just track the residues.

In the parity-0 segment, the pair traces:
  (0, 0) -> ... -> (a1, b1) [mover, then jump to parity-1]
  ... parity-1 segment (s1+1 to s2-1) ...
  (a2, b2) [mover, back to parity-0]
  (a2', b2') -> ... -> (0, 0) [wrapping back to start]

Actually wait, after the second fire at s2, the pair in the parity-0 class continues
from (fL(s2+1) mod 3, fR(s2+1) mod 3) = ((a1 + d_L) mod 3, (b1 + d_R) mod 3).
Hmm, this is getting complex. Let me just check computationally: for the walks where
edge counts show existence, does EC always hold?

Since the DFS is too slow, let me use the edge counts to CONSTRUCT walks.
"""

def solve_edge_counts(n, fc, winding=1):
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
    if coeff == 0:
        if rhs != 0:
            return None
        import math
        lower = float('-inf')
        upper = float('inf')
        for k in range(n):
            if S[k] > 0:
                lower = max(lower, -A[k] / S[k])
            elif S[k] < 0:
                upper = min(upper, -A[k] / S[k])
            else:
                if A[k] < 0:
                    return None
        if lower > upper:
            return None
        c0 = max(int(lower) if lower == int(lower) else int(lower) + 1, 0)
        if c0 > upper:
            return None
        return [A[k] + S[k] * c0 for k in range(n)]
    else:
        if rhs % coeff != 0:
            return None
        c0 = rhs // coeff
        c = [A[k] + S[k] * c0 for k in range(n)]
        if any(cc < 0 for cc in c):
            return None
        return c


def construct_walk_from_edge_counts(n, fc, c_ccw, winding=1):
    """
    Given edge CCW counts c_ccw and fire counts fc, construct a valid walk.
    e_CW(p) = c_ccw[p] + winding for edge (p, p+1).
    This uses a greedy construction.
    """
    e_cw = [c_ccw[p] + winding for p in range(n)]
    e_ccw = c_ccw[:]

    # remaining_fc[p] = how many more times p needs to fire
    remaining_fc = fc[:]
    # remaining_cw[p] = how many more CW traversals of edge (p, p+1)
    remaining_cw = e_cw[:]
    # remaining_ccw[p] = how many more CCW traversals of edge (p, p+1)
    remaining_ccw = e_ccw[:]

    CL = sum(fc)
    # Start at position 0
    walk = [0]
    remaining_fc[0] -= 1

    for step in range(CL - 1):
        pos = walk[-1]
        # Can go CW (to pos+1) if there's a remaining CW traversal of edge (pos, pos+1)
        # AND pos+1 still needs fires.
        nxt_cw = (pos + 1) % n
        nxt_ccw = (pos - 1) % n

        can_cw = remaining_cw[pos] > 0 and remaining_fc[nxt_cw] > 0
        can_ccw = remaining_ccw[(pos - 1) % n] > 0 and remaining_fc[nxt_ccw] > 0

        if not can_cw and not can_ccw:
            return None  # Stuck

        # Greedy: prefer the direction with more remaining
        if can_cw and can_ccw:
            # Choose based on remaining needs
            if remaining_cw[pos] >= remaining_ccw[(pos-1) % n]:
                go_cw = True
            else:
                go_cw = False
        elif can_cw:
            go_cw = True
        else:
            go_cw = False

        if go_cw:
            remaining_cw[pos] -= 1
            walk.append(nxt_cw)
            remaining_fc[nxt_cw] -= 1
        else:
            remaining_ccw[(pos - 1) % n] -= 1
            walk.append(nxt_ccw)
            remaining_fc[nxt_ccw] -= 1

    # Check: walk closes (last -> first is +-1)
    diff = (walk[0] - walk[-1]) % n
    if diff != 1 and diff != n - 1:
        return None

    # Check: all fire counts used
    if any(r != 0 for r in remaining_fc):
        return None

    return walk


def check_ec(word, n, ms):
    L = len(word)
    for p in range(n):
        lp = (p - 1) % n
        rp = (p + 1) % n
        pfc_lp = [0] * (L + 1)
        pfc_p = [0] * (L + 1)
        pfc_rp = [0] * (L + 1)
        for t in range(L):
            pfc_lp[t + 1] = pfc_lp[t] + (1 if word[t] == lp else 0)
            pfc_p[t + 1] = pfc_p[t] + (1 if word[t] == p else 0)
            pfc_rp[t + 1] = pfc_rp[t] + (1 if word[t] == rp else 0)
        mover_steps = [t for t in range(L) if word[t] == p]
        nonmover_steps = [t for t in range(L) if word[t] != p]
        for s1 in mover_steps:
            for s2 in nonmover_steps:
                if (pfc_lp[s1] % ms[lp] == pfc_lp[s2] % ms[lp] and
                    pfc_p[s1] % ms[p] == pfc_p[s2] % ms[p] and
                    pfc_rp[s1] % ms[rp] == pfc_rp[s2] % ms[rp]):
                    return True
    return False


def total_displacement(word, n):
    W = 0
    L = len(word)
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 0:
            W += 0
        elif diff <= n // 2:
            W += diff
        else:
            W -= (n - diff)
    return W


def has_no_triple(ms, n):
    for i in range(n):
        if ms[i] == 2 and ms[(i+1) % n] == 2 and ms[(i+2) % n] == 2:
            return False
    return True


from itertools import combinations
import random

print("RA14: Walk Construction + EC Verification")
print("=" * 70)

random.seed(42)

for n in [7, 9, 11]:
    threshold = 4 * (3 ** (n - 2))
    print(f"\nn={n}, threshold={threshold}")

    total_constructed = 0
    total_ec = 0
    total_no_ec = 0
    construction_failures = 0

    for bins in list(combinations(range(n), 3))[:10]:
        bins_set = set(bins)
        ms = [2 if p in bins_set else 3 for p in range(n)]
        if not has_no_triple(ms, n):
            continue
        prod = 1
        for m in ms:
            prod *= m
        if prod >= threshold:
            continue

        ternary_pos = [p for p in range(n) if ms[p] == 3]

        for tp in ternary_pos[:2]:
            fc = list(ms)
            fc[tp] = 6
            cl = sum(fc)
            if (cl + n) % 2 != 0:
                continue

            for w in [1, -1]:
                c = solve_edge_counts(n, fc, winding=w)
                if c is None or any(cc < 0 for cc in c):
                    continue

                # Try to construct walk (multiple attempts with random tiebreaking)
                for attempt in range(50):
                    walk = construct_walk_from_edge_counts(n, fc, c, winding=w)
                    if walk is not None:
                        total_constructed += 1
                        W = total_displacement(walk, n)
                        if abs(W) == n:
                            if check_ec(walk, n, ms):
                                total_ec += 1
                            else:
                                total_no_ec += 1
                                print(f"  NO EC: ms={ms}, fc={fc}, winding={w}")
                                print(f"    walk={walk}")
                        break
                else:
                    construction_failures += 1

    print(f"  Constructed: {total_constructed}, EC: {total_ec}, no EC: {total_no_ec}")
    print(f"  Construction failures: {construction_failures}")


# The greedy construction is unlikely to find all walks. Let me use a random
# construction instead, trying many random orderings.

print(f"\n{'='*70}")
print("RANDOM WALK CONSTRUCTION")
print("=" * 70)

def construct_walk_random(n, fc, c_ccw, winding=1, seed=None):
    """Random walk construction."""
    if seed is not None:
        random.seed(seed)

    e_cw = [c_ccw[p] + winding for p in range(n)]
    e_ccw = c_ccw[:]

    remaining_fc = fc[:]
    remaining_cw = e_cw[:]
    remaining_ccw = e_ccw[:]

    CL = sum(fc)
    # Try each starting position
    for start in range(n):
        remaining_fc_t = fc[:]
        remaining_cw_t = e_cw[:]
        remaining_ccw_t = e_ccw[:]

        if remaining_fc_t[start] <= 0:
            continue
        walk = [start]
        remaining_fc_t[start] -= 1

        success = True
        for step in range(CL - 1):
            pos = walk[-1]
            nxt_cw = (pos + 1) % n
            nxt_ccw = (pos - 1) % n

            can_cw = remaining_cw_t[pos] > 0 and remaining_fc_t[nxt_cw] > 0
            can_ccw = remaining_ccw_t[(pos - 1) % n] > 0 and remaining_fc_t[nxt_ccw] > 0

            if not can_cw and not can_ccw:
                success = False
                break

            if can_cw and can_ccw:
                go_cw = random.random() < 0.5
            elif can_cw:
                go_cw = True
            else:
                go_cw = False

            if go_cw:
                remaining_cw_t[pos] -= 1
                walk.append(nxt_cw)
                remaining_fc_t[nxt_cw] -= 1
            else:
                remaining_ccw_t[(pos - 1) % n] -= 1
                walk.append(nxt_ccw)
                remaining_fc_t[nxt_ccw] -= 1

        if not success:
            continue

        diff = (walk[0] - walk[-1]) % n
        if diff != 1 and diff != n - 1:
            continue

        if any(r != 0 for r in remaining_fc_t):
            continue

        return walk

    return None


for n in [7, 9, 11]:
    threshold = 4 * (3 ** (n - 2))
    print(f"\nn={n}")

    total = 0
    ec_count = 0
    no_ec_count = 0

    for bins in list(combinations(range(n), 3))[:15]:
        bins_set = set(bins)
        ms = [2 if p in bins_set else 3 for p in range(n)]
        if not has_no_triple(ms, n):
            continue
        prod = 1
        for m in ms:
            prod *= m
        if prod >= threshold:
            continue

        ternary_pos = [p for p in range(n) if ms[p] == 3]

        for tp in ternary_pos[:3]:
            fc = list(ms)
            fc[tp] = 6
            cl = sum(fc)
            if (cl + n) % 2 != 0:
                continue

            for w in [1, -1]:
                c = solve_edge_counts(n, fc, winding=w)
                if c is None or any(cc < 0 for cc in c):
                    continue

                for trial in range(100):
                    walk = construct_walk_random(n, fc, c, winding=w, seed=42+trial)
                    if walk is not None:
                        W = total_displacement(walk, n)
                        if abs(W) == n:
                            total += 1
                            if check_ec(walk, n, ms):
                                ec_count += 1
                            else:
                                no_ec_count += 1
                                print(f"  NO EC! ms={ms}, fc={fc}, w={w}, walk={walk[:15]}...")
                        break

    print(f"  Total walks: {total}, EC: {ec_count}, no EC: {no_ec_count}")
