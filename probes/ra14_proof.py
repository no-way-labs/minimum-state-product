#!/usr/bin/env python3
"""
ra14_proof.py — The mathematical PROOF of structural EC for odd-winding
non-uniform mover words with >= 3 non-consecutive binary at sub-threshold product.

=== PROOF STRATEGY ===

The proof has TWO parts:
  Part A (parity obstruction): For most fire count vectors fc, a valid +-1 cyclic
    walk with winding +-n is IMPOSSIBLE by parity.
  Part B (structural EC): For the remaining fc, EC is forced by pigeonhole
    on the boundary triple residues at a binary processor.

=== PART A: Parity Obstruction ===

THEOREM (Parity): Let ms be a state vector with 3 non-consecutive binary (ms[p]=2)
and (n-3) ternary (ms[p]=3) on a ring of size n >= 5.
Let fc[p] be a fire count vector with fc[p] = k_p * ms[p] for positive integers k_p.
Let CL = sum(fc[p]) = 2*A + 3*B where A = sum_{binary p} k_p, B = sum_{ternary p} k_p.

A valid +-1 cyclic walk of length CL has winding W = CW - CCW where
CW + CCW = CL and each of CW, CCW is a non-negative integer.
For |W| = n: CW = (CL + n)/2 or CW = (CL - n)/2.
This requires CL + n to be even, i.e., CL ≡ n (mod 2).

CL mod 2 = (2A + 3B) mod 2 = B mod 2.
n mod 2 = n mod 2.
So CL ≡ n (mod 2) iff B ≡ n (mod 2).

If B and n have different parity: winding +-n is IMPOSSIBLE.
The case with fc[p] = ms[p] has B = n-3 (same parity as n since n-3 ≡ n+1 ≡ n-1...
wait: n-3 mod 2 = (n+1) mod 2. So B = n-3 has OPPOSITE parity to n.
ACTUALLY: n-3 ≡ n-1 ≡ n+1 (mod 2). If n is odd: n-3 is even, n is odd. OPPOSITE.
If n is even: n-3 is odd, n is even. OPPOSITE.
So for minimum fc: B = n-3 always has opposite parity to n. WINDING IMPOSSIBLE.

=== PART B: When B ≡ n (mod 2) ===

When B has same parity as n: CL + n is even, winding MIGHT be possible.
This requires at least one k_p != 1 (i.e., non-minimum fire counts).

In this case: CL = 2A + 3B with B ≡ n (mod 2).
Minimum such CL: increment one ternary from 3 to 6, so CL = 3(n-1) + 3 = 3n.
(Or increment one binary from 2 to 4, but that changes A, not B.)

Actually: CL can only change in multiples of ms[p].
Incrementing one ternary by 3: B changes by 1. CL changes by 3. CL + n parity changes.
Incrementing one binary by 2: B unchanged. CL changes by 2. CL + n parity unchanged.

So to get B ≡ n (mod 2) from B_min = n-3 (opposite parity):
need to change B by an odd number. This means incrementing an odd number of
ternary processors. Minimum: increment one ternary k_p from 1 to 2 (fc from 3 to 6).
New CL = 3(n-1) + 3 = 3n.

For the Part B case: CL >= 3n.

At binary processor p (ms[p] = 2), with non-consecutive (both neighbors ternary):
Boundary triple residue space = ms[L] * ms[p] * ms[R] = 3 * 2 * 3 = 18.
fc[p] >= 2 (binary fires at least twice).
fc[p] is even (must be a multiple of 2).

Mover steps for p: fc[p] steps. Non-mover steps: CL - fc[p] steps.
For EC: need some mover step and non-mover step to have the same residue triple.

Pigeonhole: if fc[p] + (CL - fc[p]) = CL > 18: some two steps share a residue triple.
But they could both be movers or both be non-movers.

Better: mover residues form a set of size <= fc[p].
Non-mover residues form a set of size <= CL - fc[p].
If these two sets together exceed the space: overlap guaranteed.
|mover set| + |non-mover set| > 18 implies overlap.

But |mover set| <= fc[p] and |non-mover set| <= CL - fc[p].
So |mover set| + |non-mover set| <= CL.
If CL > 18: we need that |mover set| + |non-mover set| > 18.

Actually this is NOT guaranteed by CL > 18 alone, because the sets could
overlap within themselves (reducing distinct elements).

But: CL > 18 means the TOTAL number of steps exceeds the space size.
By pigeonhole, at least ceil(CL/18) ≈ 2 steps share the same residue triple.
If they're a mover-nonmover pair: EC.
If not: they're both movers or both non-movers.

The question: can ALL same-residue pairs be same-type (all mover-mover or all non-non)?

For CL = 3n with n >= 5: CL >= 15. With 18 slots and 15 elements: at most 15 distinct.
By pigeonhole: if CL > 18, at least one collision.
CL = 3n > 18 iff n > 6, i.e., n >= 7.
For n = 5: CL = 15 < 18. NOT ENOUGH for pigeonhole on binary proc.
For n = 7: CL = 21 > 18. Pigeonhole gives collision.

But for n = 5: need a different argument.

Hmm, but wait: for n = 5 with the minimum-parity-fix fc:
CL = 15. fc[p] = 2 for binary p. Non-mover steps = 13.
Mover steps contribute 2 residue triples in the 18-element space.
Non-mover steps contribute at most 13 residue triples.
Total: 2 + 13 = 15 > 18? NO, 15 < 18.

So pigeonhole doesn't work for n = 5.

BUT: at n = 5 with 3 non-consecutive binary: is there actually a valid +-1 cyclic
walk with winding +-5 and CL = 15 and isolated binary firings?

Let me check computationally.
"""
import time
from itertools import combinations, product as iproduct


def gen_words_cyclic(n, fc_target, max_results=1000, timeout_s=30):
    """Generate +-1 ring walk words WITH valid wrap-around."""
    target_cl = sum(fc_target)
    results = []
    t0 = time.time()

    def dfs(word, fc, start):
        if time.time() - t0 > timeout_s or len(results) >= max_results:
            return
        if len(word) == target_cl:
            if all(fc[p] == fc_target[p] for p in range(n)):
                diff = (start - word[-1]) % n
                if diff == 1 or diff == n - 1:
                    results.append(tuple(word))
            return
        remaining = target_cl - len(word)
        needed = sum(max(0, fc_target[p] - fc[p]) for p in range(n))
        if needed > remaining:
            return
        last = word[-1]
        for nxt in [(last + 1) % n, (last - 1) % n]:
            if fc[nxt] < fc_target[nxt]:
                fc[nxt] += 1
                word.append(nxt)
                dfs(word, fc, start)
                word.pop()
                fc[nxt] -= 1

    for start in range(n):
        if time.time() - t0 > timeout_s or len(results) >= max_results:
            break
        fc = [0] * n
        fc[start] = 1
        if fc[start] <= fc_target[start]:
            dfs([start], fc, start)
    return results


def total_displacement(word, n):
    W = 0
    L = len(word)
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 0:
            pass
        elif diff <= n // 2:
            W += diff
        else:
            W -= (n - diff)
    return W


def step_directions(word, n):
    L = len(word)
    dirs = []
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 0:
            dirs.append(0)
        elif diff == 1:
            dirs.append(1)
        elif diff == n - 1:
            dirs.append(-1)
        else:
            dirs.append(diff if diff <= n // 2 else diff - n)
    return dirs


def has_no_triple(ms, n):
    for i in range(n):
        if ms[i] == 2 and ms[(i+1) % n] == 2 and ms[(i+2) % n] == 2:
            return False
    return True


def has_isolated_binary(word, n, ms):
    """Check that all binary processors have isolated firings."""
    L = len(word)
    for p in range(n):
        if ms[p] != 2:
            continue
        for t in range(L):
            if word[t] == p and word[(t+1) % L] == p:
                return False
    return True


def check_structural_ec(word, n, ms):
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


def canonicalize(word):
    L = len(word)
    best = word
    for i in range(L):
        rot = word[i:] + word[:i]
        if rot < best:
            best = rot
    return best


print("RA14: Proof — Structural EC for OW-NU Non-Consecutive Binary")
print("=" * 70)

# Part A verification: parity obstruction for uniform multipliers
print("\nPART A: Parity Obstruction")
print("-" * 50)

for n in [5, 7, 9, 11, 13]:
    cl_min = 3 * (n - 1)
    parity_ok = (cl_min + n) % 2 == 0
    print(f"  n={n}: CL_min={cl_min}, CL+n={cl_min+n}, winding_possible={parity_ok}")

print("\n  For uniform k*ms: CL = k*3(n-1). CL+n = 3k(n-1)+n.")
for n in [5, 7, 9]:
    for k in range(1, 5):
        cl = k * 3 * (n - 1)
        parity_ok = (cl + n) % 2 == 0
        print(f"    n={n}, k={k}: CL={cl}, CL+n={cl+n}, winding_possible={parity_ok}")

# Part B verification: search for valid OW-NU words with non-uniform multipliers
print(f"\n{'='*70}")
print("PART B: Non-uniform multiplier search")
print("-" * 50)

for n in [5, 7]:
    threshold = 4 * (3 ** (n - 2))
    print(f"\nn={n}, threshold={threshold}")

    for bins in list(combinations(range(n), 3))[:5]:
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

        # Try incrementing one ternary (fc from 3 to 6)
        for tp in ternary_pos[:2]:
            fc = list(ms)
            fc[tp] = 6
            cl = sum(fc)
            if (cl + n) % 2 != 0:
                continue

            words = gen_words_cyclic(n, fc, max_results=200, timeout_s=10)
            unique = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique:
                    unique[c] = w

            ow_nu = 0
            ow_nu_iso = 0
            ow_nu_iso_ec = 0
            for w in unique.values():
                wl = list(w)
                W = total_displacement(wl, n)
                if abs(W) != n:
                    continue
                dirs = step_directions(wl, n)
                ns_d = [d for d in dirs if d != 0]
                if not ns_d or all(d == ns_d[0] for d in ns_d):
                    continue
                ow_nu += 1
                if has_isolated_binary(wl, n, ms):
                    ow_nu_iso += 1
                    if check_structural_ec(wl, n, ms):
                        ow_nu_iso_ec += 1
                    else:
                        print(f"    NO EC: ms={ms}, fc={fc}, word={wl}")

            if ow_nu > 0 or len(words) > 0:
                print(f"  ms={ms}, fc={fc}, CL={cl}: {len(words)} walks, {ow_nu} OW-NU, "
                      f"{ow_nu_iso} isolated, {ow_nu_iso_ec} with EC")

    # Try incrementing one binary (fc from 2 to 4) — doesn't change parity
    # Try incrementing 3 ternaries
    for bins in list(combinations(range(n), 3))[:2]:
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
        if len(ternary_pos) >= 3:
            # Increment 3 ternaries (odd number -> changes B parity)
            fc = list(ms)
            for i in range(3):
                fc[ternary_pos[i]] = 6
            cl = sum(fc)
            if (cl + n) % 2 == 0:
                words = gen_words_cyclic(n, fc, max_results=100, timeout_s=10)
                ow_nu = 0
                for w in words:
                    wl = list(w)
                    W = total_displacement(wl, n)
                    if abs(W) != n:
                        continue
                    dirs = step_directions(wl, n)
                    ns_d = [d for d in dirs if d != 0]
                    if not ns_d or all(d == ns_d[0] for d in ns_d):
                        continue
                    ow_nu += 1
                print(f"  ms={ms}, fc={fc}, CL={cl}: {len(words)} walks, {ow_nu} OW-NU "
                      f"(3 ternaries doubled)")

print(f"\n{'='*70}")
print("PROOF STRUCTURE SUMMARY")
print("=" * 70)
print("""
THEOREM: Every odd-winding non-uniform good cycle with >= 3 non-consecutive
binary at sub-threshold product has structural entry conflict.

PROOF:
  Let gc be such a good cycle with fire count vector fc.
  The mover word is a +-1 cyclic walk of length CL = sum(fc[p]).
  fc[p] is a positive multiple of ms[p] for each p.

  CL = 2A + 3B where A = sum of binary multipliers, B = sum of ternary multipliers.

  CASE 1: B and n have different parity.
    Then CL + n is odd, so CL and n have different parity.
    A +-1 cyclic walk of length CL has winding W = CW - CCW where CW + CCW = CL.
    |W| = n requires CW = (CL +- n)/2, which requires CL + n even. Contradiction.
    So winding +-n is impossible. Case vacuously true.

  CASE 2: B and n have same parity.
    Then at least one ternary multiplier k_p differs from 1 (otherwise B = n-3
    which has opposite parity to n for any n >= 5).
    So CL > 3(n-1), specifically CL >= 3(n-1) + 3 = 3n.

    For n >= 7: CL >= 21 > 18.
    At binary p with non-consecutive binary: residue space = 3*2*3 = 18.
    fc[p] >= 2 mover steps. CL - fc[p] >= CL - fc[p] non-mover steps.
    Total steps CL > 18. By pigeonhole on the residue space,
    at least two steps share the same residue triple.

    CLAIM: For CL > 18 with isolated binary firings and odd winding,
    there must be a mover-nonmover collision (not just mover-mover or non-non).

    [This claim needs verification/proof...]

    For n = 5: CL = 15. Pigeonhole on 18-space doesn't directly apply.
    But... do valid +-1 cyclic OW-NU walks with isolated binary firings
    even EXIST at n=5 with non-minimum fc?

    [Need to check: possibly EMPTY for n=5 too...]
""")
