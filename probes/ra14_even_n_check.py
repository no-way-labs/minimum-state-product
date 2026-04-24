#!/usr/bin/env python3
"""
ra14_even_n_check.py — Check even n (n=6, 8) for valid-wrap OW-NU words.

For n EVEN: CL + n even iff B even.
B = sum of k_p over ternary procs.
Minimum fc: B = n-3 (odd since n even). So CL + n is ODD -> impossible!
Wait: n even, n-3 odd. B = n-3 odd. CL + n ≡ B + n ≡ odd + even = odd. IMPOSSIBLE.
2x fc: B = 2(n-3) even. CL + n even. POSSIBLE!

Actually wait, let me recheck for n=6:
CL = 2*3 + 3*3 = 6 + 9 = 15 (min fc).
CL + n = 15 + 6 = 21. Odd. IMPOSSIBLE.
2x: CL = 30. CL + n = 36. Even. POSSIBLE.

For n=8:
CL = 2*3 + 3*5 = 6 + 15 = 21. CL + n = 29. Odd. IMPOSSIBLE.
2x: CL = 42. CL + n = 50. Even. POSSIBLE.

So: for ANY n (odd or even), minimum fc gives odd CL+n. IMPOSSIBLE.
But higher multiples can give even CL+n.

Actually: CL_min = 2*3 + 3*(n-3) = 6 + 3n - 9 = 3n - 3 = 3(n-1).
CL_min + n = 3(n-1) + n = 4n - 3. This is ALWAYS ODD (4n even, -3 odd).

THEOREM: For ANY n >= 5, with 3 non-consecutive binary and minimum fire counts:
CL + n = 4n - 3 is always odd, so winding +-n is impossible.

For 2x fc: CL = 6(n-1). CL + n = 6n - 6 + n = 7n - 6.
n=5: 29. Odd. n=6: 36. Even. n=7: 43. Odd. n=8: 50. Even.
So 2x works for n even but not n odd.

For mixed: need CL + n even. CL = 3(n-1) + extra.
Need extra to make CL + n even, i.e., extra odd.
Extra must be a sum of multiples of ms[p] minus ms[p] for modified procs.
Binary: extra = 2*(k-1) for binary at k*2. Always even.
Ternary: extra = 3*(k-1) for ternary at k*3. Always a multiple of 3.

So extra = sum of even terms (binary mods) + sum of multiples of 3 (ternary mods).
Extra = 2*E + 3*T where E, T >= 0.
Need extra odd: 2*E + 3*T odd => 3*T odd => T odd.
So: need an ODD number of ternary processors with increased multiplier.

With n-3 ternary procs:
- For n odd: n-3 even. An odd subset exists (e.g., pick 1).
- For n even: n-3 odd. An odd subset exists (e.g., pick 1).

So for ANY n, it's possible to choose fc so that CL + n is even.
But the question is: do valid-wrap OW-NU words exist with these fc?

Actually, let me reconsider: maybe the correct approach is to prove that
for ALL valid fc (multiples of ms), there are no valid-wrap OW-NU words
with structural EC, OR that all valid-wrap OW-NU words have structural EC.

But if min fc doesn't even have valid-wrap OW-NU words (parity obstruction),
and we need to check higher fc... the word generation is too slow.

Let me try a TARGETED search for n=6 with 2x fc (which has correct parity).
"""
import time
from itertools import combinations


def gen_words_cyclic(n, fc_target, max_results=500, timeout_s=15):
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


print("RA14: Parity Obstruction — Universal Analysis")
print("=" * 70)

# Check: for EVERY valid fc (fc[p] multiple of ms[p]), is CL + n odd?
# CL = sum(fc[p]) = sum(k_p * ms[p]) = 2*A + 3*B.
# CL + n = 2A + 3B + n.
# Mod 2: CL + n ≡ B + n (mod 2).
# Need CL + n even: B ≡ n (mod 2).

# B = sum of k_p over ternary procs.
# Number of ternary procs = n - 3.

# Case n odd (n >= 5, 7, 9, 11, ...):
#   Need B even. B = sum of k_p over (n-3) terms, n-3 even.
#   Minimum B = n-3 (even). YES, B CAN be even.
#   But: is B always even? No: k_p = 1 for all gives B = n-3 (even), but k_p = 2 for one
#   gives B = n-2 (odd).
#   So for n odd: SOME fc choices give B even (winding impossible),
#   others give B odd (winding possible in principle).

# Case n even (n >= 6, 8, 10, ...):
#   Need B odd. B = sum of k_p over (n-3) terms, n-3 odd.
#   Minimum B = n-3 (odd). YES, minimum fc has B odd!
#   So for n even: minimum fc DOES allow winding in principle.

# WAIT! For n even, minimum fc has CL + n even. So winding IS possible.
# Let me check this for n=6.

n = 6
ms_list = []
for bins in combinations(range(n), 3):
    bins_set = set(bins)
    ms = [2 if p in bins_set else 3 for p in range(n)]
    if not has_no_triple(ms, n):
        continue
    threshold = 4 * (3 ** (n - 2))
    prod = 1
    for m in ms:
        prod *= m
    if prod >= threshold:
        continue
    ms_list.append(ms)

print(f"\nn=6: {len(ms_list)} valid multiset placements")
for ms in ms_list[:3]:
    fc = list(ms)
    cl = sum(fc)
    print(f"  ms={ms}, CL={cl}, CL+n={cl+n}, even: {(cl+n)%2==0}")

    if (cl + n) % 2 == 0:
        print(f"  Parity allows winding! Searching for valid-wrap OW-NU words...")
        words = gen_words_cyclic(n, fc, max_results=200, timeout_s=10)
        ow_nu = 0
        ow_nu_ec = 0
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
            if check_structural_ec(wl, n, ms):
                ow_nu_ec += 1
            else:
                print(f"    NO EC: word={wl[:15]}...")
        print(f"  Found: {len(words)} total, {ow_nu} OW-NU, {ow_nu_ec} with EC")

# Also check n=8
n = 8
ms_list = []
for bins in combinations(range(n), 3):
    bins_set = set(bins)
    ms = [2 if p in bins_set else 3 for p in range(n)]
    if not has_no_triple(ms, n):
        continue
    threshold = 4 * (3 ** (n - 2))
    prod = 1
    for m in ms:
        prod *= m
    if prod >= threshold:
        continue
    ms_list.append(ms)

print(f"\nn=8: {len(ms_list)} valid multiset placements")
for ms in ms_list[:2]:
    fc = list(ms)
    cl = sum(fc)
    print(f"  ms={ms}, CL={cl}, CL+n={cl+n}, even: {(cl+n)%2==0}")

    if (cl + n) % 2 == 0:
        print(f"  Parity allows winding! Searching...")
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
        print(f"  Found: {len(words)} total, {ow_nu} OW-NU")

# KEY ANALYSIS: For n ODD (which is the case for all odd-winding cycles):
# winding = n means the token wraps around the ring once.
# This requires CL ≡ n (mod 2). But CL = 3(n-1) for min fc.
# 3(n-1) mod 2 = (n-1) mod 2 = (n+1) mod 2.
# n mod 2 = n mod 2.
# These are DIFFERENT. So min fc NEVER allows winding n for ANY n.

# CRITICAL QUESTION: Can n be even in the theorem?
# The theorem says "n >= 9" for M_n = 4*3^(n-2).
# n can be 9, 10, 11, ...
# For n even: min fc CAN have odd winding (CL + n is even when n-3 is odd).
# Wait, n=10: CL_min = 3*9 = 27. CL+n = 37. ODD. So min fc doesn't work for n=10 either!
# Wait: 3(n-1) + n = 4n-3. For n=10: 37. ODD.
# For ANY n: 4n-3 is odd. So min fc NEVER allows winding +-n.

# But higher fc CAN. So we CANNOT use a pure parity argument for all fc.

print(f"\n{'='*70}")
print("DEFINITIVE PARITY ANALYSIS")
print("=" * 70)
print()
print("4n - 3 is ALWAYS ODD for any integer n.")
print("So minimum fire counts NEVER allow odd winding.")
print("But non-minimum fire counts CAN allow odd winding.")
print()
print("The question is: for fc that DO allow odd winding,")
print("do valid-wrap OW-NU words exist? And if so, do they all have EC?")
print()

# For the Lean proof: we need to handle ALL valid fc vectors.
# The parity argument handles MOST fc (those with B having wrong parity).
# The remaining fc (B with correct parity) need structural EC.

# Actually: the Lean theorem probably doesn't distinguish by fc.
# It says: for any mover word (any valid +-1 cyclic walk with winding +-n,
# non-uniform, with fire counts multiples of ms): structural EC exists.

# The parity observation shows: many (most?) fc choices are vacuously impossible.
# But some fc choices DO allow the parity, and for those we need actual EC proof.

# The 11,555 words RA13 tested include invalid-wrap words.
# Those are not real mover words! The verification was on a SUPERSET.
# EC for the superset => EC for the (smaller) valid subset.
# So RA13's result is correct but may be proving a STRONGER statement.
