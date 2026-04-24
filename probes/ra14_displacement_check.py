#!/usr/bin/env python3
"""
ra14_displacement_check.py — Understand what "odd winding" means for non-+-1 wrap.

The total_displacement function sums signed differences for ALL steps including wrap.
For a +-1 ring walk, all steps contribute +-1.
But if the wrap step is not +-1, the displacement includes a larger contribution.

Question: In the Lean formalization, is the mover word a +-1 cyclic walk?
Or is it just a sequence of fire positions with arbitrary transitions?

In a good cycle for self-stabilizing token rings:
- At each step, one processor fires.
- The mover is the processor with the token.
- The token moves +-1 at each step.
- After CL steps, the token returns to its starting position.
- So the mover word IS a +-1 cyclic walk (every step +-1 mod n).

This means: the mover word satisfies:
  word[t+1] = (word[t] +- 1) mod n for all t, INCLUDING t = L-1 (wrap-around).

RA13's gen_words enforces this for t=0..L-2 but NOT for the wrap.
So RA13 was testing INVALID mover words (non-+-1 wrap).

The valid mover words are a SUBSET of what RA13 tested.
If RA13 found EC for ALL generated words, then EC holds for the valid subset too.
But it means the theorem may be provable by a SIMPLER argument.

Let me check: are there ANY valid (+-1 wrap) OW-NU words for odd n?
By the parity argument: CW - CCW = +-n, CW + CCW = CL.
For this to have integer solution: CL + n must be even.

CL = 2A + 3B where A = sum of fire count multipliers for binary, B for ternary.
CL + n even iff 2A + 3B + n even iff B + n even (since 2A is always even, 3B ≡ B mod 2).
For n odd: need B odd.

With 3 binary and (n-3) ternary:
Each ternary fires fc[p] = k_p * 3. Multiplier k_p >= 1.
B = sum of k_p over ternary procs.

For minimum fc: all k_p = 1. B = n-3. Since n is odd, n-3 is even. B EVEN. BAD.
For k = 2 for all: all k_p = 2. B = 2(n-3). EVEN. BAD.
For one ternary at k=2, rest at k=1: B = (n-4) + 2 = n-2. n odd => n-2 odd. GOOD!

So to get a valid OW-NU +-1 cyclic walk, we need at least one ternary at 2x
(or an odd number of ternaries at even multiplier).

BUT: does this actually produce valid words? Let me try harder to generate them.
"""
import time
from itertools import combinations


def gen_words_cyclic(n, fc_target, max_results=500, timeout_s=15):
    """Generate +-1 ring walk words WITH valid wrap-around."""
    target_cl = sum(fc_target)
    results = []
    t0 = time.time()

    def dfs(word, fc, start):
        if time.time() - t0 > timeout_s or len(results) >= max_results:
            return
        if len(word) == target_cl:
            if all(fc[p] == fc_target[p] for p in range(n)):
                # Check wrap-around
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


def canonicalize(word):
    L = len(word)
    best = word
    for i in range(L):
        rot = word[i:] + word[:i]
        if rot < best:
            best = rot
    return best


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


print("RA14: Valid +-1 Cyclic Walk OW-NU Words")
print("=" * 70)

# Test with mixed multipliers for n=5
for n in [5, 7]:
    threshold = 4 * (3 ** (n - 2))
    print(f"\nn={n}, threshold={threshold}")
    print("-" * 50)

    total_words = 0
    total_ec = 0
    total_no_ec = 0

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

        ternary_pos = [p for p in range(n) if ms[p] == 3]

        # Try different fc vectors with B odd
        fc_vectors = []

        # Method 1: one ternary at 2x, rest at 1x
        for tp in ternary_pos:
            fc = list(ms)
            fc[tp] = 6
            fc_vectors.append(fc)

        # Method 2: three ternaries at 2x (if n-3 >= 3)
        if len(ternary_pos) >= 3:
            for i in range(len(ternary_pos)):
                for j in range(i+1, len(ternary_pos)):
                    for k in range(j+1, len(ternary_pos)):
                        fc = list(ms)
                        fc[ternary_pos[i]] = 6
                        fc[ternary_pos[j]] = 6
                        fc[ternary_pos[k]] = 6
                        fc_vectors.append(fc)

        for fc in fc_vectors[:5]:  # Limit
            cl = sum(fc)
            if (cl + n) % 2 != 0:
                continue  # Parity doesn't allow winding

            words = gen_words_cyclic(n, fc, max_results=200, timeout_s=5)
            unique = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique:
                    unique[c] = w

            for w in unique.values():
                wl = list(w)
                W = total_displacement(wl, n)
                if abs(W) != n:
                    continue
                dirs = step_directions(wl, n)
                ns_d = [d for d in dirs if d != 0]
                if not ns_d or all(d == ns_d[0] for d in ns_d):
                    continue
                total_words += 1
                if check_structural_ec(wl, n, ms):
                    total_ec += 1
                else:
                    total_no_ec += 1
                    print(f"  NO EC: ms={ms}, fc={fc}, word={wl}")

    print(f"  Total valid-wrap OW-NU words: {total_words}")
    print(f"  With EC: {total_ec}")
    print(f"  Without EC: {total_no_ec}")


# Parity impossibility analysis
print(f"\n{'='*70}")
print("PARITY IMPOSSIBILITY THEOREM")
print("=" * 70)
print()
print("For n >= 5 ODD, with 3 non-consecutive binary and (n-3) ternary:")
print()
print("A +-1 cyclic walk of length CL has winding W = CW - CCW.")
print("|W| = n requires CL + n to be even (so CW = (CL+n)/2 is integer).")
print()
print("CL = sum(fc[p]) where fc[p] is a positive multiple of ms[p].")
print("fc[p] = k_p * ms[p], so for binary: 2*k_p, for ternary: 3*k_p.")
print("CL = 2*A + 3*B, where A = sum of k_p (binary), B = sum of k_p (ternary).")
print("CL + n ≡ B + n (mod 2).")
print()
print("For n ODD: CL + n even iff B odd.")
print()
print("B = sum of k_p over (n-3) ternary processors, each k_p >= 1.")
print("Whether B is odd or even depends on the specific fc choice.")
print()
print("Cases where B is EVEN (winding impossible):")
print("  - Minimum fc (all k_p = 1): B = n-3. n odd => n-3 even. IMPOSSIBLE.")
print("  - Uniform 2x fc (all k_p = 2): B = 2(n-3). EVEN. IMPOSSIBLE.")
print("  - Uniform k*ms for any k: B = k(n-3). Even iff k(n-3) even.")
print("    Since n-3 even: B always even. IMPOSSIBLE for any uniform multiplier!")
print()
print("Cases where B is ODD (winding possible in principle):")
print("  - One ternary at 2x, rest at 1x: B = n-2 (odd). POSSIBLE.")
print("  - Any odd number of ternaries at even multiplier.")
