#!/usr/bin/env python3
"""
ra14_parity_proof.py — Check if the non-existence of valid-wrap OW-NU words
is a parity argument.

For a +-1 ring walk of length CL on a ring of size n:
- Each step is +1 or -1.
- Net displacement = CW - CCW, where CW + CCW = CL.
- Odd winding: |CW - CCW| = n.
- So CW - CCW = +-n.
- CW = (CL + n)/2 or (CL - n)/2.
- For this to be integer: CL and n must have SAME PARITY.

For non-consecutive 3-binary with fc = ms:
- CL = 3*2 + (n-3)*3 = 6 + 3n - 9 = 3n - 3.
- CL = 3(n-1).
- CL mod 2 = (3(n-1)) mod 2 = (n-1) mod 2 = (n+1) mod 2.
- n mod 2 = n mod 2.
- Same parity iff (n+1) mod 2 = n mod 2, i.e., 1 = 0. NEVER!

So CL = 3(n-1) and n ALWAYS have DIFFERENT parity!
This means: for a genuine +-1 cyclic walk of length 3(n-1),
the net displacement CAN NEVER equal +-n.

WAIT. This is a +-1 walk on a RING (cyclic), not on Z.
On a ring of size n, the walk is modular. The "displacement" is
sum of signed steps, which CAN be any integer (not just mod n).
For the walk to be cyclic (return to start): sum of signed steps = 0 mod n.
So: CW - CCW ≡ 0 mod n.

But OW says |CW - CCW| = n, so CW - CCW = +-n.
And CW + CCW = CL = 3(n-1).
=> CW = (3(n-1) +- n) / 2.
For this to be a non-negative integer:
- 3(n-1) + n = 4n - 3 must be even: 4n is even, 3 is odd => 4n-3 is odd. NOT EVEN.
- 3(n-1) - n = 2n - 3 must be even: 2n is even, 3 is odd => 2n-3 is odd. NOT EVEN.

So (3(n-1) +- n) / 2 is NEVER an integer!
This means: a +-1 cyclic walk of length 3(n-1) can NEVER have winding +-n.

Therefore: WITH MINIMUM FIRE COUNTS (fc = ms), odd-winding mover words
with valid +-1 wrap-around DO NOT EXIST for non-consecutive 3-binary.

But what about higher multiples? fc = k * ms for k >= 2?
CL = k * sum(ms) = k * 3(n-1).
CW - CCW = +-n.
CW = (k*3(n-1) + n) / 2.
Need k*3(n-1) + n even, i.e., 3k(n-1) + n even.
3k(n-1) has same parity as k(n-1).
n has parity n.
Sum: k(n-1) + n = kn - k + n = n(k+1) - k.
For n odd: n(k+1) is odd*(k+1). k even => k+1 odd => n(k+1) odd, -k even => odd. Need even: NO.
k odd => k+1 even => n(k+1) even, -k odd => even-odd = odd. Need even: NO.
Wait that's not right. Let me be more careful.

n(k+1) - k.
n odd, k even: n(k+1) = odd*odd = odd. odd - even = odd. NOT EVEN.
n odd, k odd: n(k+1) = odd*even = even. even - odd = odd. NOT EVEN.

So for n ODD: 3k(n-1) + n is ALWAYS ODD, regardless of k.
This means: for ANY fire count multiple k, there is NO valid +-1 cyclic walk
with winding +-n when n is odd.

WAIT. But n is always odd (n >= 5 odd).
Actually n can be even too. Let me check n=6.
n=6: 3k(n-1) + n = 3k*5 + 6 = 15k + 6.
k=1: 21. Odd. No.
k=2: 36. Even. YES!

So for n even, k=2 works. But our problem has n >= 5 ODD.

For n odd: 3k(n-1) + n = 3k*(even) + odd = even + odd = ODD. Always odd!
So (CL + n)/2 is never an integer when n is odd.

THEOREM: For n >= 5 ODD, any fire count vector fc with fc[p] = k * ms[p]
where ms has 3 non-consecutive binary and (n-3) ternary:
CL = k * 3(n-1) and winding = +-n is IMPOSSIBLE for a +-1 cyclic walk.

But wait: fc doesn't have to be a uniform multiple of ms!
The fire count could be fc[p] = ms[p] * k_p for different k_p per processor.
The key constraint is: fc[p] ≡ 0 mod ms[p] for all p (so the state returns).
The minimum is fc[p] = ms[p].

General: fc[p] = a_p * ms[p] for positive integers a_p.
CL = sum(a_p * ms[p]).
For binary p: a_p * 2. For ternary p: a_p * 3.
CL = 2 * sum_binary(a_p) + 3 * sum_ternary(a_p).

Need CL + n even for winding +-n.
CL = 2A + 3B where A = sum of a_p over binary procs, B = sum over ternary.
With 3 binary: A >= 3. With (n-3) ternary: B >= n-3.
CL = 2A + 3B.
CL + n even iff 2A + 3B + n even iff 3B + n even iff B + n even (since 3B ≡ B mod 2).
So: CL + n even iff B has SAME PARITY as n.

For n odd: need B odd. B = sum of a_p over (n-3) ternary procs.
n-3 is even (since n is odd). So there are an EVEN number of ternary procs.
Can B be odd? YES: e.g., one ternary has a_p=2 (odd fire count factor... wait, a_p is any positive integer).

Actually a_p can be any positive integer >= 1.
B = a_{t1} + a_{t2} + ... + a_{t_{n-3}}.
With n-3 terms (even number of terms), each >= 1.
Minimum B = n-3 (even). B = n-3 is EVEN.
B = n-3+1 = n-2 is ODD (by incrementing one a_p).

So: for fc with sum_ternary(a_p) = n-2 (odd): CL + n is even.
This means: winding +-n IS possible for non-minimum fire counts.

Hmm, so the parity argument only works for minimum fc, not general fc.
But RA13 checked fc = 2*ms too and found structural EC for those as well.

Let me verify: does fc = 2*ms have valid-wrap OW-NU words?
"""
import time
from itertools import combinations


def gen_words(n, fc_target, max_results=500, timeout_s=15):
    target_cl = sum(fc_target)
    results = []
    t0 = time.time()
    def dfs(word, fc):
        if time.time() - t0 > timeout_s or len(results) >= max_results:
            return
        if len(word) == target_cl:
            if all(fc[p] == fc_target[p] for p in range(n)):
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
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1
    for start in range(n):
        if time.time() - t0 > timeout_s or len(results) >= max_results:
            break
        fc = [0] * n
        fc[start] = 1
        if fc[start] <= fc_target[start]:
            dfs([start], fc)
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


print("PARITY ANALYSIS: CL + n mod 2")
print("=" * 70)

for n in [5, 7, 9]:
    print(f"\nn={n}")

    # For minimum fc = ms:
    cl_min = 3*2 + (n-3)*3
    print(f"  Minimum CL = {cl_min}, CL+n = {cl_min+n}, even: {(cl_min+n)%2==0}")

    # For fc = 2*ms:
    cl_2x = 2 * cl_min
    print(f"  2x CL = {cl_2x}, CL+n = {cl_2x+n}, even: {(cl_2x+n)%2==0}")

    # For fc = ms with one ternary incremented by 1:
    # fc[t1] = ms[t1]+1 = 4, others same.
    # CL = cl_min + 1 = 3n-2.
    # Wait, the increment must keep fc[p] as a multiple of ms[p]? NO!
    # Actually: for a good cycle, fc[p] just needs to be a positive integer
    # such that the state returns: after fc[p] fires, value returns to original.
    # For ternary: need fc[p] mod 3 = 0. For binary: need fc[p] mod 2 = 0.
    # So fc[p] must be a multiple of ms[p].

    # Minimum non-minimum fc with different parity:
    # Increment one ternary from 3 to 6: CL increases by 3.
    cl_inc = cl_min + 3  # 3n-3+3 = 3n
    print(f"  Incremented CL = {cl_inc}, CL+n = {cl_inc+n}, even: {(cl_inc+n)%2==0}")

    # Another: increment one binary from 2 to 4: CL increases by 2.
    cl_inc2 = cl_min + 2  # 3n-1
    print(f"  Binary increment CL = {cl_inc2}, CL+n = {cl_inc2+n}, even: {(cl_inc2+n)%2==0}")

print()
print("KEY INSIGHT:")
print("For n odd, minimum CL = 3(n-1) is even, n is odd.")
print("CL + n is odd -> winding +-n impossible with all +-1 steps.")
print("Any fc with CL such that CL + n is odd -> impossible.")
print()
print("CL = sum(k_p * ms[p]) = 2*sum_B(k_p) + 3*sum_T(k_p)")
print("For n odd: CL + n odd iff (2*A + 3*B + n) odd iff (B + n) odd iff B even")
print("Since n is odd: B even <=> CL+n odd <=> winding impossible.")
print("B = sum of k_p over ternary procs. Min B = n-3 (even since n odd).")
print("So minimum fc always has B even -> winding always impossible!")
print("Incrementing any ternary by 3 keeps B the same (mod 2) -> still impossible.")
print("Incrementing binary by 2 doesn't change B -> still impossible.")
print()
print("To get B odd: need to change some ternary fc from 3*k to 3*(k+1) where")
print("k was even and k+1 is odd, etc. Or add 3 to an odd number of ternary procs.")
print()

# Actually let's think about this more carefully.
# fc[p] must be a multiple of ms[p].
# For ternary: fc[p] = 3*k_p, so k_p = fc[p]/3.
# B = sum of k_p over ternary procs.
# B even iff an even number of ternary procs have odd k_p.
# With minimum fc: all k_p = 1 (odd). B = n-3 (even since n odd).
# With 2x fc: all k_p = 2 (even). B = 0 (even).
# With fc where one ternary has k_p = 2 and rest have k_p = 1:
#   B = 1*(n-4) + 2 = n-2. n odd => n-2 odd. B is ODD!
#   So CL + n is EVEN -> winding +-n IS possible!

print("CORRECTION: With mixed multipliers (one ternary at 6, rest at 3):")
for n in [5, 7]:
    n_ternary = n - 3
    cl = 3*2 + (n_ternary-1)*3 + 6  # one ternary at 6
    print(f"  n={n}: CL = {cl}, CL+n = {cl+n}, even: {(cl+n)%2==0}")

    # This gives B = (n-4)*1 + 2 = n-2. For n=5: B=3 (odd). CL+n=12+3+5=20. Even!
    # So winding IS possible. Are there actual words?

    ms = [0]*n
    # Place 3 binary non-consecutively
    if n == 5:
        binary_pos = [0, 2, 4]
    elif n == 7:
        binary_pos = [0, 2, 4]
    else:
        binary_pos = list(range(0, 6, 2))[:3]
    for i in range(n):
        ms[i] = 2 if i in binary_pos else 3

    # fc: all ms except one ternary at 2x
    fc = list(ms)
    for i in range(n):
        if ms[i] == 3 and fc[i] == 3:
            fc[i] = 6
            break

    print(f"  ms={ms}, fc={fc}, CL={sum(fc)}")

    words = gen_words(n, fc, max_results=100, timeout_s=10)
    ow_nu = 0
    ow_nu_valid_wrap = 0
    for w in words:
        wl = list(w)
        diff = (wl[0] - wl[-1]) % n
        valid_wrap = (diff == 1 or diff == n-1)
        W = total_displacement(wl, n)
        if abs(W) != n:
            continue
        dirs = step_directions(wl, n)
        ns_d = [d for d in dirs if d != 0]
        if not ns_d or all(d == ns_d[0] for d in ns_d):
            continue
        ow_nu += 1
        if valid_wrap:
            ow_nu_valid_wrap += 1

    print(f"  Generated: {len(words)}, OW-NU: {ow_nu}, with valid wrap: {ow_nu_valid_wrap}")
