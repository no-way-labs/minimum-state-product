#!/usr/bin/env python3
"""
Structural classification for {2,3} rings with sandwiched ternary.

On a ring with n procs, state sizes in {2,3}:
- "sandwiched ternary" t: ms[t]=3, ms[t-1]=ms[t+1]=2.
- >=3 binary.
- sub-threshold product < 4*3^(n-2).

Question: when is there NO binary proc with all-binary neighbors?

Answer: only when binary and ternary STRICTLY ALTERNATE: 2,3,2,3,...
On a ring of size n, this requires n even and exactly n/2 binary + n/2 ternary.

With >=3 binary out of n: if n=5, we need >=3 binary out of 5.
Options: 3 binary + 2 ternary, 4 binary + 1 ternary, 5 binary + 0 ternary.

3 binary: possible patterns with sandwiched ternary:
  Must have ...2-3-2... somewhere. Remaining: 1 binary, 1 ternary.
  On ring of 5: e.g., 2,3,2,3,2 (alternating, n=5 is odd so not perfect alternation).

Let me enumerate all patterns.

For Case B to hold (no all-binary-context binary), every binary proc must have
at least one ternary neighbor. Since binary has two neighbors, each binary
has at least one neighbor that's ternary.

Claim: with >=3 binary and sandwiched ternary on {2,3} ring:
Case B holds iff the binary procs are NON-ADJACENT (no two consecutive binary).

Proof attempt:
If two binary procs are adjacent, say p, p+1 both binary:
- If p-1 is also binary: p has all-binary context.
- If p-1 is ternary and p+2 is also binary: p+1 has all-binary context.
- If p-1 is ternary and p+2 is ternary: p and p+1 are a "binary pair" surrounded by ternary.
  But then for p to have non-all-binary context, p-1 is ternary.
  For p+1 to have non-all-binary context, p+2 is ternary.
  But p and p+1 have each other as binary neighbor, so they ARE all-binary...
  Wait: p has neighbors p-1 (ternary) and p+1 (binary). Not all-binary.
  p+1 has neighbors p (binary) and p+2 (ternary). Not all-binary.

So: "no all-binary-context binary" means: no binary proc has BOTH neighbors binary.
This is equivalent to: no three consecutive binary procs.
Actually: it means every binary is adjacent to at least one ternary.

Let me just enumerate.
"""
from itertools import product as iproduct

for n in [5, 7, 9]:
    threshold = 4 * 3**(n-2)

    case_a = []  # has all-binary-context binary
    case_b = []  # no all-binary-context binary

    for ms_tuple in iproduct([2,3], repeat=n):
        ms = list(ms_tuple)
        prod = 1
        for m in ms:
            prod *= m
        if prod >= threshold:
            continue
        binary = [p for p in range(n) if ms[p] == 2]
        if len(binary) < 3:
            continue
        sandwiched = [p for p in range(n) if ms[p] == 3
                      and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]
        if not sandwiched:
            continue

        binary_allbinary = [p for p in binary
                           if ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]

        if binary_allbinary:
            case_a.append(ms)
        else:
            case_b.append(ms)

    # Normalize by rotation
    def canonical(ms, n):
        return min(tuple(ms[i:] + ms[:i]) for i in range(n))

    case_a_canon = set(canonical(ms, n) for ms in case_a)
    case_b_canon = set(canonical(ms, n) for ms in case_b)

    print(f"n={n}, threshold={threshold}:")
    print(f"  Case A (has all-binary-ctx): {len(case_a)} total, {len(case_a_canon)} canonical")
    print(f"  Case B (no all-binary-ctx): {len(case_b)} total, {len(case_b_canon)} canonical")

    if n <= 7:
        for ms_canon in sorted(case_b_canon):
            nb = sum(1 for m in ms_canon if m == 2)
            nt = sum(1 for m in ms_canon if m == 3)
            # Check: are any two binary adjacent?
            has_adj_binary = any(ms_canon[i] == 2 and ms_canon[(i+1)%n] == 2 for i in range(n))
            # Check: do binary positions form a non-adjacent set?
            print(f"    B: {ms_canon}, #bin={nb}, #ter={nt}, adj_binary={has_adj_binary}")

        for ms_canon in sorted(case_a_canon):
            nb = sum(1 for m in ms_canon if m == 2)
            nt = sum(1 for m in ms_canon if m == 3)
            has_adj_binary = any(ms_canon[i] == 2 and ms_canon[(i+1)%n] == 2 for i in range(n))
            has_3consec = any(ms_canon[i] == 2 and ms_canon[(i+1)%n] == 2 and ms_canon[(i+2)%n] == 2 for i in range(n))
            print(f"    A: {ms_canon}, #bin={nb}, #ter={nt}, adj_binary={has_adj_binary}, 3consec={has_3consec}")

print("\n" + "="*70)
print("KEY STRUCTURAL LEMMA: Case A iff >=3 consecutive binary")
print("="*70)
print("Case A: exists binary q with both neighbors binary.")
print("This means 3 consecutive binary processors exist.")
print("Case B: no such q exists, so no 3 consecutive binary.")
print()
print("Subthreshold + >=3 binary + {2,3} sizes:")
print("  n=5: exactly 3 binary forces at most 2 ternary.")
print("  With sandwiched ternary: ...2,3,2... leaves 1 binary, 1 remaining.")
print("  Cases:")
print("    [2,3,2,_,_] with 1 more binary, 1 more ternary")
print("    Remaining (_, _) from {(2,3), (3,2)}: gives [2,3,2,2,3] or [2,3,2,3,2]")
print("    [2,3,2,2,3]: has consecutive binary at pos 2,3. But pos 3 has nbrs 2(bin),4(ter).")
print("    No 3-consecutive -> Case B.")
print("    [2,3,2,3,2]: no consecutive binary at all -> Case B.")
print("  With 4 binary: [2,2,2,2,3] has 3-consecutive binary -> Case A.")
print()

# Verify: Case A happens iff 3 consecutive binary
print("Verification:")
for n in [5, 7]:
    threshold = 4 * 3**(n-2)
    all_match = True
    for ms_tuple in iproduct([2,3], repeat=n):
        ms = list(ms_tuple)
        prod = 1
        for m in ms:
            prod *= m
        if prod >= threshold:
            continue
        binary = [p for p in range(n) if ms[p] == 2]
        if len(binary) < 3:
            continue
        sandwiched = [p for p in range(n) if ms[p] == 3
                      and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]
        if not sandwiched:
            continue

        has_3consec = any(ms[i]==2 and ms[(i+1)%n]==2 and ms[(i+2)%n]==2 for i in range(n))
        has_allbinary = any(ms[p]==2 and ms[(p-1)%n]==2 and ms[(p+1)%n]==2 for p in range(n))

        if has_3consec != has_allbinary:
            print(f"  MISMATCH: ms={ms}")
            all_match = False

    if all_match:
        print(f"  n={n}: CONFIRMED — Case A iff >=3 consecutive binary")
