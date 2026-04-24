#!/usr/bin/env python3
"""
TMidVal stutter/pigeonhole investigation for CUP-2 system.

Questions:
1. TMid(L, S, S) behavior — classify each (L,S) pair
2. Run-of-3 pigeonhole for ternary interior
3. TP-preserving copy-right steps at interior positions (n=9)
"""

from itertools import product as iprod

# ── TMidVal table from LeanMn/Tables.lean ──────────────────────────
# TMidVal(L, S, R) for L, S, R in {0,1,2}

TMID = {}
_raw = [
    (0,0,0, 0), (0,0,1, 0), (0,0,2, 0),
    (0,1,0, 0), (0,1,1, 1), (0,1,2, 0),
    (0,2,0, 0), (0,2,1, 2), (0,2,2, 0),
    (1,0,0, 1), (1,0,1, 1), (1,0,2, 1),
    (1,1,0, 1), (1,1,1, 1), (1,1,2, 2),
    (1,2,0, 0), (1,2,1, 1), (1,2,2, 2),
    (2,0,0, 0), (2,0,1, 0), (2,0,2, 2),
    (2,1,0, 1), (2,1,1, 0), (2,1,2, 2),  # (2,1,1)=0 is the liveness fix
    (2,2,0, 0), (2,2,1, 2), (2,2,2, 2),
]
for L, S, R, out in _raw:
    TMID[(L, S, R)] = out

# All 5 tables for full CUP-2 system
TBOT = {}
_raw_bot = [
    (0,0,0,1),(0,0,1,1),(0,0,2,0),
    (0,1,0,1),(0,1,1,1),(0,1,2,1),
    (1,0,0,0),(1,0,1,1),(1,0,2,0),
    (1,1,0,0),(1,1,1,1),(1,1,2,0),
]
for L,S,R,out in _raw_bot:
    TBOT[(L,S,R)] = out

TLOW = {}
_raw_low = [
    (0,0,0,0),(0,0,1,0),(0,0,2,0),
    (0,1,0,0),(0,1,1,1),(0,1,2,0),
    (0,2,0,0),(0,2,1,2),(0,2,2,0),
    (1,0,0,1),(1,0,1,1),(1,0,2,1),
    (1,1,0,1),(1,1,1,1),(1,1,2,2),
    (1,2,0,0),(1,2,1,1),(1,2,2,2),
]
for L,S,R,out in _raw_low:
    TLOW[(L,S,R)] = out

THIGH = {}
_raw_high = [
    (0,0,0,0),(0,0,1,0),
    (0,1,0,0),(0,1,1,0),
    (0,2,0,0),(0,2,1,0),
    (1,0,0,1),(1,0,1,1),
    (1,1,0,1),(1,1,1,2),
    (1,2,0,0),(1,2,1,2),
    (2,0,0,0),(2,0,1,2),
    (2,1,0,0),(2,1,1,2),
    (2,2,0,2),(2,2,1,2),
]
for L,S,R,out in _raw_high:
    THIGH[(L,S,R)] = out

TTOP = {}
_raw_top = [
    (0,0,0,0),(0,0,1,0),
    (0,1,0,0),(0,1,1,0),
    (1,0,0,0),(1,0,1,1),
    (1,1,0,1),(1,1,1,1),
    (2,0,0,1),(2,0,1,1),
    (2,1,0,1),(2,1,1,1),
]
for L,S,R,out in _raw_top:
    TTOP[(L,S,R)] = out


def cup2_table(n, i):
    """Return the transition table for position i in an n-ring."""
    if i == 0:
        return TBOT
    elif i == 1:
        return TLOW
    elif i == n - 1:
        return TTOP
    elif i == n - 2:
        return THIGH
    else:
        return TMID

def cup2_m(n, i):
    """State count at position i."""
    if i == 0 or i == n - 1:
        return 2
    return 3

def cup2_out(n, i, L, S, R):
    """Compute output of CUP-2 transition at position i."""
    tbl = cup2_table(n, i)
    return tbl.get((L, S, R), 0)


# ════════════════════════════════════════════════════════════════════
# QUESTION 1: TMid(L, S, S) behavior
# ════════════════════════════════════════════════════════════════════

print("=" * 70)
print("QUESTION 1: TMidVal(L, S, S) for all (L, S) in {0,1,2}^2")
print("=" * 70)
print()
print(f"{'L':>3} {'S':>3} | {'TMid(L,S,S)':>11} | {'=S?':>4} {'=L?':>4} | Classification")
print("-" * 60)

stutter_count = 0
copy_left_count = 0
other_count = 0

for L in range(3):
    for S in range(3):
        out = TMID[(L, S, S)]
        eq_s = (out == S)
        eq_l = (out == L)
        if eq_s:
            if L == S:
                cls = "no-op (L=S=out)"
            else:
                cls = "STUTTER (out=S, not privileged)"
                stutter_count += 1
        elif eq_l:
            cls = "COPY LEFT (out=L != S, fires)"
            copy_left_count += 1
        else:
            cls = f"OTHER (out={out} != S={S}, != L={L})"
            other_count += 1
        print(f"{L:>3} {S:>3} | {out:>11} | {'Y' if eq_s else 'N':>4} {'Y' if eq_l else 'N':>4} | {cls}")

print()
print(f"Summary: {stutter_count} stutters, {copy_left_count} copy-left fires, "
      f"{other_count} other, {9 - stutter_count - copy_left_count - other_count} L=S no-ops")

# Also check: when R=S (not privileged from right), what is TMid(L, S, S)?
# In the ring, position k is not privileged iff c[k] = f(c[k-1], c[k], c[k+1]).
# Stutter = TMid(L,S,S) = S means "if R=S, the position doesn't fire."
print()
print("Interpretation: When c[k-1]=L, c[k]=S, c[k+1]=S (right neighbor = self),")
print("TMid(L,S,S)=S means position k is NOT privileged (no move).")
print("TMid(L,S,S)=L means position k IS privileged and copies left neighbor's value.")


# ════════════════════════════════════════════════════════════════════
# QUESTION 2: Run-of-3 pigeonhole for ternary interior
# ════════════════════════════════════════════════════════════════════

print()
print("=" * 70)
print("QUESTION 2: Pigeonhole for ternary interior assignments")
print("=" * 70)
print()

def has_run_of_k(seq, k):
    """Check if seq has k consecutive equal values."""
    count = 1
    for i in range(1, len(seq)):
        if seq[i] == seq[i-1]:
            count += 1
            if count >= k:
                return True
        else:
            count = 1
    return False

def has_equal_pair(seq):
    """Check if any two consecutive elements are equal."""
    return has_run_of_k(seq, 2)

def count_equal_pairs(seq):
    """Count number of consecutive equal pairs."""
    return sum(1 for i in range(len(seq)-1) if seq[i] == seq[i+1])

# For n processors, interior = positions 3 to n-4 inclusive
# Number of interior positions = n - 7 (for n >= 10)
print("Analysis: For n-ring with ternary interior at positions 3..n-4:")
print("  Interior length = n - 7")
print("  Consecutive pairs in interior = n - 8")
print()

for n in [10, 11, 12, 13, 14]:
    int_len = n - 7  # positions 3,...,n-4
    if int_len < 1:
        continue
    total = 3 ** int_len
    run3_count = 0
    pair_count = 0
    for assignment in iprod(range(3), repeat=int_len):
        if has_run_of_k(assignment, 3):
            run3_count += 1
        if has_equal_pair(assignment):
            pair_count += 1
    print(f"n={n}: interior length={int_len}, total assignments={total}")
    print(f"  Has run of 3: {run3_count}/{total} = {run3_count/total*100:.1f}%")
    print(f"  Has equal pair (run of 2): {pair_count}/{total} = {pair_count/total*100:.1f}%")
    print(f"  NO equal pair (all distinct neighbors): {total-pair_count}/{total} = {(total-pair_count)/total*100:.1f}%")
    print()

print("Pigeonhole argument for equal pair (run of 2):")
print("  With 3 values and k positions, the number of sequences with no")
print("  two consecutive equal = 3 * 2^(k-1) (first free, rest != predecessor).")
print("  Fraction without equal pair = 3*2^(k-1) / 3^k = (2/3)^(k-1)")
for n in [10, 11, 12, 13, 14, 20]:
    k = n - 7
    if k < 1:
        continue
    frac_no_pair = (2/3) ** (k - 1)
    print(f"  n={n}, k={k}: fraction with NO equal pair = (2/3)^{k-1} = {frac_no_pair:.6f}")

print()
print("Pigeonhole argument for run of 3:")
print("  With 3 values and k positions, pigeonhole gives a run of 3")
print("  only when k >= 3*2+1 = 7 (can avoid with alternating patterns).")
print("  So run-of-3 is NOT guaranteed by simple pigeonhole.")
print("  For small k: fraction that avoid run-of-3 is significant.")
print()

# More detailed: for n=10, interior has 3 positions.
# Can we ALWAYS find c[k]=c[k-1] somewhere in positions 3..n-4?
# The answer is: only if int_len > 3 (by pigeonhole, 4 ternary values have
# at least one consecutive repeat among 3 pairs... no, that's not right either).
# With 3 values and k positions, we need k-1 >= 3 pairs, i.e. k >= 4 to guarantee.
# Actually: 3 values, can have alternating 0,1,0,1,... with no equal pair.
# So no guarantee of equal pair for ANY fixed k!
# The (2/3)^(k-1) formula gives the exact fraction.

print("KEY INSIGHT: Equal pair is NOT guaranteed by pigeonhole alone.")
print("With 3 values, alternating patterns (e.g., 0,1,2,0,1,2,...) avoid all pairs.")
print("The probability of NO pair decreases as (2/3)^(k-1) but never reaches 0.")
print()

# ── Copy-left pair analysis (c[k] = c[k-1] in interior) ──
print("Copy-left pair analysis:")
print("If c[k] = c[k-1] at some interior position k, then TMid(c[k-2], c[k-1], c[k])")
print("= TMid(c[k-2], c[k-1], c[k-1]). From Q1 table:")
print()

copy_left_cases = []
stutter_cases = []
for L in range(3):
    for S in range(3):
        out = TMID[(L, S, S)]
        if out == S:
            stutter_cases.append((L, S))
        elif out == L:
            copy_left_cases.append((L, S))
        # else: other

print(f"  TMid(L,S,S) = S (stutter/no-op): {stutter_cases}")
print(f"  TMid(L,S,S) = L (copy left):     {copy_left_cases}")
print()
print("So when c[k]=c[k-1]=S: if c[k-2]=L is in a copy-left pair with S,")
print("then position k-1 fires (copies left). Otherwise it stutters.")


# ════════════════════════════════════════════════════════════════════
# QUESTION 3: TP-preserving copy-right steps at interior (n=9)
# ════════════════════════════════════════════════════════════════════

print()
print("=" * 70)
print("QUESTION 3: TP-preserving privileged moves at interior positions (n=9)")
print("=" * 70)
print()

n = 9

def all_configs(n):
    """Generate all configs for n-ring with CUP-2 state sizes."""
    ranges = [range(cup2_m(n, i)) for i in range(n)]
    for c in iprod(*ranges):
        yield list(c)

def is_privileged(n, c, j):
    """Check if position j is privileged in config c."""
    L = c[(j - 1) % n]
    S = c[j]
    R = c[(j + 1) % n]
    out = cup2_out(n, j, L, S, R)
    return out != S

def fire(n, c, j):
    """Fire position j, return new config."""
    c2 = list(c)
    L = c[(j - 1) % n]
    S = c[j]
    R = c[(j + 1) % n]
    c2[j] = cup2_out(n, j, L, S, R)
    return c2

def tp_count(c, n):
    """Count total privilege (number of privileged positions)."""
    return sum(1 for j in range(n) if is_privileged(n, c, j))

# Find good cycle configs (by computing the cycle from the known structure)
# The good cycle for CUP-2 has length 3n-2 and visits (n+2)(n+3)/2 - 5 good configs.
# For n=9: length 25, good configs = 11*12/2 - 5 = 61

# Instead of computing the full cycle, let's enumerate all configs and check
# TP-preserving steps at interior positions.

print(f"n={n}, total configs = {4 * 3**7} = 4*3^7")
print(f"Interior positions: 3..{n-4} = {list(range(3, n-3))}")
print(f"(positions 2..{n-3} are mid-table positions)")
print()

# Actually for n=9: positions 0(bot), 1(low), 2..6(mid), 7(high), 8(top)
# "Interior" in the 6-tuple sense = positions 3..5 (not in the 6-tuple boundary)
# But the question asks about positions 3..n-4 = 3..5 for n=9

# Let's check ALL mid positions (2..6) since they all use TMidVal
print("Checking all mid positions (2..6) that use TMidVal:")
print()

total_priv_mid = 0
copy_left_mid = 0
copy_right_mid = 0
copy_other_mid = 0
tp_preserving_count = 0
tp_preserving_copy_right = 0
tp_preserving_copy_left = 0

config_count = 0
for c in all_configs(n):
    config_count += 1
    for j in range(2, n - 2):  # mid positions: 2,3,4,5,6
        if not is_privileged(n, c, j):
            continue
        L = c[(j-1) % n]
        S = c[j]
        R = c[(j+1) % n]
        out = cup2_out(n, j, L, S, R)

        total_priv_mid += 1

        if out == L:
            copy_left_mid += 1
        elif out == R:
            copy_right_mid += 1
        else:
            copy_other_mid += 1

        # Check TP-preserving: does firing j keep TP the same?
        c2 = fire(n, c, j)
        tp_before = tp_count(c, n)
        tp_after = tp_count(c2, n)
        if tp_after == tp_before:
            tp_preserving_count += 1
            if out == R:
                tp_preserving_copy_right += 1
            elif out == L:
                tp_preserving_copy_left += 1

print(f"Total configs enumerated: {config_count}")
print(f"Total privileged steps at mid positions: {total_priv_mid}")
print(f"  Copy-left (out=L):  {copy_left_mid} ({copy_left_mid/total_priv_mid*100:.1f}%)")
print(f"  Copy-right (out=R): {copy_right_mid} ({copy_right_mid/total_priv_mid*100:.1f}%)")
print(f"  Other:              {copy_other_mid} ({copy_other_mid/total_priv_mid*100:.1f}%)")
print()
print(f"TP-preserving privileged steps at mid positions: {tp_preserving_count}")
print(f"  of which copy-left:  {tp_preserving_copy_left}")
print(f"  of which copy-right: {tp_preserving_copy_right}")
print(f"  (other: {tp_preserving_count - tp_preserving_copy_left - tp_preserving_copy_right})")
print()

# Now restrict to "interior" = positions 3..n-4 = 3..5
print(f"Restricting to interior positions 3..{n-4}:")
total_priv_int = 0
copy_left_int = 0
copy_right_int = 0
copy_other_int = 0
tp_pres_int = 0
tp_pres_cr_int = 0
tp_pres_cl_int = 0

for c in all_configs(n):
    for j in range(3, n - 3):  # interior: 3,4,5
        if not is_privileged(n, c, j):
            continue
        L = c[(j-1) % n]
        S = c[j]
        R = c[(j+1) % n]
        out = cup2_out(n, j, L, S, R)

        total_priv_int += 1
        if out == L:
            copy_left_int += 1
        elif out == R:
            copy_right_int += 1
        else:
            copy_other_int += 1

        c2 = fire(n, c, j)
        tp_before = tp_count(c, n)
        tp_after = tp_count(c2, n)
        if tp_after == tp_before:
            tp_pres_int += 1
            if out == R:
                tp_pres_cr_int += 1
            elif out == L:
                tp_pres_cl_int += 1

print(f"Total privileged steps at interior: {total_priv_int}")
if total_priv_int > 0:
    print(f"  Copy-left:  {copy_left_int} ({copy_left_int/total_priv_int*100:.1f}%)")
    print(f"  Copy-right: {copy_right_int} ({copy_right_int/total_priv_int*100:.1f}%)")
    print(f"  Other:      {copy_other_int} ({copy_other_int/total_priv_int*100:.1f}%)")
    print()
    print(f"TP-preserving at interior: {tp_pres_int}")
    print(f"  Copy-left:  {tp_pres_cl_int}")
    print(f"  Copy-right: {tp_pres_cr_int}")
    print(f"  Other:      {tp_pres_int - tp_pres_cl_int - tp_pres_cr_int}")

# ── Detailed TMid classification ──
print()
print("=" * 70)
print("APPENDIX: Full TMidVal table with copy-left/copy-right classification")
print("=" * 70)
print()
print(f"{'L':>3} {'S':>3} {'R':>3} | {'out':>3} | {'=L':>3} {'=S':>3} {'=R':>3} | Classification")
print("-" * 65)

for L in range(3):
    for S in range(3):
        for R in range(3):
            out = TMID[(L, S, R)]
            eq_l = (out == L)
            eq_s = (out == S)
            eq_r = (out == R)
            priv = (out != S)
            if not priv:
                cls = "not privileged"
            elif eq_l and eq_r:
                cls = "fires, out=L=R"
            elif eq_l:
                cls = "COPY LEFT"
            elif eq_r:
                cls = "COPY RIGHT"
            else:
                cls = f"OTHER (out={out})"
            print(f"{L:>3} {S:>3} {R:>3} | {out:>3} | {'Y' if eq_l else '.':>3} {'Y' if eq_s else '.':>3} {'Y' if eq_r else '.':>3} | {cls}")
    print()
