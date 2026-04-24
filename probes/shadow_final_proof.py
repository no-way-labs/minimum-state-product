"""
COMPLETE analytic proof of Distinctness and Disjointness for all n ≥ 5.
No computational verification needed — pure case analysis.

SETUP:
  g0(j) = 1 iff 1 ≤ j mod 2n ≤ n  (indicator of {1,...,n} on Z_{2n})
  s_k[i] = g0(k + d_i)
  g_j[i] = g0(j - i)   (waterfall: g_j[i] = 1 iff j ∈ {i+1,...,n+i})

  D = {d_i mod 2n : i=0,...,n-1} = {0} ∪ {2,...,n-2} ∪ {n+1} ∪ {2n-1}
  D^c = {1} ∪ {n-1, n} ∪ {n+2,...,2n-2}
"""


def d_shift(i, n):
    if 0 <= i <= n - 5:
        return n - 2 - i
    elif i == n - 4:
        return 0
    elif i == n - 3:
        return n + 1
    elif i == n - 2:
        return 2
    elif i == n - 1:
        return 2 * n - 1


def g0(j, n):
    j = j % (2 * n)
    return 1 if 1 <= j <= n else 0


def shadow_config(k, n):
    return tuple(g0(k + d_shift(i, n), n) for i in range(n))


# =================================================================
# THEOREM 1: DISTINCTNESS (all n ≥ 5)
# =================================================================
print("=" * 70)
print("THEOREM 1: DISTINCTNESS")
print("=" * 70)
print()
print("""
THEOREM: For all n ≥ 5, s_j ≠ s_k whenever j ≠ k (mod 2n).

PROOF:
s_j = s_k iff g0(j+d) = g0(k+d) for all d ∈ D.
This means (j+D) ∩ D(Δ) = ∅ where Δ = k-j mod 2n and
D(Δ) = {x : g0(x) ≠ g0(x+Δ)}.

D(Δ) consists of two arcs of size Δ' = min(Δ, 2n-Δ), separated by
exactly n on the circle Z_{2n}. Call them Arc1 and Arc2.

For (j+D) ∩ D(Δ) = ∅: need D(Δ) ⊂ j + D^c. Since D(Δ) is two arcs
separated by n, Arc1 - j ⊂ D^c and Arc2 - j ⊂ D^c.
Since Arc2 = Arc1 + n, this requires two runs of D^c separated by n,
each of size ≥ Δ' ≥ 1.

D^c has exactly three maximal runs:
  Run A = {1}           (size 1, centered at 1)
  Run B = {n-1, n}      (size 2, centered at n-½)
  Run C = {n+2,...,2n-2} (size n-3, centered at 3n/2)

For ANY two of these runs, their centers are NOT n apart:
  |center(A) - center(B)| = n - 3/2 ≠ n
  |center(A) - center(C)| = 3n/2 - 1 ≠ n  (for n ≥ 5)
  |center(B) - center(C)| = n/2 + 1/2 ≠ n

More precisely, checking element-by-element:
  Run A + n = {n+1}. But n+1 ∈ D (it's the shift d_{n-3}). Not in D^c.
  Run B + n = {2n-1, 0}. Both in D (d_{n-1}=2n-1, d_{n-4}=0). Not in D^c.
  Run C + n = {2n+2,...,3n-2} ≡ {2,...,n-2} (mod 2n). All in D. Not in D^c.

Therefore no pair of runs is n apart. So D(Δ) cannot be contained in
any translate of D^c, meaning (j+D) ∩ D(Δ) ≠ ∅ for all j.

This holds for all Δ ∈ {1,...,2n-1}, proving s_j ≠ s_k.  ∎
""")

# Verify the run+n claims
print("Verification of Run+n claims:")
for n in [5, 7, 10, 20, 50, 100]:
    D_set = {0} | set(range(2, n-1)) | {n+1} | {2*n-1}

    # Run A + n
    runA_plus_n = {(1 + n) % (2*n)}
    assert runA_plus_n <= D_set, f"Run A+n not in D at n={n}"

    # Run B + n
    runB_plus_n = {(n-1+n) % (2*n), (n+n) % (2*n)}
    assert runB_plus_n <= D_set, f"Run B+n not in D at n={n}"

    # Run C + n
    runC_plus_n = {(x+n) % (2*n) for x in range(n+2, 2*n-1)}
    assert runC_plus_n <= D_set, f"Run C+n not in D at n={n}"

    print(f"  n={n}: Run A+n={runA_plus_n}⊂D ✓, Run B+n={runB_plus_n}⊂D ✓, "
          f"Run C+n⊂D ✓ ({len(runC_plus_n)} elements)")

print()

# Also verify Run - n (since arcs could go the other way)
print("Verification of Run-n claims:")
for n in [5, 7, 10, 20, 50, 100]:
    D_set = {0} | set(range(2, n-1)) | {n+1} | {2*n-1}

    runA_minus_n = {(1 - n) % (2*n)}  # = {n+1}
    assert runA_minus_n <= D_set

    runB_minus_n = {(n-1-n) % (2*n), (n-n) % (2*n)}  # = {2n-1, 0}
    assert runB_minus_n <= D_set

    runC_minus_n = {(x-n) % (2*n) for x in range(n+2, 2*n-1)}  # = {2,...,n-2}
    assert runC_minus_n <= D_set

    print(f"  n={n}: Run A-n⊂D ✓, Run B-n⊂D ✓, Run C-n⊂D ✓")

print()


# =================================================================
# THEOREM 2: DISJOINTNESS (all n ≥ 5)
# =================================================================
print("=" * 70)
print("THEOREM 2: DISJOINTNESS")
print("=" * 70)
print()
print("""
THEOREM: For all n ≥ 5, no shadow config equals any good config:
s_k ≠ g_j for all k, j ∈ Z_{2n}.

PROOF:
s_k[i] = g0(k + d_i) and g_j[i] = g0(j - i).

Define e_i = d_i + i. Then s_k[i] = g0(k + e_i - i) and g_j[i] = g0(j - i).
s_k[i] = g_j[i] iff g0(k + e_i - i) = g0(j - i),
i.e., (k + e_i - i) and (j - i) are on the same side of {1,...,n}.

Computing e_i:
  For 0 ≤ i ≤ n-5: e_i = (n-2-i) + i = n-2
  For i = n-1: e_{n-1} = (2n-1) + (n-1) = 3n-2 ≡ n-2 (mod 2n)
  So e_i = n-2 for i ∈ {0,...,n-5} ∪ {n-1}  (a set of n-3 positions)

  For i = n-4: e_{n-4} = 0 + (n-4) = n-4
  For i = n-3: e_{n-3} = (n+1) + (n-3) = 2n-2
  For i = n-2: e_{n-2} = 2 + (n-2) = n

For the n-3 positions with e_i = n-2:
  s_k[i] = g_j[i] iff g0(k+n-2-i) = g0(j-i)
  iff g0(a + (k-j+n-2)) = g0(a) where a = j-i.

Let Δ = (k-j+n-2) mod 2n. The condition g0(a+Δ) = g0(a) must hold
for all a in {j, j-1, ..., j-n+5, j-n+1} (n-3 values, a near-
consecutive arc with a 3-element gap at {j-n+4, j-n+3, j-n+2}).

For this n-3 element set to lie entirely in the agreement set
Agr(Δ) = {x : g0(x) = g0(x+Δ)}, which consists of two arcs each
of size n - Δ' where Δ' = min(Δ, 2n-Δ):

The n-3 values span an arc of total width n-2 (with a 3-element gap).
For them to fit in agreement arcs of size n-Δ' each: need n-Δ' ≥ n-4,
i.e., Δ' ≤ 4. But the gap means we actually need Δ' ≤ 3.

(The gap positions j-n+2, j-n+3, j-n+4 could land on detection
positions, but the n-3 specified positions must all be in agreement.
The specified positions form a block of n-5 consecutive {j,...,j-n+5}
plus the isolated j-n+1, spanning width n-1. For n-5 consecutive
values to fit in one agreement arc of size n-Δ': need Δ' ≤ 5.
Then j-n+1, which is 3 away from j-n+4, must also be in agreement.
Checking: the agreement arcs have size n-Δ'. For the block {j,...,j-n+5}
(size n-4) and isolated j-n+1 (distance 3 from block end) to all be in
agreement: need arc size ≥ n-1, giving Δ' ≤ 1. OR the gap {j-n+4,...,j-n+2}
must overlap a detection set boundary, allowing the arc to "skip" over.)

Actually, the simplest argument: Δ' ≤ n/2 (otherwise |Agr| = 2(n-Δ') < n,
and n-3 values can't fit in total agreement size < n). But even for
Δ' ≤ n/2, we need the specific positions to miss D(Δ).

Let me use a cleaner approach: only 8 candidate Δ values survive.

ALTERNATIVE PROOF:
For the n-3 positions with e_i = n-2, consider just the ENDPOINTS:
  Position i=0: a = j, need j ∈ Agr(Δ)
  Position i=n-5: a = j-n+5, need j-n+5 ∈ Agr(Δ)
  Position i=n-1: a = j-n+1, need j-n+1 ∈ Agr(Δ)

The values j and j-n+5 span a gap of n-5. For both to be in the same
agreement arc of size n-Δ': need n-Δ' > n-5, i.e., Δ' < 5.
Plus j-n+1 (4 positions from j-n+5) must also be in agreement.

So Δ' ∈ {1, 2, 3, 4}, giving Δ ∈ {1,2,3,4,2n-4,2n-3,2n-2,2n-1},
i.e., k-j ∈ {3-n, 4-n, 5-n, 6-n, n-2, n-1, n, n+1} (mod 2n).
That's 8 candidates.

But we can eliminate Δ'=4 too: position i=0 gives a=j, position i=n-5
gives a=j-n+5, distance n-5. Both in Agr arcs of size n-4 requires
n-4 > n-5 ✓, but also j-n+1 must be in Agr, distance 4 from j-n+5.
Total span from j-n+1 to j is n-1. Agreement arc size n-4.
j-n+1 to j can't fit in one arc of size n-4 < n-1.
Could be in two arcs? Only if the split falls in the 3-element gap.
This is possible but the 3 special positions will eliminate it.

For each of the 8 candidate Δ values (i.e., 8 values of k-j mod 2n),
we check the 3 SPECIAL positions i=n-4, n-3, n-2 (with e_i = n-4, 2n-2, n):

Position i=n-4 (e=n-4): g0(k+n-4-(n-4)) = g0(j-(n-4)), i.e., g0(k) = g0(j-n+4).
Position i=n-3 (e=2n-2): g0(k+2n-2-(n-3)) = g0(j-(n-3)), i.e., g0(k+n+1) = g0(j-n+3).
Position i=n-2 (e=n): g0(k+n-(n-2)) = g0(j-(n-2)), i.e., g0(k+2) = g0(j-n+2).
""")

# Check all 8 candidates analytically
# Δ = k-j+n-2 mod 2n, so k-j = Δ-n+2 mod 2n.
# Candidates: Δ ∈ {1,2,3,4,2n-4,2n-3,2n-2,2n-1}
# → k-j ∈ {3-n, 4-n, 5-n, 6-n, n-2, n-1, n, n+1} mod 2n

print("Checking 8 candidate k-j values (mod 2n):")
print()

for kj_offset_formula, delta_val_name in [
    ("3-n", "1"), ("4-n", "2"), ("5-n", "3"), ("6-n", "4"),
    ("n-2", "2n-4"), ("n-1", "2n-3"), ("n", "2n-2"), ("n+1", "2n-1")
]:
    print(f"  k-j ≡ {kj_offset_formula} (Δ={delta_val_name}):")

    # Check for several n values
    all_eliminated = True
    for n in [5, 6, 7, 8, 10, 15, 20, 50]:
        delta_candidates = {1: 1, 2: 2, 3: 3, 4: 4,
                            "2n-4": 2*n-4, "2n-3": 2*n-3,
                            "2n-2": 2*n-2, "2n-1": 2*n-1}
        kj_candidates = {"3-n": (3-n)%(2*n), "4-n": (4-n)%(2*n),
                         "5-n": (5-n)%(2*n), "6-n": (6-n)%(2*n),
                         "n-2": n-2, "n-1": n-1, "n": n, "n+1": n+1}
        kj = kj_candidates[kj_offset_formula]

        survived = False
        for j in range(2*n):
            k = (j + kj) % (2*n)
            # Check special positions
            # i=n-4: g0(k) = g0(j-n+4)
            ok_n4 = g0(k, n) == g0(j - n + 4, n)
            # i=n-3: g0(k+n+1) = g0(j-n+3)
            ok_n3 = g0(k + n + 1, n) == g0(j - n + 3, n)
            # i=n-2: g0(k+2) = g0(j-n+2)
            ok_n2 = g0(k + 2, n) == g0(j - n + 2, n)

            if ok_n4 and ok_n3 and ok_n2:
                # Also check a standard position to be safe
                # i=0: g0(k+n-2) = g0(j)
                ok_0 = g0(k + n - 2, n) == g0(j, n)
                if ok_0:
                    # Check full equality
                    sk = shadow_config(k, n)
                    gj = tuple(g0(j - i, n) for i in range(n))
                    if sk == gj:
                        survived = True
                        print(f"    n={n}: SURVIVED at j={j}, k={k}!")
                        all_eliminated = False

    if all_eliminated:
        print(f"    Eliminated for all tested n. ✓")

print()

# Now let's prove each case analytically
print("=" * 70)
print("ANALYTIC ELIMINATION OF ALL 8 CANDIDATES")
print("=" * 70)
print()

# For each Δ, derive which j values survive the standard positions,
# then show special positions kill them.

# Let's work out the constraints precisely.
# Standard positions (e_i = n-2): g0(j-i+Δ) = g0(j-i), i.e., j-i ∈ Agr(Δ).
# Special: i=n-4: g0(j-n+4+(k-j+n-4)) = g0(j-n+4), i.e., g0(j-n+4+k-j+n-4) = g0(j-n+4)
#   = g0(k+n-4-(n-4)... wait. Let me redo.
# i=n-4: s_k[n-4] = g0(k + d_{n-4}) = g0(k+0) = g0(k).
#         g_j[n-4] = g0(j-(n-4)) = g0(j-n+4).
# So need: g0(k) = g0(j-n+4).
# With k = j + (k-j):
# g0(j+(k-j)) = g0(j-n+4).
# Let c = k-j. Need g0(j+c) = g0(j-n+4).
# g0(x) = g0(y) iff x,y same side. So j+c and j-n+4 same side.
# Equivalently: (j+c) - (j-n+4) = c+n-4 must not cross a boundary.
# g0(j-n+4) = g0(j-n+4+(c+n-4)). Need c+n-4 ∈ Agr for the specific value j-n+4.

# This is getting complex case-by-case. Let me just do a clean finite check:
# For each of the 8 c values, check if there exists ANY (j, n≥5) where
# all n positions agree. The computational check above shows none survive
# through n=50. But let me prove it for general n.

# Key insight for clean proof: just check 4 positions explicitly.
# Positions: i=n-4 (d=0), i=n-3 (d=n+1), i=n-2 (d=2), i=n-1 (d=2n-1)
# These give:
#   s_k[n-4] = g0(k)          vs  g_j[n-4] = g0(j-n+4)
#   s_k[n-3] = g0(k+n+1)     vs  g_j[n-3] = g0(j-n+3)
#   s_k[n-2] = g0(k+2)       vs  g_j[n-2] = g0(j-n+2)
#   s_k[n-1] = g0(k+2n-1)    vs  g_j[n-1] = g0(j-n+1)
#
# Substituting k = j + c:
#   g0(j+c) = g0(j-n+4)         ... (*)
#   g0(j+c+n+1) = g0(j-n+3)     ... (**)
#   g0(j+c+2) = g0(j-n+2)       ... (***)
#   g0(j+c+2n-1) = g0(j-n+1)    ... (****)
#
# From (*) and (****): g0(j+c) = g0(j-n+4) and g0(j+c-1) = g0(j-n+1).
# Note j+c-1 = (j+c) - 1 and j-n+1 = (j-n+4) - 3.
# So we need g0(a) = g0(a-c-n+4) for a=j+c and
#            g0(a-1) = g0(a-1-c-n+4+3-3)... this is messy.
#
# Cleaner: define u = j + c, v = j - n + 4. Then:
# (*): g0(u) = g0(v)
# (**): g0(u+n+1) = g0(v-1)
# (***): g0(u+2) = g0(v-2)
# (****): g0(u+2n-1) = g0(v-3) = g0(u-1) [since 2n-1 ≡ -1]
#
# Wait: (****) says g0(j+c+2n-1) = g0(j-n+1).
# j+c+2n-1 ≡ j+c-1 mod 2n. j-n+1 = v-3. So g0(u-1) = g0(v-3).
# (**): g0(u+n+1) = g0(v-1).
#
# From (*): u, v same side: both in {1,...,n} or both in {0,n+1,...,2n-1}.
# From (****): u-1, v-3 same side.
# From (***): u+2, v-2 same side.
# From (**): u+n+1, v-1 same side. Note g0(u+n+1) = g0(u+n+1).
#   If u ∈ {1,...,n}: u+n+1 ∈ {n+2,...,2n+1} ≡ {n+2,...,2n-1,0,1}.
#     g0(u+n+1) = 1 iff u+n+1 ∈ {1,...,n}, i.e., u+n+1 ≤ n → u ≤ -1. No.
#     Or u+n+1 mod 2n ∈ {1,...,n}: for u ∈ {1,...,n}, u+n+1 mod 2n ∈ {n+2,...,1}.
#     u+n+1 mod 2n = u+n+1 if u ≤ n-1 (then u+n+1 ≤ 2n), = u+n+1-2n = u-n+1 if u=n.
#     For u ∈ {1,...,n-1}: u+n+1 ∈ {n+2,...,2n}. mod 2n: {n+2,...,2n-1,0}. g0 = 0 except g0(0)=0. All 0.
#     For u=n: u+n+1 = 2n+1 → 1 mod 2n. g0(1) = 1.
#   So if u ∈ {1,...,n-1}: g0(u+n+1) = 0. If u=n: g0(u+n+1) = 1.
#   Similarly g0(v-1): if v ∈ {1,...,n}: g0(v-1) = 1 if v-1 ∈ {1,...,n} i.e. v ∈ {2,...,n+1}∩{1,...,n} = {2,...,n}.
#     g0(v-1) = 0 if v = 1.

# This case analysis works but is tedious. Let me just enumerate all
# possible (u mod 2n, v mod 2n) satisfying (*)-(*****) and show none exist
# where v - u = -c - n + 4 for valid c.

print("Complete case analysis for all n ≥ 5:")
print()
print("Let u = (j+c) mod 2n, v = (j-n+4) mod 2n.")
print("Need: c = k - j satisfies one of 8 candidate values.")
print("Also: v = u - c - n + 4 mod 2n, so c = u - v - n + 4 mod 2n.")
print()
print("The 4 constraints (*)-(*****) involve only g0 at:")
print("  u, v, u+n+1, v-1, u+2, v-2, u-1, v-3")
print("  = 8 values of g0, each 0 or 1.")
print()
print("Since g0 is determined by which interval [1,n] the arg falls in,")
print("and u,v determine everything, we enumerate over the 4 intervals")
print("that u and v can be in.")
print()

# The 4 constraints:
# (1) g0(u) = g0(v)
# (2) g0(u+n+1) = g0(v-1)
# (3) g0(u+2) = g0(v-2)
# (4) g0(u-1) = g0(v-3)
#
# g0 partitions Z_{2n} into two sets:
#   ON = {1,...,n}, OFF = {0,n+1,...,2n-1}
#
# For each constraint, both sides must be in ON or both in OFF.
#
# The boundary positions of the constraint values relative to u:
# u, u+2, u-1, u+n+1 = four positions around the circle.
# And relative to v: v, v-1, v-2, v-3 = four consecutive positions.
#
# v-3, v-2, v-1, v are 4 consecutive integers mod 2n.
# Their g0 values form a pattern depending on where v is:
#   If v ∈ {4,...,n}: all four in ON. Pattern: 1111.
#   If v = 3: v-3=0∈OFF, v-2=1∈ON, v-1=2∈ON, v=3∈ON. Pattern: 0111.
#   If v = 2: v-3=2n-1∈OFF, v-2=0∈OFF, v-1=1∈ON, v=2∈ON. Pattern: 0011.
#   If v = 1: v-3=2n-2∈OFF, v-2=2n-1∈OFF, v-1=0∈OFF, v=1∈ON. Pattern: 0001.
#   If v = 0: all OFF. Pattern: 0000.
#   If v = n+1: v-3=n-2∈ON, v-2=n-1∈ON, v-1=n∈ON, v=n+1∈OFF. Pattern: 1110.
#   If v = n+2: v-3=n-1∈ON, v-2=n∈ON, v-1=n+1∈OFF, v=n+2∈OFF. Pattern: 1100.
#   If v = n+3: v-3=n∈ON, v-2=n+1∈OFF, v-1=n+2∈OFF, v=n+3∈OFF. Pattern: 1000.
#   If v ∈ {n+4,...,2n-1}: all OFF. Pattern: 0000.
# Summary of v-patterns (g0(v-3), g0(v-2), g0(v-1), g0(v)):
v_patterns = {}
for n in [10]:  # representative
    for v in range(2*n):
        pat = (g0(v-3, n), g0(v-2, n), g0(v-1, n), g0(v, n))
        v_class = None
        if v == 0:
            v_class = "v=0"
        elif v == 1:
            v_class = "v=1"
        elif v == 2:
            v_class = "v=2"
        elif v == 3:
            v_class = "v=3"
        elif 4 <= v <= n:
            v_class = "4≤v≤n"
        elif v == n+1:
            v_class = "v=n+1"
        elif v == n+2:
            v_class = "v=n+2"
        elif v == n+3:
            v_class = "v=n+3"
        elif n+4 <= v <= 2*n-1:
            v_class = "n+4≤v≤2n-1"
        v_patterns[v_class] = pat

print("v-patterns (g0(v-3), g0(v-2), g0(v-1), g0(v)):")
for vc, pat in sorted(v_patterns.items()):
    print(f"  {vc:15s}: {pat}")

# Similarly for u: g0(u), g0(u+2), g0(u-1), g0(u+n+1)
# g0(u+n+1): if u ∈ {1,...,n-1}: u+n+1 ∈ {n+2,...,2n} → OFF (since 2n≡0, g0(0)=0). All OFF.
#            if u = n: u+n+1 = 2n+1 → 1. ON.
#            if u = 0: u+n+1 = n+1. OFF.
#            if u ∈ {n+1,...,2n-1}: u+n+1 ∈ {2n+2,...,3n} → {2,...,n} mod 2n. ON.

u_patterns = {}
for n in [10]:
    for u in range(2*n):
        pat = (g0(u, n), g0(u+2, n), g0(u-1, n), g0(u+n+1, n))
        u_class = None
        if u == 0:
            u_class = "u=0"
        elif u == 1:
            u_class = "u=1"
        elif 2 <= u <= n-2:
            u_class = "2≤u≤n-2"
        elif u == n-1:
            u_class = "u=n-1"
        elif u == n:
            u_class = "u=n"
        elif u == n+1:
            u_class = "u=n+1"
        elif n+2 <= u <= 2*n-3:
            u_class = "n+2≤u≤2n-3"
        elif u == 2*n-2:
            u_class = "u=2n-2"
        elif u == 2*n-1:
            u_class = "u=2n-1"
        u_patterns[u_class] = pat

print()
print("u-patterns (g0(u), g0(u+2), g0(u-1), g0(u+n+1)):")
for uc, pat in sorted(u_patterns.items()):
    print(f"  {uc:15s}: {pat}")

print()

# Now match: constraints are
# g0(u) = g0(v), g0(u+n+1) = g0(v-1), g0(u+2) = g0(v-2), g0(u-1) = g0(v-3)
# Rearranged: u-pattern must equal v-pattern component-wise:
# u_pat[0] = v_pat[3]  (g0(u) = g0(v))
# u_pat[1] = v_pat[1]  (g0(u+2) = g0(v-2))
# u_pat[2] = v_pat[0]  (g0(u-1) = g0(v-3))
# u_pat[3] = v_pat[2]  (g0(u+n+1) = g0(v-1))

print("Matching u-classes to v-classes:")
print("Need: u[0]=v[3], u[1]=v[1], u[2]=v[0], u[3]=v[2]")
print()

matches = []
for uc, up in sorted(u_patterns.items()):
    for vc, vp in sorted(v_patterns.items()):
        if up[0] == vp[3] and up[1] == vp[1] and up[2] == vp[0] and up[3] == vp[2]:
            matches.append((uc, vc, up, vp))
            print(f"  MATCH: {uc} ↔ {vc}: u={up}, v={vp}")

print()
if not matches:
    print("NO MATCHES! Disjointness proved for all n ≥ 5. ∎")
else:
    print(f"{len(matches)} matches found. Checking if they yield valid (j,k)...")
    # For each match, check if c = u - v - n + 4 is one of the 8 candidates
    for uc, vc, up, vp in matches:
        print(f"  {uc} ↔ {vc}:")
        # Get representative u, v values for n=10
        n = 10
        for u in range(2*n):
            u_pat_actual = (g0(u, n), g0(u+2, n), g0(u-1, n), g0(u+n+1, n))
            if u_pat_actual != up:
                continue
            for v in range(2*n):
                v_pat_actual = (g0(v-3, n), g0(v-2, n), g0(v-1, n), g0(v, n))
                if v_pat_actual != vp:
                    continue
                c = (u - v - n + 4) % (2*n)
                # Check: is this a valid c candidate?
                cands = {(3-n)%(2*n), (4-n)%(2*n), (5-n)%(2*n), (6-n)%(2*n),
                         n-2, n-1, n, n+1}
                if c in cands:
                    # Full check
                    j = (u - c) % (2*n)
                    k = (j + c) % (2*n)
                    sk = shadow_config(k, n)
                    gj = tuple(g0(j - i, n) for i in range(n))
                    if sk == gj:
                        print(f"    REAL OVERLAP at n={n}: u={u}, v={v}, c={c}, j={j}, k={k}")
                    else:
                        print(f"    u={u}, v={v}, c={c}: special positions match but other positions don't")
                else:
                    pass  # c not a candidate, fine


print()
print("=" * 70)
print("FINAL THEOREM")
print("=" * 70)
print()
print("""
THEOREM (Shadow Cycle Properties, all n ≥ 5):
The shadow cycle S = (s_0,...,s_{2n-1}) with s_k[i] = g0(k + d_i) satisfies:

(i)   CLOSURE: Immediate from periodicity mod 2n.
(ii)  MOVERS: 6-case analytic proof (Exploration 11).
(iii) DISTINCTNESS: D^c has 3 runs; Run+n ⊂ D for each run,
      so D(Δ) never avoids D entirely. (Theorem 1 above.)
(iv)  DISJOINTNESS: 4-position constraint (i=n-4,n-3,n-2,n-1) yields
      NO matching (u,v) class pair. (Theorem 2 above.)
(v)   DETERMINED ENTRIES: follows from construction.

Combined with Universal Escape (Exploration 10):
  M_n = 32 · 3^{n-4} for all n ≥ 5.  ∎
""")
