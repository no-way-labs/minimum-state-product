#!/usr/bin/env python3
"""
Verify that the lexicographic measure (total_disagree, sum_distances)
strictly decreases on every interior fire at positions 3..n-4.

CUP-2 system with ms = (2, 3, 3, ..., 3, 2).
"""

from itertools import product as iproduct

# === CUP-2 Tables ===
TMid = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,
        (1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,
        (2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):2,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2}

TBot = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,
        (1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
TLow = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,
        (1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
THigh = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,
         (1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,
         (2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
TTop = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,
        (1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,
        (2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}


def get_table(j, n):
    """Return the transition table for position j in a ring of size n."""
    if j == 0:
        return TBot
    elif j == 1:
        return TLow
    elif j == n - 2:
        return THigh
    elif j == n - 1:
        return TTop
    else:
        return TMid


def ms_for_n(n):
    """State counts: (2, 3, 3, ..., 3, 2)."""
    return [2] + [3] * (n - 2) + [2]


def fire(c, j, n):
    """Fire position j, return new config (or None if not privileged)."""
    ms = ms_for_n(n)
    L = c[(j - 1) % n]
    S = c[j]
    R = c[(j + 1) % n]
    tbl = get_table(j, n)
    new_val = tbl[(L, S, R)]
    if new_val == S:
        return None  # not privileged
    c2 = list(c)
    c2[j] = new_val
    return tuple(c2)


# === Part 1: Verify TMid copies neighbor for all privileged transitions ===
print("=" * 70)
print("PART 1: TMid copies neighbor for all privileged transitions")
print("=" * 70)

privileged = []
for (L, S, R), out in sorted(TMid.items()):
    if out != S:
        privileged.append((L, S, R, out))
        copies_L = (out == L)
        copies_R = (out == R)
        copies = "copies_L" if copies_L else ("copies_R" if copies_R else "NEITHER")
        print(f"  TMid({L},{S},{R}) = {out}  [{copies}]")

all_copy = all(out == L or out == R for (L, S, R, out) in privileged)
print(f"\nAll {len(privileged)} privileged transitions copy a neighbor: {all_copy}")

# === Part 2: Classify shifting types ===
print("\n" + "=" * 70)
print("PART 2: Classify right-shifting vs left-shifting types")
print("=" * 70)

# Right-shifting: TMid(a, b, b) = a (when a != b, i.e., privileged)
# This means: if disagree is at j (c[j-1]=a, c[j]=b, a!=b) and c[j+1]=b,
# then c'[j] = a, so the disagree boundary moves RIGHT (from j to j+1).
print("\nRight-shifting types (a,b) where TMid(a,b,b) = a:")
right_shifting = set()
for a in range(3):
    for b in range(3):
        if a != b:
            out = TMid[(a, b, b)]
            if out == a:
                right_shifting.add((a, b))
                print(f"  ({a},{b}): TMid({a},{b},{b}) = {out} = L  ✓")
            else:
                print(f"  ({a},{b}): TMid({a},{b},{b}) = {out} ≠ {a}  (not right-shifting)")

# Left-shifting: TMid(a, a, b) = b (when a != b, i.e., privileged)
# If disagree at j means c[j-1]=a, c[j]=b with a!=b, then for left-shifting
# we need: when c[j-1]=c[j]=a and c[j+1]=b (disagree at j+1), TMid gives b.
# Actually let me reconsider. Left-shifting type (a,b) means:
# TMid(a, a, b) = b, so c[j-1]=a, c[j]=a, c[j+1]=b, output=b.
# The disagree at j+1 (type (a,b)) shifts LEFT to j (now c'[j]=b != c[j-1]=a).
# Wait, that keeps disagree at j+1 AND creates one at j. That's wrong.
#
# Let me think more carefully about what "shifting" means for the measure.
#
# For a disagree at position j: c[j-1] != c[j], type = (c[j-1], c[j]).
# When j fires: c'[j] = TMid(c[j-1], c[j], c[j+1]).
#
# After firing j:
# - Disagree at j: c[j-1] vs c'[j] — may or may not exist
# - Disagree at j+1: c'[j] vs c[j+1] — may or may not exist
# - All other disagrees unchanged
#
# So firing at j can affect disagrees at positions j and j+1 only.

print("\nLeft-shifting types (a,b) where TMid(a,a,b) = b (i.e., copies R):")
left_shifting = set()
for a in range(3):
    for b in range(3):
        if a != b:
            out = TMid[(a, a, b)]
            if out == b:
                left_shifting.add((a, b))
                print(f"  ({a},{b}): TMid({a},{a},{b}) = {out} = R  ✓")
            else:
                print(f"  ({a},{b}): TMid({a},{a},{b}) = {out} ≠ {b}  (not left-shifting)")

print(f"\nRight-shifting types: {sorted(right_shifting)}")
print(f"Left-shifting types: {sorted(left_shifting)}")

# === Part 3: Compute measure ===

def compute_measure(c, n):
    """
    Compute (total_disagree, sum_distances) for interior positions 3..n-4.

    For each interior position j in {3, ..., n-4}:
      ld(j) = 1 if c[j] != c[j-1]
      If ld(j) = 1:
        type = (c[j-1], c[j])
        if type in right_shifting: dist = (n-4) - j  (distance to right boundary n-4)
        elif type in left_shifting: dist = j - 3      (distance to left boundary 3)
        else: dist = 0
    """
    interior = range(3, n - 3)  # positions 3, 4, ..., n-4
    total_d = 0
    sum_dist = 0
    for j in interior:
        if c[j] != c[j - 1]:
            total_d += 1
            tp = (c[j - 1], c[j])
            if tp in right_shifting:
                sum_dist += (n - 4) - j
            elif tp in left_shifting:
                sum_dist += j - 3
            # else: non-shifting, dist = 0
    return (total_d, sum_dist)


def lex_lt(a, b):
    """Lexicographic strict less-than."""
    return a[0] < b[0] or (a[0] == b[0] and a[1] < b[1])


# === Part 4: Exhaustive verification ===
print("\n" + "=" * 70)
print("PART 3: Exhaustive verification for n = 9, 10, 11, 12")
print("=" * 70)

for n in [9, 10, 11, 12]:
    ms = ms_for_n(n)
    interior_positions = list(range(3, n - 3))
    if not interior_positions:
        print(f"\nn={n}: no true interior positions (n-4={n-4} < 3), skipping")
        continue

    print(f"\nn={n}: interior positions = {interior_positions}")
    print(f"  State counts: {ms}, total configs = {2 * 3**(n-2) * 2}")

    total_fires = 0
    violations = 0
    violation_examples = []

    # Generate all configs
    ranges = [range(m) for m in ms]
    for c in iproduct(*ranges):
        for j in interior_positions:
            c2 = fire(c, j, n)
            if c2 is None:
                continue  # not privileged

            total_fires += 1
            m_before = compute_measure(c, n)
            m_after = compute_measure(c2, n)

            if not lex_lt(m_after, m_before):
                violations += 1
                if len(violation_examples) < 3:
                    violation_examples.append((c, j, c2, m_before, m_after))

    print(f"  Total interior fires checked: {total_fires}")
    print(f"  Violations: {violations}")

    if violations > 0:
        print(f"  FAILED! First {min(3, len(violation_examples))} violation(s):")
        for (c, j, c2, mb, ma) in violation_examples:
            print(f"    c={list(c)}, fire j={j}, c'={list(c2)}")
            print(f"      M(c)={mb}, M(c')={ma}")
            # Show details
            for pos in range(3, n - 3):
                if c[pos] != c[pos-1]:
                    tp = (c[pos-1], c[pos])
                    shift = "R" if tp in right_shifting else ("L" if tp in left_shifting else "N")
                    print(f"      Before: disagree at {pos}, type={tp}, shift={shift}")
            for pos in range(3, n - 3):
                if c2[pos] != c2[pos-1]:
                    tp = (c2[pos-1], c2[pos])
                    shift = "R" if tp in right_shifting else ("L" if tp in left_shifting else "N")
                    print(f"      After:  disagree at {pos}, type={tp}, shift={shift}")
    else:
        print(f"  PASSED ✓")

print("\n" + "=" * 70)
print("DONE")
print("=" * 70)
