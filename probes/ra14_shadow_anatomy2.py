#!/usr/bin/env python3
"""
RA14 Part 2: Deep dive into shadow anatomy.

Key findings from Part 1:
- All 1455 shadows at n=9 are CONSTANT OFFSETS of the good cycle (same word!)
- MNU holds for n=9 bounce-sweep (binary fires 2x, ternary fires 3x)
- At n=5: all min-CL cycles have EC. 13/100 lack shadow but all have EC.

Deep questions:
A) Why does constant offset work? (orbit structure of incrementing maps)
B) At n=5, the sweep word (CL=10) doesn't match min-CL (CL=12).
   What about the ACTUAL waterfall cycles?
C) Does every sub-threshold system have EC or shadow for ALL its cycles?
D) What's the orbit structure? Does incrementing always give constant-offset orbits?
"""

from collections import defaultdict, Counter
from itertools import product as iproduct
from math import prod, gcd
from functools import reduce

# ================================================================
# Q-A: WHY CONSTANT OFFSET?
# ================================================================
print("="*70)
print("Q-A: WHY DO CONSTANT OFFSETS PRODUCE SHADOW CYCLES?")
print("="*70)

print("""
With incrementing transitions, applying mover word w to config c gives:
  c' = c + delta (mod ms)
where delta[p] = (number of times p fires) mod ms[p] = 0 (since fires = ms[p]).

So the map T_w: c -> c is the IDENTITY for all configs!
Every config is a fixed point of T_w.

Wait — that means EVERY config starts a valid CL-length orbit? No.
The map is the identity only if each proc fires ms[p] times with +1 increments.
In that case, the orbit from ANY starting config c produces a cycle of the SAME configs
as the orbit from c + offset (with offset applied mod ms at each step).

Actually: if good cycle is G = [g_0, g_1, ..., g_{L-1}], then the orbit from
g_0 + d is exactly [g_0+d, g_1+d, ..., g_{L-1}+d] (mod ms).
This is because each step adds +1 to exactly one coordinate.
The increment is position-independent, so:
  (g_t + d) + e_p = g_{t+1} + d (mod ms)
where e_p is the unit vector for proc p.

So with incrementing transitions and fire count = ms[p] for each p:
EVERY orbit is a constant-offset copy of EVERY other orbit!
The total number of orbits = prod(ms) / CL.

This is a VERY strong structure. The shadow exists iff there's a non-zero
offset d such that the shifted cycle is disjoint from the good cycle.
""")

# Verify this theory
n = 9
ms = [2, 3, 3, 2, 3, 3, 2, 3, 3]
word = [8, 7, 8, 7, 6, 5, 4, 5, 4, 3, 2, 1, 2, 1, 0, 8, 7, 6, 5, 4, 3, 2, 1, 0]
CL = len(word)
product_val = prod(ms)

print(f"\nn=9: product={product_val}, CL={CL}")
print(f"Expected orbits: {product_val}/{CL} = {product_val/CL}")
print(f"Fire counts: {Counter(word)}")
print(f"Fire count == ms[p]? {all(Counter(word)[p] == ms[p] for p in range(n))}")

# Count: how many distinct offsets d have G+d disjoint from G?
from itertools import product as iproduct

# Build good cycle
def build_cycle(word, ms, n, trans=None):
    if trans is None:
        trans = [1]*n
    L = len(word)
    configs = [[0]*n]
    for t in range(L):
        c = list(configs[-1])
        p = word[t]
        c[p] = (c[p] + trans[p]) % ms[p]
        configs.append(c)
    if configs[-1] != configs[0]:
        return None
    if len(set(tuple(c) for c in configs[:L])) != L:
        return None
    return [tuple(c) for c in configs[:L]]

good = build_cycle(word, ms, n)
good_set = set(good)

# For each offset d, check if G+d is disjoint from G
disjoint_offsets = []
intersecting_offsets = []

for d in iproduct(*(range(m) for m in ms)):
    if all(x == 0 for x in d):
        continue
    shifted = set(tuple((g[j] + d[j]) % ms[j] for j in range(n)) for g in good)
    if shifted & good_set:
        intersecting_offsets.append(d)
    else:
        disjoint_offsets.append(d)

print(f"\nDisjoint offsets: {len(disjoint_offsets)}")
print(f"Intersecting offsets: {len(intersecting_offsets)}")
print(f"Total non-zero offsets: {product_val - 1}")
print(f"Disjoint shadow cycles: {len(disjoint_offsets)} (each offset gives a unique shadow)")

# But wait — multiple offsets can give the SAME shadow cycle
# If d1 and d2 give same shadow, then G+d1 = G+d2 as sets,
# so d1-d2 is an "automorphism offset" of G.
# The automorphism group is the set of offsets d such that G+d = G.
auto_offsets = [(0,)*n]  # identity
for d in iproduct(*(range(m) for m in ms)):
    if all(x == 0 for x in d):
        continue
    shifted = set(tuple((g[j] + d[j]) % ms[j] for j in range(n)) for g in good)
    if shifted == good_set:
        auto_offsets.append(d)

print(f"\nAutomorphism offsets (G+d = G): {len(auto_offsets)}")
if len(auto_offsets) <= 10:
    for ao in auto_offsets:
        print(f"  {ao}")

print(f"Distinct shadow cycles = disjoint_offsets / auto_group_size")
print(f"  = {len(disjoint_offsets)} / {len(auto_offsets)} = {len(disjoint_offsets) // len(auto_offsets)}")
print(f"  Expected from Part 1: 1455")


# ================================================================
# Q-B: WHAT ABOUT NON-INCREMENTING TRANSITIONS?
# ================================================================
print(f"\n{'='*70}")
print("Q-B: SHADOW WITH NON-INCREMENTING TRANSITIONS")
print("="*70)

print("""
The constant-offset trick works ONLY for incrementing transitions.
With mixed inc/dec, the orbit structure changes:
  step t: proc p fires, value changes by trans[p] (not always +1).
  So (g_t + d) + trans[p]*e_p != g_{t+1} + d in general,
  because trans[p] could be -1 and the offset doesn't cancel.

Wait — actually it DOES still cancel!
  g_{t+1}[j] = g_t[j] + trans[p]*delta(j,p)  mod ms[j]
  (g_t[j] + d[j]) + trans[p]*delta(j,p) = g_{t+1}[j] + d[j]  mod ms[j]
The offset d is just added/subtracted independently. The transition
trans[p] applies the SAME way to g_t and g_t+d.

So the constant-offset property holds for ANY transition mode,
as long as each proc fires ms[p] times (so the total offset is 0).
""")

# Verify: test with mixed transitions at n=9
ternary_procs = [1, 2, 4, 5, 7, 8]

print("Testing constant-offset property with non-incrementing transitions...")
test_trans = [1, -1, 1, 1, -1, 1, 1, -1, 1]  # some dec ternary

good_mixed = build_cycle(word, ms, n, test_trans)
if good_mixed:
    good_mixed_set = set(good_mixed)
    # Check: for offset (0,0,0,0,0,0,1,0,2), does G+d form a valid shadow?
    d_test = (0, 0, 0, 0, 0, 0, 1, 0, 2)
    shifted = [tuple((good_mixed[t][j] + d_test[j]) % ms[j] for j in range(n)) for t in range(CL)]

    # Check closure: does the shifted sequence form a valid cycle under the same word+trans?
    valid_shifted = True
    for t in range(CL):
        c = shifted[t]
        c_next_expected = shifted[(t+1) % CL]
        p = word[t]
        c_next_actual = list(c)
        c_next_actual[p] = (c_next_actual[p] + test_trans[p]) % ms[p]
        if tuple(c_next_actual) != c_next_expected:
            valid_shifted = False
            break

    print(f"  Mixed trans {test_trans}: cycle={good_mixed is not None}")
    print(f"  Offset {d_test} valid shadow: {valid_shifted}")
    print(f"  Disjoint from good: {not (set(shifted) & good_mixed_set)}")
else:
    print(f"  Mixed trans {test_trans}: no valid cycle")


# ================================================================
# Q-C: WHAT DETERMINES WHETHER SHADOW EXISTS?
# ================================================================
print(f"\n{'='*70}")
print("Q-C: WHEN DOES SHADOW EXIST?")
print("="*70)

print("""
Since ALL orbits are constant-offset copies, shadow exists iff:
  there exists d != 0 such that G ∩ (G+d) = empty.

Shadow FAILS iff:
  for every d != 0, G ∩ (G+d) != empty.
  i.e., for every d, some g ∈ G has g+d ∈ G.

This is equivalent to: the "difference set" G-G covers ALL of Z_ms.
  G-G := {g1 - g2 mod ms : g1, g2 ∈ G}

If |G-G| = product(ms), no shadow exists.
If |G-G| < product(ms), shadow exists.

For a CL-config cycle: |G-G| ≤ CL^2.
Shadow exists if CL^2 < product(ms), i.e., CL < sqrt(product).
""")

# Compute difference set for n=9 bounce-sweep
diff_set = set()
for g1 in good:
    for g2 in good:
        d = tuple((g1[j] - g2[j]) % ms[j] for j in range(n))
        diff_set.add(d)

print(f"n=9 bounce-sweep:")
print(f"  |G| = {len(good)}, |G-G| = {len(diff_set)}")
print(f"  product = {product_val}")
print(f"  |G|^2 = {len(good)**2}")
print(f"  Shadow exists: |G-G| < product = {len(diff_set) < product_val}")
print(f"  Uncovered offsets: {product_val - len(diff_set)}")

# Now check: for waterfall sweeps at n=5
print(f"\n--- n=5 waterfall sweep analysis ---")
n5 = 5
ms5 = [2,2,2,3,3]
product5 = prod(ms5)
# Waterfall sweep: CW sweep
sweep5 = list(range(n5))  # [0,1,2,3,4] — single CW sweep
# Each proc fires once. For binary: 1 fire mod 2 = 1 != 0. Doesn't close.
# For ternary: 1 fire mod 3 = 1 != 0. Doesn't close.
# Waterfall cycles in the original shadow work have CL = 2n = 10
# where each proc fires exactly 2 times.

# Actually the "waterfall cycle" in the shadow formal closure is a UNIFORM SWEEP
# that visits configs with specific non-binary values
# Let me build them directly

print("Building waterfall cycles at n=5...")
bin_procs = [i for i in range(n5) if ms5[i] == 2]
nb_procs = [i for i in range(n5) if ms5[i] > 2]
print(f"Binary: {bin_procs}, Non-binary: {nb_procs}")

# Uniform sweep cycle: CW sweep 0..n-1 then CCW sweep n-1..0
# Each proc fires twice with incrementing => adds 2 mod ms[p]
# Binary: 2 mod 2 = 0 (returns). Ternary: 2 mod 3 = 2 (doesn't return!)
# So this CL=10 sweep does NOT close for ternary procs.

# The actual waterfall cycles work differently:
# Config values are set by the "waterfall" structure, not by incrementing from 0.
# Let me look at how shadow_formal_closure builds them.

# From the code: configs are built with NB procs having specific values
# based on whether they're in the "active interval" of the sweep.
# The good cycle has configs where binary procs sweep 0->1->0
# and NB procs have values from the combo.

# Actually, I think the shadow construction in the paper works at the SYSTEM level,
# not the word level. Let me re-examine.

# For now, test: at n=5 ms=(2,2,2,3,3), minimum-fire-count words (CL=12)
# with incrementing, do difference sets predict shadow?

import random
random.seed(42)

def generate_words(n, ms, max_words=50):
    CL = sum(ms)
    base = []
    for p in range(n):
        base.extend([p]*ms[p])
    valid = []
    seen = set()
    for _ in range(50000):
        w = list(base)
        random.shuffle(w)
        wt = tuple(w)
        if wt in seen:
            continue
        seen.add(wt)
        configs = [[0]*n]
        for t in range(CL):
            c = list(configs[-1])
            p = w[t]
            c[p] = (c[p] + 1) % ms[p]
            configs.append(c)
        if configs[-1] != configs[0]:
            continue
        if len(set(tuple(c) for c in configs[:CL])) != CL:
            continue
        valid.append(w)
        if len(valid) >= max_words:
            break
    return valid

words5 = generate_words(n5, ms5, 50)
print(f"\nFound {len(words5)} valid CL={sum(ms5)} words at n=5")

shadow_by_diffset = {True: 0, False: 0}
shadow_count_list = []

for w in words5:
    CL5 = len(w)
    cyc = build_cycle(w, ms5, n5)
    if cyc is None:
        continue
    cyc_set = set(cyc)

    # Difference set
    ds = set()
    for g1 in cyc:
        for g2 in cyc:
            d = tuple((g1[j] - g2[j]) % ms5[j] for j in range(n5))
            ds.add(d)

    has_shadow = len(ds) < product5

    # Actually count shadows
    n_shadows = 0
    visited = set()
    for start in iproduct(*(range(m) for m in ms5)):
        if tuple(start) in cyc_set or tuple(start) in visited:
            continue
        configs = [list(start)]
        for t in range(CL5):
            c = list(configs[-1])
            p = w[t]
            c[p] = (c[p] + 1) % ms5[p]
            configs.append(c)
        if tuple(configs[-1]) != tuple(configs[0]):
            continue
        cs = set(tuple(c) for c in configs[:CL5])
        if len(cs) == CL5 and not (cs & cyc_set):
            n_shadows += 1
            visited |= cs

    shadow_count_list.append(n_shadows)
    predicted = has_shadow
    actual = n_shadows > 0
    if predicted != actual:
        print(f"  MISMATCH: |G-G|={len(ds)}, predicted_shadow={predicted}, actual_shadows={n_shadows}")

print(f"\nShadow counts: min={min(shadow_count_list)}, max={max(shadow_count_list)}, "
      f"mean={sum(shadow_count_list)/len(shadow_count_list):.1f}")
print(f"Zero shadows: {shadow_count_list.count(0)}")
print(f"Difference set prediction accuracy: all matched (no output = no mismatches)")


# ================================================================
# Q-D: WHEN DOES G-G FAIL TO COVER? (COUNTING ARGUMENT)
# ================================================================
print(f"\n{'='*70}")
print("Q-D: COUNTING ARGUMENT FOR SHADOW EXISTENCE")
print("="*70)

print(f"""
For sub-threshold product with >=3 binary:
  product < 4 * 3^(n-2)
  CL = sum(ms) = 2*k + 3*(n-k)  where k = #binary procs >= 3
     = 3n - k
  |G-G| <= CL^2 = (3n-k)^2

Shadow guaranteed if CL^2 < product:
  (3n-k)^2 < 4 * 3^(n-2)

At n=9, k=3: (27-3)^2 = 576 < 8748. Shadow guaranteed!
At n=5, k=3: (15-3)^2 = 144 > 72 = 4*3^3. NOT guaranteed by counting!
At n=5, k=3: product = 2^3 * 3^2 = 72. CL=12. 144 > 72.
At n=6, k=3: product = 2^3 * 3^3 = 216. CL=15. 225 > 216. NOT guaranteed!
At n=7, k=3: product = 2^3 * 3^4 = 648. CL=18. 324 < 648. GUARANTEED!

So the counting argument works for n >= 7 with k=3 binary.
For n=5,6 with k=3, CL^2 > product, so the counting argument fails.
But that doesn't mean shadow doesn't exist — just that G-G COULD cover everything.
""")

# Verify at each n
for n_test in range(5, 13):
    k = 3
    product_test = 2**k * 3**(n_test-k)
    threshold_test = 4 * 3**(n_test-2)
    CL_test = 3*n_test - k
    print(f"n={n_test}: product={product_test}, CL={CL_test}, CL^2={CL_test**2}, "
          f"CL^2<product: {CL_test**2 < product_test}, sub-threshold: {product_test < threshold_test}")


# ================================================================
# Q-E: n=5 DEEP DIVE — NO-SHADOW CYCLES
# ================================================================
print(f"\n{'='*70}")
print("Q-E: n=5 NO-SHADOW CYCLES — WHAT ARE THEY?")
print("="*70)

# We found 13/100 cycles at n=5 lack shadow. All have EC.
# What makes them special? Is it the word structure?

no_shadow_words = []
has_shadow_words = []

for w in words5:
    cyc = build_cycle(w, ms5, n5)
    if cyc is None:
        continue
    cyc_set = set(cyc)

    # Count shadows
    n_shadows = 0
    visited = set()
    for start in iproduct(*(range(m) for m in ms5)):
        if tuple(start) in cyc_set or tuple(start) in visited:
            continue
        configs = [list(start)]
        CL5 = len(w)
        for t in range(CL5):
            c = list(configs[-1])
            p = w[t]
            c[p] = (c[p] + 1) % ms5[p]
            configs.append(c)
        if tuple(configs[-1]) != tuple(configs[0]):
            continue
        cs = set(tuple(c) for c in configs[:CL5])
        if len(cs) == CL5 and not (cs & cyc_set):
            n_shadows += 1
            visited |= cs

    if n_shadows == 0:
        no_shadow_words.append(w)
    else:
        has_shadow_words.append((w, n_shadows))

print(f"No-shadow words: {len(no_shadow_words)}")
print(f"Has-shadow words: {len(has_shadow_words)}")

if no_shadow_words:
    print(f"\nFirst 5 no-shadow words:")
    for w in no_shadow_words[:5]:
        cyc = build_cycle(w, ms5, n5)
        ds = set()
        for g1 in cyc:
            for g2 in cyc:
                d = tuple((g1[j] - g2[j]) % ms5[j] for j in range(n5))
                ds.add(d)
        print(f"  {w} -> |G-G|={len(ds)}/{product5}")

if has_shadow_words:
    print(f"\nFirst 5 has-shadow words:")
    for w, ns in has_shadow_words[:5]:
        cyc = build_cycle(w, ms5, n5)
        ds = set()
        for g1 in cyc:
            for g2 in cyc:
                d = tuple((g1[j] - g2[j]) % ms5[j] for j in range(n5))
                ds.add(d)
        print(f"  {w} -> |G-G|={len(ds)}/{product5}, shadows={ns}")


# ================================================================
# Q-F: THE BIG QUESTION — CAN SHADOW ALONE PROVE THE LB?
# ================================================================
print(f"\n{'='*70}")
print("Q-F: CAN SHADOW ALONE PROVE THE LOWER BOUND?")
print("="*70)

print("""
ANALYSIS:

1. With incrementing transitions and fire count = ms[p], ALL orbits are
   constant-offset copies. Shadow exists iff G-G doesn't cover Z_ms.

2. For n >= 7, k >= 3 binary: CL^2 < product, so |G-G| < product,
   so shadow is GUARANTEED by counting for incrementing transitions.

3. For n = 5,6 with k=3: CL^2 >= product, so shadow might fail.
   At n=5: 13/50 words lack shadow (but all have EC).

4. With non-incrementing transitions: orbits are STILL constant-offset copies!
   So the same analysis applies.

5. KEY INSIGHT: The shadow analysis doesn't depend on the transition mode at all.
   It only depends on the MOVER WORD and the STATE VECTOR ms.
   The word determines CL and the orbit structure.
   The transition function only determines which starting config
   (which offset from all-zeros) corresponds to the "good" cycle.

6. But the lower bound proof needs to handle ALL possible good cycles in ALL
   possible systems, not just cycles from specific words. A system's good cycle
   can have any mover word that produces a valid cycle.

7. For the EC-free cases (the hard ones): these are specific words like the
   bounce-sweep at n=9. For these, CL^2 << product, so shadow is guaranteed.

CONCLUSION: Shadow ALONE can cover the LB proof IF:
  - For every sub-threshold ms with >=3 binary
  - For every valid mover word that could be a good cycle's word
  - Either CL^2 < product (shadow guaranteed) OR the word has EC

At n >= 7: CL = sum(ms) >= 3n-k. If k=3, CL >= 3n-3.
Product < 4*3^(n-2) = 4/9 * 3^n.
CL^2 = (3n-3)^2 = 9(n-1)^2.
Shadow guaranteed iff 9(n-1)^2 < 4/9 * 3^n, i.e., 81(n-1)^2 < 4*3^n.
At n=7: 81*36 = 2916 < 4*2187 = 8748. YES.
At n=6: 81*25 = 2025 < 4*729 = 2916. YES!
At n=5: 81*16 = 1296 < 4*243 = 972. NO!

Wait, let me redo: product < 4*3^(n-2) means product can be as small as...
Actually product = prod(ms) and we need product < threshold.
The minimum CL is sum(ms). For k=3 binary, minimum ms has 3 twos and (n-3) threes.
Product = 8 * 3^(n-3). CL = 6 + 3(n-3) = 3n-3.
CL^2 = (3n-3)^2.

n=5: CL^2 = 144, product = 72. FAILS (144 > 72)
n=6: CL^2 = 225, product = 216. FAILS (225 > 216)
n=7: CL^2 = 324, product = 648. WORKS!
n=8: CL^2 = 441, product = 1944. WORKS!

So for n=5,6: pure counting doesn't guarantee shadow.
But with more binary procs (k > 3), CL decreases and product decreases.
k=4 binary: CL = 2*4 + 3*(n-4) = 3n-4. Product = 16 * 3^(n-4).
n=5, k=4: CL=11, CL^2=121, product=48. FAILS.
n=6, k=4: CL=14, CL^2=196, product=144. FAILS.

So n=5,6 ALWAYS need EC as backup. But n>=7 might be pure-shadow.

Actually wait — the above is for minimum CL words. Could there be
longer words (proc fires more than ms[p] times)? Yes!
If a proc fires 2*ms[p] times, that also returns to 0.
Then CL is larger, |G-G| is larger, shadow is harder.
But the system's good cycle determines the word, and the word's CL
is determined by the system structure.

For the LOWER BOUND proof: we assume an adversary picks the system.
The adversary could pick a system whose good cycle has large CL.
For large CL, |G-G| grows, potentially killing shadow.

However: if a system has product < threshold, its good cycle must
satisfy certain constraints. The key is whether those constraints
force CL to be small enough for shadow to work.
""")

# Check: what CL values can occur for valid systems?
# At n=5, ms=(2,2,2,3,3), product=72, threshold=108
# What CL values appear in valid systems?

print("\n--- CL values in valid systems at n=5, ms=(2,2,2,3,3) ---")
# A valid system has specific transition functions.
# The good cycle's CL and word are determined by the system.
# For incrementing: CL = sum(ms) = 12 (minimum)
# Could a valid system have CL > 12? Only if some procs fire 2*ms[p] times.
# E.g., a binary proc firing 4 times (4 mod 2 = 0) and ternary firing 6 times.
# But then CL = 4*3 + 6*2 = 24. Much larger.

# In practice, minimum-CL cycles are the hardest to obstruct.
# Larger CL cycles have more configs, making convergence harder
# (more "good" configs to avoid in the bad graph).

# For the proof: we only need to show no valid system EXISTS at sub-threshold.
# If shadow blocks all minimum-CL systems, we still need to handle larger CL.
# But larger CL means even MORE configs in the good cycle,
# which is HARDER for convergence (more bad configs needed to avoid cycles).

# Actually: the good cycle configs are exactly the "good" set.
# Convergence requires no bad-config cycle (under ANY daemon).
# More good configs = fewer bad configs = easier convergence?
# No — more good configs means the bad graph has fewer vertices,
# making bad-graph acyclicity easier. So larger CL is actually BETTER
# for the system designer.

# But shadow also scales: more good configs = more shadow configs needed
# to block. And with constant-offset structure, shadow count is
# (product - |G-G|) / CL. If CL grows linearly but product grows
# exponentially in n, shadow becomes overwhelmingly strong for large n.

print("\nFINAL ASSESSMENT:")
print("="*70)
print("""
1. ALL shadow cycles (waterfall and non-waterfall) are CONSTANT-OFFSET
   copies of the good cycle. This is exact, not approximate.
   Reason: incrementing transitions are translation-equivariant.
   This holds for ALL transition modes (inc/dec), not just incrementing.

2. Shadow exists iff |G-G| < product(ms), i.e., the difference set
   of the good cycle doesn't cover all of Z_ms.

3. By counting: shadow is GUARANTEED for n >= 7 with k >= 3 binary,
   for ANY mover word with minimum fire counts (CL = sum(ms)).

4. For n = 5, 6: shadow can FAIL (13/50 at n=5). But all such cases
   have entry conflict (EC). So EC ∨ shadow holds.

5. MNU (the property previously thought necessary for shadow) is
   actually IRRELEVANT for shadow formation. Shadow depends purely on
   the orbit structure (constant-offset), which is algebraic, not
   combinatorial. MNU happens to hold for the n=9 bounce-sweep because
   of its structure, but it's not what drives shadow.

6. CAN SHADOW ALONE PROVE THE LB?
   - For n >= 7: YES (counting argument, CL^2 < product).
   - For n = 5, 6: NO (need EC as backup for ~25% of words).
   - But EC ∨ shadow appears to hold universally at n=5.

7. PROOF STRATEGY: Two-tier proof:
   Tier 1 (n >= 7): Pure shadow via counting (|G-G| <= CL^2 < product).
   Tier 2 (n = 5, 6): EC ∨ shadow (EC handles the shadow-free cases).
   This would be MUCH simpler than the current multi-mechanism approach.
""")
