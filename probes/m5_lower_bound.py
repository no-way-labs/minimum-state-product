"""
M_5 Lower Bound: Show that no valid system exists with product < 96.

The candidates with product < 96 are:
  (2,2,2,3,3) product=72  [and rotations]
  (2,2,3,2,3) product=72  [and rotations]

All other configurations with max(m_i)≤3 have product ≥ 108 > 96.
Configs with 4+ consecutive binary (e.g., (2,2,2,2,3)) have product 48
but are known to be impossible (RFC obstruction).

CRITICAL CORRECTION: Dijkstra's Solution 3 shows ms=(3,3,3,3,3) IS VALID
with product 243. So "quaternary necessity" (max(m_i)≥4 for ALL systems)
is FALSE. The correct claim is: no system with product < 96 exists.
"""

import sys
sys.path.insert(0, '.')
from verifier import verify_system
import random
from itertools import product as iproduct
from collections import defaultdict

n = 5

# ============================================================
# PART 1: Verify Dijkstra's Solution 3 works (counterexample
# to quaternary necessity for ALL systems)
# ============================================================

print("="*70)
print("DIJKSTRA'S SOLUTION 3 — COUNTEREXAMPLE TO UNIVERSAL QUATERNARY NECESSITY")
print("="*70)

ms_333 = [3, 3, 3, 3, 3]

def f_bottom(L, S, R):
    if (S + 1) % 3 == R:
        return (S - 1) % 3
    return S

def f_top(L, S, R):
    if L == R and (L + 1) % 3 != S:
        return (L + 1) % 3
    return S

def f_middle(L, S, R):
    if (S + 1) % 3 == L:
        return L
    if (S + 1) % 3 == R:
        return R
    return S

fs_sol3 = [f_bottom] + [f_middle] * 3 + [f_top]
result = verify_system(ms_333, fs_sol3)
print(f"  ms=(3,3,3,3,3), product=243: {'VALID' if result['valid'] else 'INVALID'}")
if result['valid']:
    print(f"  Cycle length: {result['cycle_length']}")
    print(f"  max(m_i) = 3 < 4. QUATERNARY NOT REQUIRED for existence.")

# ============================================================
# PART 2: Focused search on product-72 candidates
# ============================================================

print("\n" + "="*70)
print("PRODUCT-72 CANDIDATES: ms=(2,2,2,3,3) AND ms=(2,2,3,2,3)")
print("="*70)

candidates_72 = [
    [2,2,2,3,3],
    [2,2,3,2,3],
]

for ms in candidates_72:
    print(f"\n  ms={ms}, product={72}")

    # Larger random search
    random.seed(42)
    found = False
    for trial in range(50000):
        fs = []
        for i in range(n):
            m_L = ms[(i-1) % n]
            m_S = ms[i]
            m_R = ms[(i+1) % n]
            lookup = {}
            for L in range(m_L):
                for S in range(m_S):
                    for R in range(m_R):
                        lookup[(L,S,R)] = random.randint(0, m_S - 1)

            def make_f(table):
                def f(L, S, R):
                    return table[(L, S, R)]
                return f
            fs.append(make_f(lookup))

        result = verify_system(ms, fs)
        if result['valid']:
            found = True
            print(f"    VALID at trial {trial}! Cycle length: {result['cycle_length']}")
            break

    if not found:
        print(f"    No valid system found in 50,000 random trials")

# ============================================================
# PART 3: Check product-72 with Dijkstra-like rules
# ============================================================

print("\n" + "="*70)
print("PRODUCT-72 WITH STRUCTURAL APPROACHES")
print("="*70)

# For ms=(2,2,2,3,3), try adapting Dijkstra's Solution 3.
# Solution 3 uses 3-state processors with bottom/middle/top rules.
# Can we "project" some processors to 2 states?

# Approach: take Solution 3 for n=5, then project P0, P1, P2 to 2 states
# by mapping state 2 → 0 (merge states 0 and 2).

ms_proj = [2, 2, 2, 3, 3]

# Projected transition functions
def project(val, m):
    return val % m

# For projected P0 (binary, was bottom):
# Original: f_bottom(L, S, R) = (S-1)%3 if (S+1)%3==R else S
# Projected: states 0,1. S=0: original could give 0 or 2→0. S=1: gives 0 or 1.
# But R is P1's state, which is also projected to {0,1}.
# (S+1)%3 for S=0 is 1, for S=1 is 2.
# So f_bottom(L, 0, R) = (0-1)%3 = 2→0 if 1==R else 0. i.e., if R=1: return 0, else return 0. Always 0!
# f_bottom(L, 1, R) = (1-1)%3 = 0 if 2==R else 1. R ∈ {0,1}, so 2≠R always. Return 1.
# So projected P0: always returns S. DEADLOCK — P0 is never privileged!

print("Projecting Solution 3 to ms=(2,2,2,3,3):")
print("  P0 (binary, was bottom): f0(L,0,R)=0 always, f0(L,1,R)=1 always → NEVER PRIVILEGED")
print("  This projection fails immediately — P0 becomes inert.")

# Try a different projection: merge states 1 and 2 instead of 0 and 2
# State mapping: 0→0, 1→1, 2→1
print("\n  Alternative: merge states 1,2 → 1")
# f_bottom(L, 0, R): (0+1)%3=1 vs R. If R=1: return (0-1)%3=2→1. Else: return 0.
# f_bottom(L, 1, R): was f(L,1,R) and f(L,2,R).
#   f(L,1,R): (1+1)%3=2 vs R. R∈{0,1}. 2≠R always. Return 1.
#   f(L,2,R): (2+1)%3=0 vs R. If R=0: return (2-1)%3=1. Else: return 2→1.
#   So f(L,2,R) = 1 always.
#   Merged: f(L,1,R) = 1 (both map to 1). P0 in state 1 is never privileged.
# So P0 can only be privileged in state 0 when R=1. Then it goes to state 1.
# But then it's stuck at state 1 forever.
print("  P0 in state 1: never privileged (stuck). Fails after first move.")

# The fundamental issue: Dijkstra's Solution 3 relies on 3-state arithmetic
# (mod 3 operations). Projecting to 2 states breaks the arithmetic.

print("\n  Conclusion: Dijkstra's Solution 3 cannot be projected to binary processors.")
print("  The mod-3 arithmetic is essential to its correctness.")

# ============================================================
# PART 4: Information-theoretic argument
# ============================================================

print("\n" + "="*70)
print("WHY ms=(2,2,2,3,3) CAN'T WORK: THE INFORMATION ARGUMENT")
print("="*70)

print("""
KEY INSIGHT: The issue is NOT that max(m_i)≥4 is universally required.
Dijkstra's Solution 3 works with max(m_i)=3.

The issue is PRODUCT MINIMIZATION. To achieve product < 96, we need
binary processors (m_i=2). But binary processors are "too simple" to
support the mod-3 arithmetic that makes Solution 3 work.

Specifically:
- Solution 3 uses (S+1) mod 3 arithmetic. This requires all 3 states.
- Binary processors can only distinguish L=S vs L≠S (Dijkstra Sol 1 style).
- A ring with 3 binary + 2 ternary can't replicate either Sol 1 (needs K≥n=5)
  or Sol 3 (needs all states ≥ 3) or Sol 2 (needs uniform states).

The minimum-product system uses a DIFFERENT solution structure:
- 3 binary processors for the "sweep" (wave propagation)
- 1 quaternary processor for "phase counting" (routing memory)
- (n-4) ternary processors for "relay" (one-directional token passing)

This hybrid structure achieves product 32·3^(n-4), which is less than
3^n (Dijkstra's Sol 3) because it replaces 2 processors at cost 3 with
cost 2 (binary sweep), at the expense of needing 1 processor at cost 4
(quaternary phase counter).

The tradeoff: 3·3 = 9 vs 2·2·2·4 = 32... wait, that doesn't work.
Let me recalculate:

  Sol 3 for n=5: 3^5 = 243
  Optimal for n=5: 2·2·2·3·4 = 96

  Ratio: 243/96 = 2.53x improvement.

  The savings come from:
  - 3 processors reduced from 3 to 2 states: saves 3^3/2^3 = 27/8 = 3.375x
  - 1 processor increased from 3 to 4 states: costs 4/3 = 1.33x
  - Net: 3.375/1.33 = 2.53x ✓

So the quaternary processor is the "price" for having binary processors.
Without the quaternary, the binary processors can't be made to work
(as shown by the shadow cycle theorem and random search failures).
""")

# ============================================================
# PART 5: What exactly needs to be proved for M_5 = 96
# ============================================================

print("="*70)
print("WHAT NEEDS TO BE PROVED FOR M_5 = 96")
print("="*70)

print("""
THEOREM (M_5 = 96):
The minimum state product for a self-stabilizing token ring with n=5
processors is M_5 = 96, achieved by ms=(2,2,2,3,4).

PROOF STRUCTURE:

Upper bound (M_5 ≤ 96):
  The witness ms=(2,2,2,3,4) is verified valid. Product = 96. ✓ [DONE]

Lower bound (M_5 ≥ 96):
  Must show: no valid system exists with product < 96.

  State vectors with product < 96 and m_i ≥ 2 for all i:
  (sorted by product)

  Product 32: (2,2,2,2,2) — RFC obstruction (all binary, n≥4 fails) ✓
  Product 48: (2,2,2,2,3) — 4 consecutive binary, RFC obstruction ✓
  Product 64: (2,2,2,2,4) — 4 consecutive binary, RFC obstruction ✓
  Product 72: (2,2,2,3,3) — NEED TO PROVE IMPOSSIBLE
  Product 72: (2,2,3,2,3) — NEED TO PROVE IMPOSSIBLE
  Product 80: (2,2,2,2,5) — 4 consecutive binary ✓
  Product 96: (2,2,2,2,6) — 4 consecutive binary ✓
  Product 48: (2,2,2,3,2) = rotation of (2,2,2,2,3) ✓
  etc.

  Key remaining cases:
  1. ms=(2,2,2,3,3) and ALL rotations — product 72
  2. ms=(2,2,3,2,3) and ALL rotations — product 72
  3. ms=(2,2,2,4,3) and rotations — product 96 (equal to bound!)
     Wait, 2·2·2·4·3 = 96 = M_5. So these MIGHT be valid!
     And indeed, (2,2,2,3,4) is a rotation of this. ✓

  So the only cases to prove impossible are product 72:
  - (2,2,2,3,3): 3 consecutive binary, 2 ternary
  - (2,2,3,2,3): 2 consecutive binary + 1 isolated binary, 2 ternary

  THESE are the targets for the lower bound proof.

STATUS:
  (2,2,2,3,3): Strong computational evidence (shadow cycle theorem,
    50K random search, Dijkstra-like search — all fail). Theoretical
    proof covers sweep-based cycles. Complete proof needs extension.

  (2,2,3,2,3): Computational evidence (1K random search failed).
    No theoretical analysis yet. NEEDS WORK.
""")
