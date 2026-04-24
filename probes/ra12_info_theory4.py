"""
Information-Theoretic Analysis Part 4:
Focus on the context utilization crossover and the zero-error capacity interpretation.
"""

import math
from collections import defaultdict

def product(ms):
    p = 1
    for m in ms:
        p *= m
    return p

def table_capacity(ms):
    n = len(ms)
    total = 0
    for i in range(n):
        entries = ms[(i-1)%n] * ms[i] * ms[(i+1)%n]
        total += entries * math.log2(ms[i])
    return total

# ============================================================
# The key finding from Part 3: context utilization
# ============================================================

print("="*70)
print("CONTEXT UTILIZATION CROSSOVER ANALYSIS")
print("="*70)

print("""
CRITICAL OBSERVATION from Part 3:

Context utilization = (CL × n) / Σ_i(m_{i-1}·m_i·m_{i+1})
where CL = Σ m_i (good cycle length)

For the threshold multiset ms = (2, 3^(n-2), 2):
  CL = 3n - 4
  Σlocal = 27n - 48  (computed in Part 2)

  util = n(3n-4) / (27n-48) = (3n² - 4n) / (27n - 48)

As n→∞: util → 3n²/(27n) = n/9 → ∞

This means: at the threshold, utilization > 1 for n ≥ 8!
Contexts MUST be reused across good-cycle steps.
The system works despite this because:
  - Reuse at the SAME proc in the SAME role (both non-mover) is fine
  - Only mover↔non-mover overlap at the SAME proc is fatal

Let's compute the EXACT crossover.
""")

print(f"{'n':>3} {'util':>8} {'CL':>5} {'Σlocal':>7} {'n×CL':>7}")
print("-" * 40)
for n in range(3, 20):
    ms = [2] + [3]*(n-2) + [2]
    CL = sum(ms)
    total_local = sum(ms[(i-1)%n]*ms[i]*ms[(i+1)%n] for i in range(n))
    util = CL * n / total_local
    marker = " <-- util crosses 1" if 0.95 < util < 1.05 else ""
    print(f"{n:>3} {util:>8.4f} {CL:>5} {total_local:>7} {CL*n:>7}{marker}")

print("""
Utilization = 1 when n(3n-4) = 27n-48
  3n² - 4n = 27n - 48
  3n² - 31n + 48 = 0
  n = (31 ± √(961-576))/6 = (31 ± √385)/6 ≈ (31 ± 19.62)/6
  n ≈ 8.44  or  n ≈ 1.90

So util = 1 at n ≈ 8.44. For n ≥ 9 (where M_n = 4·3^(n-2)), util > 1!
""")


# ============================================================
# Sub-threshold context utilization
# ============================================================

print("\n" + "="*70)
print("SUB-THRESHOLD UTILIZATION CROSSOVER AT EACH n")
print("="*70)

print("""
For each n, find the product where util = 1.
At a given product P with multiset ms:
  util = n × CL / Σlocal

We know sub-threshold multisets have more binary procs.
Let's compare sub-threshold vs at-threshold for each n.
""")

def compute_util(ms):
    n = len(ms)
    CL = sum(ms)
    total_local = sum(ms[(i-1)%n]*ms[i]*ms[(i+1)%n] for i in range(n))
    return CL * n / total_local

# For n=5, sweep across multisets
print("n=5, various multisets:")
n5_cases = [
    [2,2,2,2,2],  # P=32
    [2,2,2,2,3],  # P=48
    [2,2,2,3,3],  # P=72
    [2,2,2,3,4],  # P=96 = M_5
    [2,2,3,3,3],  # P=108
    [2,3,3,3,3],  # P=162
    [3,3,3,3,3],  # P=243
]
print(f"  {'ms':>20} {'P':>6} {'util':>8} {'above_1':>8}")
for ms in n5_cases:
    P = product(ms)
    u = compute_util(ms)
    print(f"  {str(ms):>20} {P:>6} {u:>8.4f} {'YES' if u > 1 else 'no':>8}")


# ============================================================
# The deeper structure: per-proc mover/nonmover utilization
# ============================================================

print("\n\n" + "="*70)
print("PER-PROC MOVER/NONMOVER CONTEXT DENSITY")
print("="*70)

print("""
For proc i with state count m_i:
  - It fires m_i times in the good cycle (must visit all states)
  - It appears as non-mover CL - m_i times
  - Its local context space is L_i = m_{i-1} × m_i × m_{i+1}

  mover_density_i = m_i / L_i = 1 / (m_{i-1} × m_{i+1})
  nonmover_density_i = (CL - m_i) / L_i

  If mover_density + nonmover_density > 1, overlap is FORCED at proc i
  (by pigeonhole: distinct contexts < total appearances)

  BUT: distinct non-mover contexts ≤ L_i, and distinct mover contexts ≤ L_i.
  Overlap forced if: distinct_mover + distinct_nonmover > L_i

  Since distinct_mover ≤ m_i (at most m_i mover appearances, each could be unique),
  and distinct_nonmover ≤ min(CL - m_i, L_i),

  Overlap forced if: m_i + (CL - m_i) > L_i, i.e., CL > L_i
""")

print(f"{'n':>3} {'proc':>5} {'m_i':>4} {'L_i':>6} {'CL':>5} {'CL>L_i?':>8} {'ms':>25}")
print("-" * 65)

for n, ms in [
    (5, [2,2,2,2,2]),
    (5, [2,2,2,3,3]),
    (5, [2,2,2,3,4]),
    (5, [2,2,3,3,3]),
    (7, [2,2,2,3,3,3,4]),
    (9, [2,3,3,3,3,3,3,3,2]),
]:
    P = product(ms)
    CL = sum(ms)
    forced = False
    for i in range(n):
        L_i = ms[(i-1)%n]*ms[i]*ms[(i+1)%n]
        is_forced = CL > L_i
        if is_forced: forced = True
        print(f"{n:>3} {i:>5} {ms[i]:>4} {L_i:>6} {CL:>5} {'YES' if is_forced else 'no':>8} {str(ms):>25}")
    print(f"  → Overlap forced at any proc: {'YES' if forced else 'NO'}")
    print()

print("""
KEY FINDING: CL > L_i means that the total number of good-cycle appearances
at proc i EXCEEDS the number of distinct local contexts. By pigeonhole,
some context must appear as BOTH mover and non-mover → entry conflict.

But this is a NECESSARY condition for conflict, not sufficient.
The actual conflict requires the SAME context in both roles.
Distinct mover and non-mover appearances might use different contexts.

For sub-threshold all-binary (n=5, P=32): CL=10 > L_i=8 at ALL procs!
So overlap is FORCED at every processor.

For threshold (2,2,2,3,4) at n=5: CL=13 > 8 at proc 1, CL=13 > 12 at proc 2.
Still forced at binary procs!

Wait — but a valid system EXISTS at P=96. How?
Because CL > L_i forces context REUSE, but not necessarily mover↔nonmover overlap.
If the same context appears twice as non-mover, that's fine.

Actually, CL > L_i does force some context to appear in both mover and non-mover
at that proc, by simple counting:
  mover appearances = m_i (≥2)
  non-mover appearances = CL - m_i
  total = CL > L_i
So yes, some context must appear twice. But the two could both be non-mover.
We need: (distinct mover contexts) + (distinct non-mover contexts) > L_i.
Since distinct mover ≤ m_i and distinct non-mover ≤ CL - m_i, and these
could overlap with each other, we need a more careful analysis.

Actually: if ALL mover contexts are distinct AND all non-mover contexts
that overlap with mover contexts also appear as non-mover, then:
  #(contexts appearing only as mover) + #(contexts in both) + #(only non-mover) ≤ L_i
If some context appears as both → conflict.
If no context appears as both → distinct_mover + distinct_nonmover ≤ L_i
  → m_i + min(CL-m_i, L_i-m_i) ≤ L_i which is CL ≤ L_i.

So: CL > L_i IMPLIES there exists a context appearing as both mover and non-mover!
This IS the entry conflict!
""")

print("="*70)
print("PIGEON HOLE ENTRY CONFLICT: CL > L_i IMPLIES OVERLAP AT PROC i")
print("="*70)

print(f"\n{'n':>3} {'ms':>25} {'P':>8} {'CL':>5} {'min_L':>6} {'CL>min_L?':>10} {'status':>15}")
print("-" * 80)

all_results = []
for n, ms_list in [
    (4, [[2,2,2,2], [2,2,2,3], [2,2,3,3], [2,3,3,3], [3,3,3,3]]),
    (5, [[2,2,2,2,2], [2,2,2,2,3], [2,2,2,3,3], [2,2,2,3,4], [2,2,3,3,3],
         [2,3,3,3,3], [3,3,3,3,3]]),
    (7, [[2,2,2,2,2,2,2], [2,2,2,3,3,3,3], [2,2,2,3,3,3,4], [3,3,3,3,3,3,3]]),
    (9, [[2,2,2,3,3,3,3,3,3], [2,3,3,3,3,3,3,3,2], [3,3,3,3,3,3,3,3,3]]),
]:
    for ms in ms_list:
        P = product(ms)
        CL = sum(ms)
        L_values = [ms[(i-1)%n]*ms[i]*ms[(i+1)%n] for i in range(n)]
        min_L = min(L_values)
        has_conflict = CL > min_L

        if n <= 4: threshold = 4 * 3**(n-2)
        elif n <= 8: threshold = 32 * 3**(n-4)
        else: threshold = 4 * 3**(n-2)

        if P < threshold: status = "SUB-THRESH"
        elif P == threshold: status = "AT THRESH"
        else: status = "ABOVE"

        print(f"{n:>3} {str(ms):>25} {P:>8} {CL:>5} {min_L:>6} "
              f"{'YES→CONFLICT' if has_conflict else 'no':>10} {status:>15}")
        all_results.append((n, ms, P, CL, min_L, has_conflict, status))


# ============================================================
# THE REFINED QUESTION
# ============================================================

print("\n\n" + "="*70)
print("REFINED ANALYSIS: DOES CL > min_L PREDICT THE THRESHOLD?")
print("="*70)

print("""
The pigeonhole argument says: if CL > L_i for ANY proc i, then that proc
has an entry conflict, and the system is impossible.

So the necessary condition for feasibility is: CL ≤ L_i for ALL i.
i.e., Σ m_i ≤ min_i(m_{i-1} × m_i × m_{i+1})

For the threshold multiset (2,3,...,3,2):
  CL = 3n - 4
  min_L = min(12, 18, 27, ..., 27, 18, 12) = 12  (at the binary endpoints)

  CL ≤ 12 requires 3n - 4 ≤ 12, i.e., n ≤ 5.33

So for n ≥ 6, the pigeonhole argument says CL > min_L at the binary procs!
But valid systems EXIST for all n ≥ 9 with this multiset!

The resolution: the pigeonhole gives a NECESSARY condition for overlap at
a SINGLE proc, but the actual systems use clever good cycles where the
overlapping contexts at one proc are both in the non-mover role.

Wait — I proved above that CL > L_i implies overlap. Let me re-examine.

CL = total appearances (mover + non-mover) at proc i across all cycle steps.
L_i = number of distinct contexts at proc i.
CL > L_i → some context appears ≥ 2 times (by pigeonhole).
But both could be non-mover! The key question is whether some context
appears as BOTH mover AND non-mover.

More careful:
  mover appearances = m_i (proc fires exactly m_i times)
  non-mover appearances = CL - m_i

  Distinct mover contexts: each mover step has a unique context? Not necessarily!
  But each mover step transitions to a different state, and the mover's S value
  changes. Since the output must differ from S, and there are only m_i states...
  Actually each step where proc i fires, it transitions from state s to s'≠s.
  If we're on a good cycle visiting all m_i states, proc i fires in m_i distinct
  S values. But the (L,R) context could repeat.

  So distinct mover contexts ≤ m_i (one per firing, each with different S).
  Actually, the S values in mover appearances are all distinct (cycling through
  all m_i values), but L and R might not distinguish them.

  Distinct non-mover contexts ≤ CL - m_i.

  For overlap: we need some (L,S,R) that appears as mover AND as non-mover.

  If distinct_mover contexts ∩ distinct_nonmover contexts = ∅, then:
    |distinct_mover| + |distinct_nonmover| ≤ L_i
    m_i + |distinct_nonmover| ≤ L_i
    |distinct_nonmover| ≤ L_i - m_i

  The total non-mover appearances = CL - m_i ≤ |distinct_nonmover| only if
  each non-mover appearance uses a unique context. In general,
  |distinct_nonmover| ≤ CL - m_i (and could be much less due to repeats).

  So overlap-free requires: m_i + |distinct_nonmover| ≤ L_i.
  This is ALWAYS satisfiable as long as |distinct_nonmover| ≤ L_i - m_i,
  which is possible since |distinct_nonmover| ≤ L_i - m_i when the good
  cycle is designed to avoid mover contexts.

MY EARLIER CLAIM WAS WRONG. CL > L_i does NOT force mover↔nonmover overlap.
It only forces SOME context repetition, which could be all-nonmover repeats.
""")

# So what DOES force mover↔nonmover overlap?
print("="*70)
print("WHAT ACTUALLY FORCES ENTRY CONFLICT?")
print("="*70)

print("""
The entry conflict is forced when the SET of mover contexts and the SET of
non-mover contexts MUST intersect. This happens when:

  m_i + (CL - m_i - repeats_in_nonmover) > L_i

But the good cycle structure constrains which contexts CAN appear.
The mover contexts at proc i are determined by the sequence of configs
where proc i fires — specifically by (L, S, R) at those steps.

The key insight from the proved lower bound:
- For binary procs with 3 consecutive binary: Palindromic Entry Conflict
  forces overlap because the walk structure in binary-state space is
  too constrained
- For non-consecutive binary: Universal Entry Conflict via 4 mechanisms

These are STRUCTURAL results about walks on the state space,
not simple counting arguments.

FINAL ASSESSMENT:

The information-theoretic framing fails because:
1. Raw bit capacity is irrelevant (cap/P → 0 but systems still exist)
2. Simple pigeonhole doesn't capture the real constraint
3. The actual obstruction is about the STRUCTURE of walks in local
   state spaces, not about counting

The correct framework is COMBINATORIAL, not information-theoretic:
- The good cycle defines a walk on the product space
- The walk projects to local (L,S,R) walks at each processor
- The local walks must avoid certain patterns (entry conflicts)
- Sub-threshold state spaces force these patterns

The threshold 4·3^(n-2) is a COMBINATORIAL PACKING bound:
the minimum product where local walks can avoid entry conflicts
at all processors simultaneously.
""")
