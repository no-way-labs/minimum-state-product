"""
Information-Theoretic Analysis Part 2:
1. Exhaustive enumeration at n=3 (feasible: 2^24 = 16M for all-binary)
2. Better information-theoretic measures
3. The real bottleneck: entries/configs ratio analysis
4. Analytical capacity formula
"""

import math
import itertools
import random
from collections import defaultdict

random.seed(42)

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
# Part A: Analytical formulas for key quantities
# ============================================================

print("="*70)
print("ANALYTICAL INFORMATION-THEORETIC FRAMEWORK")
print("="*70)

print("\n--- Key Formula ---")
print("Table capacity C = Σ_i  m_{i-1} · m_i · m_{i+1} · log2(m_i)  bits")
print("Config space   P = Π m_i")
print("Entries/config = C / (P · avg_log2_m)")
print("                = Σ_i (m_{i-1}·m_i·m_{i+1}) / P")
print("                = Σ_i 1/R_i  where R_i = P/(m_{i-1}·m_i·m_{i+1})")

print("\n--- For homogeneous ms = (k,k,...,k) ---")
for k in [2,3,4]:
    for n in [3,4,5,7,9]:
        P = k**n
        entries = n * k**3
        cap = entries * math.log2(k)
        ratio = entries / P  # = n * k^3 / k^n = n / k^(n-3)
        fanout = k**(n-3)
        print(f"  k={k}, n={n}: P={P:>8}, entries={entries:>6}, cap={cap:>8.1f} bits, "
              f"entries/P={ratio:.4f}, fanout={fanout}")

print("\n--- For threshold ms at n≥9: (2,3,...,3,2) ---")
for n in range(5, 15):
    # ms = (2, 3, ..., 3, 2) with n-2 ternary procs
    ms = [2] + [3]*(n-2) + [2]
    P = product(ms)
    threshold = 4 * 3**(n-2)

    cap = table_capacity(ms)

    # Entries breakdown:
    # Proc 0 (m=2): L=ms[n-1]=2, S=2, R=ms[1]=3 → entries=2·2·3=12
    # Proc 1 (m=3): L=ms[0]=2, S=3, R=ms[2]=3 → entries=2·3·3=18
    # Proc i (m=3, 2≤i≤n-3): L=3, S=3, R=3 → entries=27
    # Proc n-2 (m=3): L=3, S=3, R=2 → entries=18
    # Proc n-1 (m=2): L=3, S=2, R=2 → entries=12

    entries_total = 12 + 18 + 27*(n-4) + 18 + 12  # for n≥5
    if n >= 5:
        entries_formula = 60 + 27*(n-4)  # = 27n - 48

    print(f"  n={n:>2}: P={P:>10} = {threshold:>10}, cap={cap:>10.1f} bits, "
          f"entries={entries_total:>5}, entries/P={entries_total/P:.6f}, "
          f"cap/P={cap/P:.4f}")


# ============================================================
# Part B: The REAL information bottleneck
# ============================================================

print("\n\n" + "="*70)
print("THE REAL BOTTLENECK: LOCAL vs GLOBAL CONTROL")
print("="*70)

print("""
Each table entry at proc i controls ALL configs with that local (L,S,R) pattern.
This is the fundamental tension:
  - The transition function must be LOCALLY determined (one output per (L,S,R))
  - But convergence is a GLOBAL property (all paths through config space reach good cycle)

The fan-out = P / (local pattern count at proc i) = number of configs sharing one local pattern.
When fan-out is large, one table entry must handle many different configs identically.

KEY INSIGHT: At proc i, the table has m_{i-1}·m_i·m_{i+1} entries.
But each entry must work correctly for P/(m_{i-1}·m_i·m_{i+1}) different configs.
The entry doesn't KNOW which of those configs it's in — it only sees (L,S,R).

This is exactly a rate-distortion problem:
  - Source: config space (P possible configs)
  - Encoder: local view (L,S,R) — loses information about distant procs
  - The "distortion" is: does the transition lead toward the good cycle?
""")

# Compute how much information is LOST by each processor's local view
print("--- Information loss per processor ---")
print(f"{'n':>3} {'ms':>20} {'P':>8} {'proc':>5} {'local_view':>12} {'info_lost':>12} {'bits_available':>15}")
print("-" * 85)

test_cases = [
    (5, [2,2,2,3,3]),
    (5, [2,2,2,3,4]),
    (5, [2,2,3,3,3]),
    (7, [2,2,2,3,3,3,4]),
    (9, [2,3,3,3,3,3,3,3,2]),
]

for n, ms in test_cases:
    P = product(ms)
    for i in range(n):
        local = ms[(i-1)%n] * ms[i] * ms[(i+1)%n]
        info_total = math.log2(P)
        info_local = math.log2(local)
        info_lost = info_total - info_local
        bits_avail = local * math.log2(ms[i])
        print(f"{n:>3} {str(ms):>20} {P:>8} {i:>5} {local:>12} "
              f"{info_lost:>12.2f} {bits_avail:>15.1f}")
    print()


# ============================================================
# Part C: Exhaustive at n=3 all-binary
# ============================================================

print("\n" + "="*70)
print("EXHAUSTIVE ENUMERATION: n=3, ms=(2,2,2), P=8")
print("="*70)

def check_ss_n3(ms, tables):
    """Check self-stabilization for n=3 with given table dicts."""
    n = 3
    P = product(ms)
    configs = list(itertools.product(*(range(m) for m in ms)))

    def f(i, L, S, R):
        return tables[i][(L, S, R)]

    priv_map = {}
    for c in configs:
        priv = []
        for i in range(n):
            L = c[(i-1)%n]
            S = c[i]
            R = c[(i+1)%n]
            if f(i, L, S, R) != S:
                priv.append(i)
        priv_map[c] = priv

    # Liveness
    for c in configs:
        if not priv_map[c]:
            return False, 'liveness'

    # Good configs
    good = set(c for c in configs if len(priv_map[c]) == 1)
    if not good:
        return False, 'no_good'

    # Closure
    for c in good:
        p = priv_map[c][0]
        c2 = list(c)
        c2[p] = f(p, c[(p-1)%n], c[p], c[(p+1)%n])
        if tuple(c2) not in good:
            return False, 'closure'

    # Convergence (attractor)
    bad = set(configs) - good
    levels = {c: 0 for c in good}
    remaining = set(bad)
    changed = True
    while changed and remaining:
        changed = False
        new_level = set()
        for c in list(remaining):
            all_ok = True
            for p in priv_map[c]:
                c2 = list(c)
                c2[p] = f(p, c[(p-1)%n], c[p], c[(p+1)%n])
                if tuple(c2) not in levels:
                    all_ok = False
                    break
            if all_ok:
                new_level.add(c)
                changed = True
        for c in new_level:
            levels[c] = 1
            remaining.remove(c)

    if remaining:
        return False, 'convergence'

    # Fairness
    good_graph = {}
    for c in good:
        p = priv_map[c][0]
        c2 = list(c)
        c2[p] = f(p, c[(p-1)%n], c[p], c[(p+1)%n])
        good_graph[c] = (tuple(c2), p)

    start = next(iter(good))
    visited_procs = set()
    c = start
    for _ in range(len(good) + 1):
        c2, p = good_graph[c]
        visited_procs.add(p)
        c = c2
        if c == start:
            break

    if len(visited_procs) < n:
        return False, 'fairness'

    return True, len(good)


# n=3, ms=(2,2,2): each proc has 2^3=8 entries, each binary.
# Total: 3 procs × 2^8 = 768 tables per proc. Total combos: 256^3 ≈ 16M.
# Actually each proc table: 8 entries, each 0 or 1 → 2^8 = 256 possible tables.
# Total: 256^3 = 16,777,216 combos. Feasible!

ms = [2, 2, 2]
n = 3

print(f"\nEnumerating all {256**3:,} transition function combinations...")
print(f"ms = {ms}, P = {product(ms)}")

# Generate all possible tables for each proc
def gen_all_tables(m_L, m_S, m_R):
    keys = [(L, S, R) for L in range(m_L) for S in range(m_S) for R in range(m_R)]
    n_entries = len(keys)
    tables = []
    for vals in itertools.product(range(m_S), repeat=n_entries):
        t = dict(zip(keys, vals))
        tables.append(t)
    return tables

all_tables_0 = gen_all_tables(ms[2], ms[0], ms[1])  # L=proc n-1, S=proc 0, R=proc 1
all_tables_1 = gen_all_tables(ms[0], ms[1], ms[2])
all_tables_2 = gen_all_tables(ms[1], ms[2], ms[0])

print(f"Tables per proc: {len(all_tables_0)}")

valid_count = 0
valid_good_sizes = defaultdict(int)
fail_counts = defaultdict(int)

total = len(all_tables_0) * len(all_tables_1) * len(all_tables_2)
check_interval = total // 20

for idx0, t0 in enumerate(all_tables_0):
    for idx1, t1 in enumerate(all_tables_1):
        for idx2, t2 in enumerate(all_tables_2):
            is_valid, info = check_ss_n3(ms, [t0, t1, t2])
            if is_valid:
                valid_count += 1
                valid_good_sizes[info] += 1
            else:
                fail_counts[info] += 1

    if (idx0 + 1) % 16 == 0:
        pct = (idx0 + 1) / len(all_tables_0) * 100
        print(f"  {pct:.0f}% done, {valid_count} valid so far...")

total_combos = total
rate = valid_count / total_combos
info_bits = -math.log2(rate) if rate > 0 else float('inf')
cap = table_capacity(ms)

print(f"\nResults:")
print(f"  Total combinations:  {total_combos:,}")
print(f"  Valid systems:       {valid_count}")
print(f"  Rate:                {rate:.8f} = 1/{1/rate:.0f}" if rate > 0 else "  Rate: 0")
print(f"  Information content: {info_bits:.2f} bits" if info_bits < float('inf') else "  Info: inf")
print(f"  Table capacity:      {cap:.1f} bits")
print(f"  Cap / Info:          {cap / info_bits:.3f}" if info_bits < float('inf') else "  Cap/Info: N/A")
print(f"  Good cycle sizes:    {dict(valid_good_sizes)}")
print(f"  Failure breakdown:   {dict(fail_counts)}")


# ============================================================
# Part D: Scaling analysis — the key formula
# ============================================================

print("\n\n" + "="*70)
print("SCALING ANALYSIS: ENTRIES/CONFIGS vs n")
print("="*70)

print("""
For ms = (2, 3^(n-2), 2):
  P = 4 · 3^(n-2)
  Total entries = 2·12 + 2·18 + (n-4)·27 = 60 + 27(n-4) = 27n - 48
  Entries/P = (27n - 48) / (4 · 3^(n-2))

This ratio → 0 exponentially fast!
As n grows, each table entry must handle exponentially more configs.

The "channel rate" = cap / P = Σ(entries_i · log2(m_i)) / P
For the threshold multiset:
  cap = 2·12·1 + 2·18·log2(3) + (n-4)·27·log2(3)
      = 24 + 36·log2(3) + 27(n-4)·log2(3)
      = 24 + (27n - 72)·log2(3)
      ≈ 42.8n - 90.1  (for large n)

  Rate = cap/P ≈ 42.8n / (4·3^(n-2)) → 0 exponentially
""")

print(f"{'n':>3} {'P':>10} {'entries':>8} {'cap':>10} {'entries/P':>12} {'cap/P':>10} {'log2(P)':>8}")
print("-" * 72)
for n in range(3, 20):
    ms = [2] + [3]*(n-2) + [2]
    P = product(ms)
    cap = table_capacity(ms)
    entries = sum(ms[(i-1)%n]*ms[i]*ms[(i+1)%n] for i in range(n))
    print(f"{n:>3} {P:>10} {entries:>8} {cap:>10.1f} {entries/P:>12.6f} {cap/P:>10.4f} {math.log2(P):>8.2f}")


# ============================================================
# Part E: The dual view — what does the threshold optimize?
# ============================================================

print("\n\n" + "="*70)
print("WHAT DOES THE THRESHOLD OPTIMIZE?")
print("="*70)

print("""
The threshold P* = 4·3^(n-2) is the minimum product for which self-stabilization is possible.
Let's look at what's special about this point.

For a system with n procs, product P, we need:
1. A good cycle of length CL (= Σ m_i by closure)
2. Convergence: every bad config eventually reaches good cycle under any daemon

The good cycle uses CL configs out of P total.
The remaining P - CL configs must all have a "routing" to the good cycle.

For ms = (2,3,...,3,2), CL = 2+3(n-2)+2 = 3n-4.
Fraction good = CL/P = (3n-4)/(4·3^(n-2)) → 0.
""")

print(f"{'n':>3} {'P':>10} {'CL':>6} {'bad':>10} {'CL/P(%)':>10} {'fanout_max':>12}")
print("-" * 55)
for n in range(3, 15):
    ms = [2] + [3]*(n-2) + [2]
    P = product(ms)
    CL = sum(ms)
    bad = P - CL
    fanout_max = max(P // (ms[(i-1)%n]*ms[i]*ms[(i+1)%n]) for i in range(n))
    print(f"{n:>3} {P:>10} {CL:>6} {bad:>10} {CL/P*100:>10.4f} {fanout_max:>12}")

# ============================================================
# Part F: Binary bottleneck analysis
# ============================================================

print("\n\n" + "="*70)
print("BINARY PROCESSOR BOTTLENECK")
print("="*70)

print("""
A binary proc (m=2) can only output 0 or 1.
Its transition table is a boolean function of (L,S,R).
The MAXIMUM information per entry is 1 bit.

But to route configs correctly, the proc needs to distinguish between
fan-out many configs that share the same (L,S,R).

The proc CANNOT distinguish them — it must give the SAME output.
This means: for each (L,S,R), all configs with that local pattern
either ALL fire this proc, or NONE do.

This is the locality constraint. The question is:
Can we partition configs into "fire" and "don't fire" using only local views,
such that convergence is guaranteed?

The number of "routing decisions" per table entry = fan-out.
For a binary proc, 1 bit must route fan-out configs.
""")

print("Binary proc fan-out at threshold:")
for n in range(5, 15):
    ms = [2] + [3]*(n-2) + [2]
    P = product(ms)
    # Binary procs are at positions 0 and n-1
    for pos in [0, n-1]:
        local = ms[(pos-1)%n] * ms[pos] * ms[(pos+1)%n]
        fanout = P // local
        bits = math.log2(ms[pos])
        print(f"  n={n:>2}, proc {pos:>2} (m={ms[pos]}): fanout={fanout:>8}, "
              f"bits/entry={bits:.3f}, bits/config={bits/fanout:.6f}")


# ============================================================
# Part G: Alternative capacity measure — counting constraints
# ============================================================

print("\n\n" + "="*70)
print("CONSTRAINT COUNTING: DEGREES OF FREEDOM vs CONSTRAINTS")
print("="*70)

print("""
Alternative view: count degrees of freedom (DOF) vs constraints.

DOF = number of independent table entries = Σ_i m_{i-1}·m_i·m_{i+1}
     (each entry is a free choice)

Constraints for self-stabilization:
- Good cycle: CL configs must have exactly 1 privileged proc
  → CL constraints on which procs fire
- Closure: successor of each good config is in good cycle
  → CL constraints on transition values
- Convergence: no bad cycle under any daemon
  → at least P - CL constraints (each bad config must have "progress")

Total min constraints ≈ 2·CL + (P - CL) = P + CL

If DOF < constraints, system is over-determined → likely impossible.
If DOF ≥ constraints, system might be feasible.
""")

print(f"{'n':>3} {'ms':>20} {'P':>8} {'DOF':>6} {'CL':>5} {'P+CL':>8} {'DOF/(P+CL)':>12}")
print("-" * 70)

for n, ms in [
    (3, [2,2,2]),
    (3, [3,3,3]),
    (4, [2,2,2,2]),
    (4, [2,2,3,3]),
    (5, [2,2,2,2,2]),
    (5, [2,2,2,2,3]),
    (5, [2,2,2,3,3]),
    (5, [2,2,2,3,4]),
    (5, [2,2,3,3,3]),
    (5, [3,3,3,3,3]),
    (7, [2,2,2,3,3,3,4]),
    (9, [2,3,3,3,3,3,3,3,2]),
]:
    P = product(ms)
    dof = sum(ms[(i-1)%n]*ms[i]*ms[(i+1)%n] for i in range(n))
    CL = sum(ms)
    constraints = P + CL
    ratio = dof / constraints
    print(f"{n:>3} {str(ms):>20} {P:>8} {dof:>6} {CL:>5} {constraints:>8} {ratio:>12.4f}")


# ============================================================
# Part H: The product-split optimization
# ============================================================

print("\n\n" + "="*70)
print("OPTIMAL PRODUCT SPLIT: MAXIMIZE DOF/CONSTRAINTS FOR FIXED P")
print("="*70)

print("""
For fixed product P and fixed n, which multiset maximizes DOF/(P+CL)?

DOF = Σ m_{i-1}·m_i·m_{i+1}
CL = Σ m_i

For fixed P = Π m_i, we want to maximize Σ m_{i-1}·m_i·m_{i+1}.

By AM-GM or similar: the SUM of triple-products on a ring is maximized
when the state counts are as UNEQUAL as possible (concentrate mass).
But P is fixed, so we can't just make one huge.

Interesting: the threshold multiset (2,3,...,3,2) has many ternary and
only two binary. Does it maximize DOF for its product?
""")

# For n=5, compare all multisets with P=96
print("n=5, P=96: all multisets")
from itertools import combinations_with_replacement

def partitions_with_product(target, n, min_val=2, max_val=None):
    """Find all sorted multisets of length n with product = target."""
    if max_val is None:
        max_val = target
    results = []

    def backtrack(remaining_product, remaining_n, min_v, current):
        if remaining_n == 0:
            if remaining_product == 1:
                results.append(tuple(current))
            return
        for v in range(min_v, min(remaining_product, max_val) + 1):
            if remaining_product % v == 0:
                backtrack(remaining_product // v, remaining_n - 1, v, current + [v])

    backtrack(target, n, min_val, [])
    return results

for target_P in [72, 96, 108]:
    parts = partitions_with_product(target_P, 5, 2, target_P)
    if parts:
        print(f"\n  P={target_P}:")
        for ms_tuple in parts:
            ms = list(ms_tuple)
            n = len(ms)
            P = product(ms)
            dof = sum(ms[(i-1)%n]*ms[i]*ms[(i+1)%n] for i in range(n))
            CL = sum(ms)
            cap = table_capacity(ms)
            print(f"    {ms}: DOF={dof}, CL={CL}, DOF/(P+CL)={dof/(P+CL):.4f}, cap={cap:.1f}")


# ============================================================
# Part I: The critical ratio
# ============================================================

print("\n\n" + "="*70)
print("THE CRITICAL RATIO: DOF/P at threshold")
print("="*70)

print(f"{'n':>3} {'P*':>10} {'DOF':>8} {'DOF/P':>10} {'DOF/P*n':>10}")
print("-" * 50)
for n in range(3, 20):
    if n <= 4:
        P_star = 4 * 3**(n-2)
        if n == 3: ms = [3,3,3]
        else: ms = [2,2,3,3]
    elif n <= 8:
        P_star = 32 * 3**(n-4)
        ms = [2,2,2] + [3]*(n-4) + [4]
    else:
        P_star = 4 * 3**(n-2)
        ms = [2] + [3]*(n-2) + [2]

    P = product(ms)
    dof = sum(ms[(i-1)%n]*ms[i]*ms[(i+1)%n] for i in range(n))
    print(f"{n:>3} {P:>10} {dof:>8} {dof/P:>10.4f} {dof/(P*n):>10.6f}")
