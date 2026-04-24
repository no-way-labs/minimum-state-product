"""
Information-Theoretic Analysis Part 3:
1. Exhaustive at n=3 for multiple multisets (where feasible)
2. The correct information measure: log2(#valid / #total) per multiset
3. Overlap constraint analysis (the REAL obstruction)
4. Summary assessment
"""

import math
import itertools
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


def exhaustive_count(ms, max_combos=50_000_000):
    """Count valid self-stabilizing systems exhaustively."""
    n = len(ms)
    P = product(ms)

    # Check feasibility
    total_log = 0
    for i in range(n):
        entries = ms[(i-1)%n] * ms[i] * ms[(i+1)%n]
        total_log += entries * math.log2(ms[i])
    if total_log > math.log2(max_combos):
        return None, None, None  # too many

    # Generate all tables for each proc
    def gen_tables(i):
        m_L = ms[(i-1)%n]
        m_S = ms[i]
        m_R = ms[(i+1)%n]
        keys = [(L,S,R) for L in range(m_L) for S in range(m_S) for R in range(m_R)]
        tables = []
        for vals in itertools.product(range(m_S), repeat=len(keys)):
            tables.append(dict(zip(keys, vals)))
        return tables

    all_tables = [gen_tables(i) for i in range(n)]
    total_combos = 1
    for t in all_tables:
        total_combos *= len(t)

    if total_combos > max_combos:
        return None, None, None

    configs = list(itertools.product(*(range(m) for m in ms)))

    valid_count = 0
    fail_counts = defaultdict(int)

    # Iterate over all combinations
    def check_system(tables_list):
        # Compute privileges
        priv_map = {}
        for c in configs:
            priv = []
            for i in range(n):
                L = c[(i-1)%n]
                S = c[i]
                R = c[(i+1)%n]
                if tables_list[i][(L,S,R)] != S:
                    priv.append(i)
            priv_map[c] = priv

        # Liveness
        for c in configs:
            if not priv_map[c]:
                return False, 'liveness'

        good = set(c for c in configs if len(priv_map[c]) == 1)
        if not good:
            return False, 'no_good'

        # Closure
        for c in good:
            p = priv_map[c][0]
            c2 = list(c)
            c2[p] = tables_list[p][(c[(p-1)%n], c[p], c[(p+1)%n])]
            if tuple(c2) not in good:
                return False, 'closure'

        # Convergence
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
                    c2[p] = tables_list[p][(c[(p-1)%n], c[p], c[(p+1)%n])]
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
            c2[p] = tables_list[p][(c[(p-1)%n], c[p], c[(p+1)%n])]
            good_graph[c] = (tuple(c2), p)

        start = next(iter(good))
        visited = set()
        c = start
        for _ in range(len(good)+1):
            c2, p = good_graph[c]
            visited.add(p)
            c = c2
            if c == start: break
        if len(visited) < n:
            return False, 'fairness'

        return True, len(good)

    # Multi-proc iteration
    if n == 2:
        for t0 in all_tables[0]:
            for t1 in all_tables[1]:
                ok, info = check_system([t0, t1])
                if ok:
                    valid_count += 1
                else:
                    fail_counts[info] += 1
    elif n == 3:
        for idx0, t0 in enumerate(all_tables[0]):
            for t1 in all_tables[1]:
                for t2 in all_tables[2]:
                    ok, info = check_system([t0, t1, t2])
                    if ok:
                        valid_count += 1
                    else:
                        fail_counts[info] += 1
            if (idx0+1) % max(1, len(all_tables[0])//10) == 0:
                print(f"  {(idx0+1)/len(all_tables[0])*100:.0f}%...")
    else:
        # General case — too slow for large n
        for combo in itertools.product(*all_tables):
            ok, info = check_system(list(combo))
            if ok:
                valid_count += 1
            else:
                fail_counts[info] += 1

    return valid_count, total_combos, fail_counts


# ============================================================
# Exhaustive counts at n=3
# ============================================================

print("="*70)
print("EXHAUSTIVE SELF-STABILIZATION COUNTS")
print("="*70)

results = {}

# n=3 cases: ms=(2,2,2) → 2^24 ≈ 16M combos. Already done: 12843 valid.
# ms=(2,2,3) → 2^12 * 3^12 ≈ 2.2B. Too many.
# ms=(3,3,3) → 3^81 → way too many.

# Let's do n=2 cases (trivial ring)
print("\n--- n=2 ---")
for ms in [[2,2], [2,3], [3,3]]:
    n = len(ms)
    print(f"\nms={ms}, P={product(ms)}")
    v, t, f = exhaustive_count(ms)
    if v is not None:
        rate = v/t if t > 0 else 0
        info = -math.log2(rate) if rate > 0 else float('inf')
        cap = table_capacity(ms)
        print(f"  Valid: {v}/{t} = {rate:.8f}")
        print(f"  Info:  {info:.2f} bits")
        print(f"  Cap:   {cap:.1f} bits")
        print(f"  Fails: {dict(f)}")
        results[tuple(ms)] = (v, t, rate, info, cap)

# n=3, ms=(2,2,2): already computed, hardcode result
print("\n--- n=3, ms=(2,2,2) [from Part 2] ---")
v, t = 12843, 16777216
rate = v/t
info = -math.log2(rate)
cap = table_capacity([2,2,2])
print(f"  Valid: {v}/{t} = {rate:.8f}")
print(f"  Info:  {info:.2f} bits, Cap: {cap:.1f} bits, Cap/Info: {cap/info:.3f}")
results[(2,2,2)] = (v, t, rate, info, cap)


# ============================================================
# Key insight: overlap constraints
# ============================================================

print("\n\n" + "="*70)
print("THE OVERLAP CONSTRAINT — THE REAL OBSTRUCTION")
print("="*70)

print("""
The ACTUAL obstruction to self-stabilization is not just about bits.
It's about a STRUCTURAL constraint: the entry conflict (overlap).

When a processor's local context (L,S,R) appears in BOTH:
  - a mover position (proc should fire: f(L,S,R) ≠ S)
  - a non-mover position (proc should NOT fire: f(L,S,R) = S)
...in different configs of the same good cycle, there's a CONFLICT.

The table must satisfy f(L,S,R) ≠ S AND f(L,S,R) = S simultaneously.
This is impossible. It's not about bits — it's about CONTRADICTIONS.

The probability of conflict depends on:
  1. Good cycle length CL
  2. Number of distinct local contexts in mover vs non-mover roles
  3. Fan-out (more configs sharing contexts → more likely conflict)

Let's analyze this quantitatively.
""")

# For a good cycle of length CL on ring of n procs:
# Each step has 1 mover and n-1 non-movers.
# Total mover contexts = CL (one per step)
# Total non-mover contexts = CL × (n-1)
# If a context appears in both sets → conflict

print("--- Context collision analysis ---")
print(f"{'n':>3} {'ms':>25} {'P':>8} {'CL':>5} {'mover_ctx':>10} {'nonmover_ctx':>13} {'max_local':>10}")
print("-" * 85)

for n, ms in [
    (3, [2,2,2]),
    (3, [3,3,3]),
    (4, [2,2,2,2]),
    (4, [2,2,3,3]),
    (5, [2,2,2,2,2]),
    (5, [2,2,2,3,3]),
    (5, [2,2,2,3,4]),
    (5, [2,2,3,3,3]),
    (5, [3,3,3,3,3]),
    (7, [2,2,2,3,3,3,4]),
    (9, [2,3,3,3,3,3,3,3,2]),
]:
    P = product(ms)
    CL = sum(ms)
    mover_ctx = CL  # one mover per step
    nonmover_ctx = CL * (n-1)
    max_local = max(ms[(i-1)%n]*ms[i]*ms[(i+1)%n] for i in range(n))
    min_local = min(ms[(i-1)%n]*ms[i]*ms[(i+1)%n] for i in range(n))

    # Expected collision: birthday-paradox style
    # For a single proc i with L_i local contexts:
    # mover appearances at proc i ≈ CL/n (each proc fires CL/n ≈ m_i times)
    # non-mover appearances at proc i ≈ CL(n-1)/n
    # Collision prob ≈ 1 - (1 - m_i/L_i)^(something)... complex

    # Simpler: ratio of total contexts used to available
    total_local = sum(ms[(i-1)%n]*ms[i]*ms[(i+1)%n] for i in range(n))
    mover_frac = CL / total_local  # fraction of local space used by movers
    nonmover_frac = CL * (n-1) / total_local  # by non-movers

    print(f"{n:>3} {str(ms):>25} {P:>8} {CL:>5} {mover_ctx:>10} {nonmover_ctx:>13} "
          f"{max_local:>10}  mover_load={mover_frac:.3f} nonmover_load={nonmover_frac:.3f}")


# ============================================================
# The EXACT overlap measure for concrete systems
# ============================================================

print("\n\n" + "="*70)
print("GOOD CYCLE CONTEXT OVERLAP: CONCRETE EXAMPLES")
print("="*70)

# For a known valid system, check how contexts are distributed
# Using Dijkstra's Sol 3 at n=5: all procs ternary, f_0(L,S,R) = (S+1)%3 if S==L else S
# Actually, Sol 3 is f_i(L,S,R) = (S+1)%m if S==L else S for all i

def dijkstra_sol3(ms):
    """Dijkstra's Solution 3: f_i(L,S,R) = (S+1)%m_i if L==S else S."""
    n = len(ms)
    fs = []
    for i in range(n):
        m = ms[i]
        def make_f(m_i):
            return lambda L, S, R: (S+1) % m_i if L == S else S
        fs.append(make_f(m))
    return fs

# Analyze good cycle context distribution
def analyze_good_cycle_contexts(ms, fs):
    n = len(ms)
    P = product(ms)
    configs = list(itertools.product(*(range(m) for m in ms)))

    # Find good configs
    priv_map = {}
    for c in configs:
        priv = []
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            if fs[i](L,S,R) != S:
                priv.append(i)
        priv_map[c] = priv

    good = [c for c in configs if len(priv_map[c]) == 1]

    # Follow the good cycle
    good_set = set(good)
    good_graph = {}
    for c in good:
        p = priv_map[c][0]
        c2 = list(c)
        c2[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
        good_graph[c] = (tuple(c2), p)

    # Trace cycle — follow from a good config
    # The good configs form a permutation (each has exactly 1 successor in good)
    start = good[0]
    cycle = []
    movers = []
    c = start
    visited = set()
    for _ in range(len(good)+1):
        if c in visited:
            break
        if c not in good_graph:
            break
        visited.add(c)
        c2, p = good_graph[c]
        cycle.append(c)
        movers.append(p)
        c = c2

    CL = len(cycle)
    if CL == 0:
        print(f"  ms={ms}: No good cycle found!")
        return 0, None, None

    # For each proc, collect mover contexts and non-mover contexts
    per_proc_mover = defaultdict(set)    # proc -> set of (L,S,R) when mover
    per_proc_nonmover = defaultdict(set) # proc -> set of (L,S,R) when non-mover

    for step, (c, p) in enumerate(zip(cycle, movers)):
        for i in range(n):
            ctx = (c[(i-1)%n], c[i], c[(i+1)%n])
            if i == p:
                per_proc_mover[i].add(ctx)
            else:
                per_proc_nonmover[i].add(ctx)

    # Check overlaps
    total_overlap = 0
    print(f"\n  ms={ms}, CL={CL}, P={P}")
    for i in range(n):
        overlap = per_proc_mover[i] & per_proc_nonmover[i]
        local_size = ms[(i-1)%n]*ms[i]*ms[(i+1)%n]
        print(f"    Proc {i} (m={ms[i]}): mover_ctx={len(per_proc_mover[i])}, "
              f"nonmover_ctx={len(per_proc_nonmover[i])}, "
              f"local_space={local_size}, overlap={len(overlap)}")
        total_overlap += len(overlap)

    print(f"    Total context overlap: {total_overlap}")
    if total_overlap > 0:
        print(f"    WARNING: overlapping contexts found — system has conflicts!")
    else:
        print(f"    CLEAN: no context overlap — system is overlap-free")

    return CL, per_proc_mover, per_proc_nonmover


# Dijkstra Sol 3 at various sizes
for ms in [[3,3,3], [3,3,3,3], [3,3,3,3,3]]:
    fs = dijkstra_sol3(ms)
    analyze_good_cycle_contexts(ms, fs)


# ============================================================
# Context utilization at threshold
# ============================================================

print("\n\n" + "="*70)
print("CONTEXT UTILIZATION RATIO")
print("="*70)

print("""
For a good cycle of length CL, each step uses n local contexts (1 mover + n-1 non-mover).
Total context-uses = CL × n.
Available context slots = Σ_i (m_{i-1}·m_i·m_{i+1}).

Utilization = (CL × n) / Σ_i (m_{i-1}·m_i·m_{i+1})

If utilization > 1, the good cycle MUST reuse contexts → potential conflicts.
If utilization ≤ 1, it's possible (not guaranteed) to avoid conflicts.
""")

print(f"{'n':>3} {'ms':>25} {'P':>8} {'CL':>5} {'CL×n':>7} {'Σlocal':>7} {'util':>8} {'status':>15}")
print("-" * 90)

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
    (11, [2,3,3,3,3,3,3,3,3,3,2]),
]:
    P = product(ms)
    CL = sum(ms)
    total_uses = CL * n
    total_local = sum(ms[(i-1)%n]*ms[i]*ms[(i+1)%n] for i in range(n))
    util = total_uses / total_local

    # At threshold?
    if n <= 4:
        threshold = 4 * 3**(n-2)
    elif n <= 8:
        threshold = 32 * 3**(n-4)
    else:
        threshold = 4 * 3**(n-2)

    if P < threshold:
        status = "SUB-THRESH"
    elif P == threshold:
        status = "AT THRESH"
    else:
        status = "ABOVE"

    print(f"{n:>3} {str(ms):>25} {P:>8} {CL:>5} {total_uses:>7} {total_local:>7} "
          f"{util:>8.4f} {status:>15}")


# ============================================================
# The critical quantity: MOVER utilization per proc
# ============================================================

print("\n\n" + "="*70)
print("PER-PROC MOVER UTILIZATION")
print("="*70)

print("""
For proc i, it fires m_i times in the good cycle (since it must cycle through all states).
The local context space at proc i has m_{i-1}·m_i·m_{i+1} entries.
Mover utilization at proc i = m_i / (m_{i-1}·m_i·m_{i+1}) = 1/(m_{i-1}·m_{i+1})

This is the fraction of contexts that must be "fire" contexts.
The remaining (1 - that) must be "don't fire" contexts.

If mover_util + nonmover_util > 1, there MUST be overlap.
Nonmover_util at proc i = (CL - m_i) non-mover appearances / local_space
  but only the distinct contexts matter, not total appearances.
""")

print(f"{'n':>3} {'ms':>25} {'proc':>5} {'m_i':>4} {'local':>6} {'mover_frac':>11} {'nonmov_apps':>12}")
print("-" * 75)

for n, ms in [
    (5, [2,2,2,3,4]),
    (9, [2,3,3,3,3,3,3,3,2]),
]:
    P = product(ms)
    CL = sum(ms)
    for i in range(n):
        local = ms[(i-1)%n]*ms[i]*ms[(i+1)%n]
        mover_frac = ms[i] / local  # = 1/(m_{i-1}·m_{i+1})
        nonmov_appearances = CL - ms[i]
        print(f"{n:>3} {str(ms):>25} {i:>5} {ms[i]:>4} {local:>6} {mover_frac:>11.4f} {nonmov_appearances:>12}")
    print()


# ============================================================
# FINAL SUMMARY
# ============================================================

print("\n\n" + "="*70)
print("ASSESSMENT: DOES THE SHANNON FRAMING EXPLAIN THE THRESHOLD?")
print("="*70)

print("""
FINDINGS:

1. TABLE CAPACITY vs ROUTING INFORMATION:
   - Table capacity grows linearly in n: cap ≈ 42.8n bits
   - Config space grows exponentially: P = 4·3^(n-2)
   - Capacity/config → 0 exponentially: cap/P ≈ 42.8n / (4·3^(n-2))
   - The crude "routing info" measure (bad configs × log2(n)) also grows exponentially
   - Cap/Route ratio is well BELOW 1 at n≥5 for threshold multisets
     → The "channel" is always way too small in raw bits

   BUT THIS IS MISLEADING: Dijkstra's Sol 3 works with all-ternary (product=3^n),
   where cap/P is even WORSE. So raw capacity isn't the bottleneck.

2. THE REAL STORY: CONTEXT CONFLICTS (ENTRY CONFLICTS)
   The actual obstruction is STRUCTURAL, not informational:
   - A single table entry must be either "fire" or "don't fire"
   - If the same (L,S,R) context appears as both mover and non-mover
     across different good-cycle configs, the system is IMPOSSIBLE
   - This is a YES/NO constraint, not a capacity issue

   The threshold is where context conflicts become unavoidable:
   - Sub-threshold: EVERY good cycle has context conflicts at some proc
   - At/above threshold: context conflicts CAN be avoided

3. WHY THE ENTRY CONFLICT IS NOT REALLY ABOUT INFORMATION:
   - A binary proc's table has 1 bit per entry — but the constraint is
     "this entry must be 0 AND 1 simultaneously" (contradiction)
   - Adding more bits (larger m_i) doesn't help with the contradiction
   - What helps is having MORE CONTEXTS (larger m_{i-1}·m_i·m_{i+1})
     so that mover and non-mover appearances use DIFFERENT contexts

4. WHAT THE THRESHOLD OPTIMIZES:
   The threshold P* = 4·3^(n-2) is the minimum product where:
   - There exist ENOUGH distinct local contexts to separate
     mover from non-mover roles for ALL processors simultaneously
   - This is a COMBINATORIAL packing problem, not an information-theoretic one

5. INFORMATION-THEORETIC REFRAMING (partial):
   The context utilization ratio CL×n / Σlocal IS meaningful:
   - At threshold: CL×n / Σlocal ≈ 0.3-0.9 depending on n
   - This bounds the collision probability
   - But the actual obstruction is the STRUCTURED overlap (same proc,
     mover vs non-mover), not random collisions

VERDICT: The Shannon framing is SUGGESTIVE but NOT EXPLANATORY.
- The capacity ratio does decrease at sub-threshold, but it's below 1
  even at threshold and above
- The actual obstruction is entry conflicts (a combinatorial constraint),
  not channel capacity
- A better analogy might be ZERO-ERROR capacity (combinatorial coding)
  rather than Shannon capacity (probabilistic coding)
- The threshold is more like a combinatorial packing bound than a
  rate-distortion limit

The entry conflict obstruction IS information-theoretic in a sense:
it's about whether local information (3-tuples) can DISTINGUISH between
configs that need different treatment. But it's the ZERO-ERROR version
of the problem, not the probabilistic Shannon version.
""")

# One more data point: DOF/P scaling
print("\n--- Scaling summary ---")
print(f"{'n':>3} {'P*':>10} {'DOF/P':>10} {'cap/P':>10} {'CL/P(%)':>10} {'util':>8}")
print("-" * 55)
for n in range(3, 15):
    if n <= 4:
        if n == 3: ms = [3,3,3]
        else: ms = [2,2,3,3]
    elif n <= 8:
        ms = [2,2,2] + [3]*(n-4) + [4]
    else:
        ms = [2] + [3]*(n-2) + [2]

    P = product(ms)
    dof = sum(ms[(i-1)%n]*ms[i]*ms[(i+1)%n] for i in range(n))
    cap = table_capacity(ms)
    CL = sum(ms)
    total_local = dof  # same thing
    util = CL * n / total_local
    print(f"{n:>3} {P:>10} {dof/P:>10.4f} {cap/P:>10.4f} {CL/P*100:>10.4f} {util:>8.4f}")
