"""
Script 4: The killing argument — identify the exact obstruction.

Key question: WHY is no-EC + hfull impossible at sufficient n?

Approach:
1. For each processor p with fire count fc_p, it uses fc_p mover contexts and
   (CL - fc_p) non-mover contexts. These context triples must be DISJOINT
   (no triple can appear as both mover and non-mover for the same proc).

2. The total number of distinct context triples for proc p is bounded by
   m_{p-1} * m_p * m_{p+1} (product of neighbor state sizes).

3. So we need: (distinct mover contexts) + (distinct non-mover contexts)
   <= m_{p-1} * m_p * m_{p+1}.

4. But actually it's tighter: the non-mover contexts where f(L,S,R)=S must
   NOT overlap with mover contexts where f(L,S,R)=S'!=S.

Let's quantify this precisely.
"""

from collections import Counter, defaultdict
from itertools import product as iprod, combinations
import random
from math import prod

def ring_adj(a, b, n):
    return min(abs(a-b), n-abs(a-b)) <= 1

def context_space_size(p, n, ms):
    """Number of possible (L, S, R) triples for processor p."""
    return ms[(p-1) % n] * ms[p] * ms[(p+1) % n]

def analyze_context_budget(n, ms, walk):
    """
    For each processor, analyze the context budget.

    Key insight: at each step i, processor p has context (L_i, S_i, R_i).
    - If p is mover: needs f(L,S,R) = S' != S. This "uses" the context (L,S,R) for transition.
    - If p is non-mover: needs f(L,S,R) = S. This "uses" the context for identity.

    NO-EC means: no context (L,S,R) appears as both mover (requiring S'!=S) and non-mover
    (requiring S) for the same processor p.

    For this to be possible:
    - The set of mover contexts and non-mover contexts for p must be disjoint
      (when the mover output differs from S).
    - More precisely: if context (L,S,R) appears at a mover step, the output S'
      is fixed. If the same (L,S,R) appears at a non-mover step, we need S' = S.
      So EC occurs iff S' != S.

    The obstruction: in a cycle, the configs are highly constrained. Non-movers
    don't change, so neighboring processors' values at consecutive steps are
    strongly correlated, forcing context repetition.
    """
    cl = len(walk)
    fc = Counter(walk)

    print(f"  CL={cl}, n={n}, ms={ms}")
    print(f"  Fire counts: {dict(fc)}")
    print(f"  Product: {prod(ms)}")

    for p in range(n):
        total_ctx = context_space_size(p, n, ms)
        mover_steps = fc[p]
        nonmover_steps = cl - fc[p]
        print(f"\n  Proc {p} (m={ms[p]}): context space = {total_ctx}")
        print(f"    Mover steps: {mover_steps}, Non-mover steps: {nonmover_steps}")
        print(f"    Total context uses: {cl}")
        print(f"    Budget ratio: {cl}/{total_ctx} = {cl/total_ctx:.2f}")

        if cl > total_ctx:
            print(f"    *** IMPOSSIBLE: more context uses than available triples! ***")
        elif mover_steps + nonmover_steps > total_ctx:
            # This is just cl > total_ctx again
            pass
        else:
            # The real constraint: among total_ctx triples, we need to partition
            # the USED ones into mover-triples and non-mover-triples with no overlap
            # (when mover output != S).
            # With m_p states for S, each (L,R) pair has m_p possible S values.
            # A mover context (L,S,R) with output S'!=S: this "blocks" the identity
            # at (L,S,R). But doesn't block (L,S',R) for non-mover.
            lr_pairs = ms[(p-1)%n] * ms[(p+1)%n]
            print(f"    (L,R) pairs: {lr_pairs}")
            print(f"    S values per (L,R): {ms[p]}")
            print(f"    If fc={mover_steps}: at least {mover_steps} distinct mover contexts needed")
            print(f"    Non-mover needs {nonmover_steps} context slots (may share (L,R) with mover if S differs)")

def enumerate_short_cycles_dfs(n, binary_pos, max_cl, max_results=500):
    """
    Enumerate ring-adjacent cycles of minimum length that:
    - Visit all n processors
    - Binary procs have even fire count >= 2
    - Cycle closes (last ring-adjacent to first)
    """
    bp_set = set(binary_pos)
    results = []

    def dfs(path, visited, cl_target):
        if len(path) == cl_target:
            # Check closing and constraints
            if not ring_adj(path[-1], path[0], n):
                return
            fc = Counter(path)
            if len(fc) < n:
                return
            if not all(fc[p] % 2 == 0 and fc[p] >= 2 for p in bp_set):
                return
            results.append(tuple(path))
            return

        if len(results) >= max_results:
            return

        pos = path[-1]
        for nxt in [(pos-1)%n, pos, (pos+1)%n]:
            path.append(nxt)
            dfs(path, visited | {nxt}, cl_target)
            path.pop()

    # Try increasing cycle lengths
    for cl in range(2*n, 4*n + 1):
        if results:
            break
        dfs([0], {0}, cl)
        if results:
            print(f"  Found {len(results)} cycles at CL={cl}")

    return results

def build_configs_and_check_ec(walk, n, ms, num_trials=500):
    """
    Build consistent config sequences and check for EC.
    Returns (num_consistent, num_no_ec, ec_details).
    """
    cl = len(walk)
    consistent = 0
    no_ec = 0
    ec_proc_counts = Counter()

    for _ in range(num_trials):
        # Random initial config
        config = [random.randrange(ms[p]) for p in range(n)]
        configs = [tuple(config)]
        seen = {tuple(config)}
        ok = True

        for step in range(cl - 1):
            mover = walk[step]
            old_val = config[mover]
            choices = [v for v in range(ms[mover]) if v != old_val]
            random.shuffle(choices)
            found = False
            for new_val in choices:
                config[mover] = new_val
                c = tuple(config)
                if c not in seen:
                    seen.add(c)
                    configs.append(c)
                    found = True
                    break
            if not found:
                ok = False
                break

        if not ok:
            continue

        # Check cycle closure
        mover = walk[cl - 1]
        needed = configs[0][mover]
        close_ok = True
        for p in range(n):
            if p != mover and config[p] != configs[0][p]:
                close_ok = False
                break
        if not close_ok:
            continue
        if needed == config[mover]:
            continue

        consistent += 1

        # Check EC
        has_ec = False
        for p in range(n):
            ctx_map = {}
            for i in range(cl):
                L = configs[i][(p-1)%n]
                S = configs[i][p]
                R = configs[i][(p+1)%n]
                ctx = (L, S, R)
                next_i = (i+1) % cl
                S_next = configs[next_i][p]

                if p == walk[i]:
                    output = S_next
                else:
                    output = S

                if ctx in ctx_map:
                    if ctx_map[ctx] != output:
                        has_ec = True
                        ec_proc_counts[p] += 1
                        break
                else:
                    ctx_map[ctx] = output
            if has_ec:
                break

        if not has_ec:
            no_ec += 1

    return consistent, no_ec, ec_proc_counts

print("=" * 70)
print("SCRIPT 4: The Killing Argument")
print("=" * 70)

# Part 1: Context budget analysis
print("\n--- Part 1: Context budget analysis ---")
for n in [5, 7, 9, 11]:
    print(f"\n{'='*50}")
    print(f"n = {n}")

    # Sub-threshold: product < 4 * 3^(n-2)
    # With 3 binary: product = 2^3 * 3^(n-3) = 8 * 3^(n-3)
    # Threshold: 4 * 3^(n-2) = 12 * 3^(n-3)

    ms = [3] * n
    # Place binary at 0, n//2, ... (maximally separated)
    # For n=5: 0, 2, 4 has dist(4,0)=1 on C_5 (adjacent). Try 0, 2, 3 -- dist(2,3)=1. Hmm.
    # For n=5 there's no 3-independent set.
    # Use consecutive binary at 0,1,2 (which is the case in the actual problem).
    bp = [0, 1, 2]
    for p in bp:
        ms[p] = 2
    product = prod(ms)
    threshold = 4 * 3**(n-2)
    print(f"ms={ms}, product={product}, threshold={threshold}")
    print(f"Sub-threshold: {product < threshold}")

    # For double-loop walk
    walk = [i % n for i in range(2*n)]
    analyze_context_budget(n, ms, walk)

# Part 2: EC rate by n
print("\n\n--- Part 2: EC rate scaling ---")
print(f"{'n':>4} | {'CL':>6} | {'consistent':>12} | {'no_EC':>8} | {'EC_rate':>10}")
print("-" * 55)

for n in [5, 7, 9]:
    ms = [3] * n
    bp = [0, 1, 2]
    for p in bp:
        ms[p] = 2

    walk = [i % n for i in range(2*n)]
    consistent, no_ec, ec_procs = build_configs_and_check_ec(walk, n, ms, num_trials=2000)

    ec_rate = 1.0 - no_ec/max(consistent, 1) if consistent > 0 else 1.0
    print(f"{n:4d} | {2*n:6d} | {consistent:12d} | {no_ec:8d} | {ec_rate:10.4f}")
    if ec_procs:
        print(f"      EC proc distribution: {dict(ec_procs)}")

# Part 3: Exhaustive for n=5
print("\n\n--- Part 3: Exhaustive at n=5 ---")
n = 5
ms = [2, 2, 2, 3, 3]
bp = [0, 1, 2]
product = prod(ms)
threshold = 4 * 3**(n-2)
print(f"n={n}, ms={ms}, product={product}, threshold={threshold}")

# Try ALL walk types up to CL=3n
print(f"\nTrying all structured walk types:")
walk_types = {
    'double_CW': [i % n for i in range(2*n)],
    'double_CCW': [(n - i) % n for i in range(2*n)],
    'CW_CCW': list(range(n)) + list(range(n-1, -1, -1)),
    'triple_CW': [i % n for i in range(3*n)],
}

for name, walk in walk_types.items():
    cl = len(walk)
    if cl > product:
        print(f"\n  {name} (CL={cl}): exceeds product {product}, skip")
        continue
    fc = Counter(walk)
    binary_ok = all(fc[p] % 2 == 0 for p in bp)
    hfull = len(fc) == n

    print(f"\n  {name} (CL={cl}): fc={dict(fc)}, binary_even={binary_ok}, hfull={hfull}")
    if binary_ok and hfull:
        consistent, no_ec, ec_procs = build_configs_and_check_ec(walk, n, ms, num_trials=5000)
        print(f"    consistent={consistent}, no_EC={no_ec}")
        if ec_procs:
            print(f"    EC procs: {dict(ec_procs)}")

# Part 4: Identify the exact obstruction
print("\n\n--- Part 4: The Exact Obstruction ---")
print("""
ANALYSIS OF THE KILLING MECHANISM:

For a ring-adjacent good cycle with movers m_0, ..., m_{CL-1}:

1. CONTEXT CORRELATION: In a cycle of configs, non-mover processors don't change.
   So if mover at step i is processor p, then for all q != p:
     config[i+1][q] = config[i][q].

   This means the contexts of processor q at steps i and i+1 are IDENTICAL
   except possibly for q's neighbor values that changed (which is only
   config[*][p], the mover's value).

2. FORCED CONTEXT REPETITION: Consider a binary processor p (m_p = 2).
   - p fires fc_p times (even, >= 2) as mover.
   - p appears CL - fc_p times as non-mover.
   - p's context is (L, S, R) with L in {0,...,m_{p-1}-1}, S in {0,1}, R in {0,...,m_{p+1}-1}.
   - Total contexts: m_{p-1} * 2 * m_{p+1}.

   For binary p with binary neighbors (m_{p-1}=m_{p+1}=2):
     Total contexts = 2*2*2 = 8.
     CL = 2n uses contexts at ALL CL steps.
     For n=5: CL=10, contexts=8. PIGEONHOLE: at least 3 repeated contexts!
     Some of these MUST be mover-vs-nonmover collisions.

3. THE BINARY TRIPLE BOTTLENECK:
   For 3 consecutive binary processors at positions 0,1,2 with ms=(2,2,2,...):
   - Proc 1 has neighbors 0 and 2, both binary.
   - Context space for proc 1: 2*2*2 = 8 triples.
   - In a cycle of length CL >= 2n, proc 1 appears CL times.
   - For CL = 2n = 10 at n=5: 10 appearances in 8 slots = FORCED collision.

   Moreover: proc 1 fires 2+ times as mover. At mover steps, S changes (0->1 or 1->0).
   At non-mover steps, S stays. If the same (L,S,R) appears at both types: EC.

   For n=9: CL >= 2n = 18, context space still 8. 18 appearances in 8 slots.
   Even more collisions. But the mover fire count is still just 2.
   So 2 mover + 16 non-mover uses in 8 contexts.
   By pigeonhole: at least 10 non-mover collisions (harmless, same output S).
   But the 2 mover contexts MUST NOT collide with any of the 16 non-mover ones.
   Probability of avoidance: roughly (6/8)^2 ~ 56% per proc.

   But this doesn't FORCE EC. The obstruction is more subtle.

4. THE REAL OBSTRUCTION: WALK ADJACENCY FORCES CONTEXT OVERLAP.

   In a ring-adjacent walk, consecutive movers are at distance <= 1.
   When mover moves from position p to position p (staying in place) or p+-1,
   the context of ALL processors changes minimally.

   Specifically: when mover at step i is processor p, and mover at step i+1
   is processor q (|p-q| <= 1 mod n), then:
   - config[i+1] differs from config[i] only at position p (the mover).
   - config[i+2] differs from config[i+1] only at position q.

   So for processor r far from p and q: its context at steps i, i+1, i+2
   are ALL IDENTICAL. Three uses of the same context triple, at least some
   as mover vs non-mover. If r fires at exactly one of these: EC.

5. QUANTITATIVE BOUND:
   For proc p, let N_p = #{steps where p's context is unchanged from previous step}.
   In a ring-adjacent walk, the context of p changes only when the mover is
   p-1, p, or p+1 (neighbors change). Otherwise: exact same context.

   Fire count of {p-1, p, p+1} combined: fc_{p-1} + fc_p + fc_{p+1}.
   Steps where p's context MIGHT change: <= fc_{p-1} + fc_p + fc_{p+1}.
   Steps where p's context is DEFINITELY unchanged: CL - (fc_{p-1} + fc_p + fc_{p+1}).

   These "unchanged" steps all have the same context as their predecessor.
   If that predecessor was a mover step for p: all unchanged steps have EC!

   For sub-threshold product with 3 binary: sum of fire counts is CL = 2n.
   Average fc per proc: 2. Average sum of 3 consecutive: 6.
   Unchanged steps for middle proc: CL - 6 = 2n - 6.
   For n=9: 12 unchanged steps. Context repeats MASSIVELY.
""")

# Part 5: Quantify the forced repetition
print("--- Part 5: Forced context repetition quantification ---")
print(f"{'n':>4} | {'CL':>6} | {'ctx_space_mid':>15} | {'unchanged_mid':>15} | {'collision_ratio':>16}")
print("-" * 75)

for n in [5, 7, 9, 11, 13]:
    cl = 2 * n
    # Middle binary proc (proc 1) has binary neighbors (procs 0, 2)
    ctx_space = 2 * 2 * 2  # all binary neighbors
    # Fire counts: each proc fires ~2 times in double loop
    # Sum of fc for procs 0,1,2: ~6
    fc_neighborhood = 6
    unchanged = cl - fc_neighborhood
    collision_ratio = max(0, cl - ctx_space) / cl if cl > 0 else 0
    print(f"{n:4d} | {cl:6d} | {ctx_space:15d} | {unchanged:15d} | {collision_ratio:16.3f}")

print("""
THE KILLING ARGUMENT:

For n >= 5 with 3 consecutive binary processors at positions 0, 1, 2:

Consider processor 1 (binary, both neighbors binary).
- Context space: |{0,1}| * |{0,1}| * |{0,1}| = 8 triples.
- In ANY good cycle of length CL >= 2n:
  * Proc 1 fires fc_1 >= 2 times (even) as mover.
  * At mover steps: f(L,S,R) = S' != S (value changes).
  * At non-mover steps: f(L,S,R) = S (value stays).
  * CL total context appearances.

- Ring-adjacent walk constraint => context changes for proc 1 only when
  movers are at {0, 1, 2}. Combined fire count of {0,1,2} is >= 6.

- So proc 1's context is UNCHANGED for at least CL - 6 consecutive-step pairs.
  These form "runs" of identical context.

- Within each run: all steps have the same (L,S,R) and the same role
  (non-mover, since the mover is far from proc 1).

- The mover steps for proc 1 have SOME context (L,S,R) each.
  After a mover step, S changes (0->1 or 1->0). The context becomes (L,S',R).

- KEY: if the walk returns to proc 1 later (it must, for fc >= 2),
  the intervening non-mover steps may have accumulated a context that
  matches a previous mover context.

- For n large: CL = 2n grows, context space stays at 8.
  By pigeonhole: >= CL - 8 = 2n - 8 forced context collisions.
  These collisions between mover and non-mover contexts constitute
  entry conflicts with probability approaching 1.

- EXACT OBSTRUCTION: The entry conflict is not probabilistic —
  it's FORCED by the combination of:
  (a) Binary context space is tiny (8 triples)
  (b) Ring-adjacent walk forces slow context change
  (c) Cycle closure forces context repetition
  (d) Mover/non-mover role asymmetry at repeated contexts

This is the BINARY TRIPLE BOTTLENECK: binary processors with binary
neighbors in a ring-adjacent walk cannot avoid entry conflict because
their context space (8) is overwhelmed by the walk length (2n).

For this to fail, we would need CL <= 8, but hfull requires CL >= n.
So for n >= 9: CL >= 9 > 8, and the bottleneck is absolute.
For n = 5: CL = 10 > 8, still forced but with more room for the
specific context assignments to avoid EC (and indeed some do exist at n=5).

WAIT — but at n=5 with ms=(2,2,2,3,3), valid systems DO exist (M_5=96 witness).
So the obstruction is NOT absolute at n=5. Let me reconsider...

The M_5=96 witness has ms=[2,2,2,3,4], product=96, which is SUB-threshold
(96 < 108). But it EXISTS. So the entry conflict argument must be more
nuanced than pure pigeonhole on context space.

The correct statement: entry conflict is guaranteed for CERTAIN walk structures
(like the double loop), but there may exist OTHER walk structures that avoid it.
The real lower bound proof works by showing that ALL possible good cycles
(not just double loops) have entry conflicts under the sub-threshold product.
This requires analyzing the interplay between:
- Which processors fire and in what order
- The forced context propagation from ring-adjacency
- The parity constraints from binary processors
""")
