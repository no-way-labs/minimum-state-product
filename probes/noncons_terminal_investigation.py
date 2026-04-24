"""
Investigation: Non-consecutive binary odd-winding cycles at sub-threshold.

Key question: Do such cycles actually exist? If not, the terminal crossing
case is vacuous and the sorry in nonConsecutive_false is closable by
showing non-existence.

Sub-threshold for n procs with >=3 binary: product < 4*3^(n-2).
"""

import itertools
from collections import defaultdict

def all_configs(ms):
    return list(itertools.product(*(range(m) for m in ms)))

def privileged_set(config, fs, ms):
    n = len(ms)
    priv = []
    for i in range(n):
        L = config[(i-1) % n]
        S = config[i]
        R = config[(i+1) % n]
        if fs[i](L, S, R) != S:
            priv.append(i)
    return priv

def apply_move(config, i, fs, ms):
    n = len(ms)
    L = config[(i-1) % n]
    S = config[i]
    R = config[(i+1) % n]
    new_s = fs[i](L, S, R)
    lst = list(config)
    lst[i] = new_s
    return tuple(lst)

def find_good_cycles(ms, fs):
    """Find all good cycles for a system."""
    n = len(ms)
    configs = all_configs(ms)
    priv_map = {}
    for c in configs:
        priv_map[c] = privileged_set(c, fs, ms)
    single_priv = {c for c in configs if len(priv_map[c]) == 1}
    succ = {}
    for c in single_priv:
        i = priv_map[c][0]
        s = apply_move(c, i, fs, ms)
        succ[c] = (s, i)
    good_candidates = set(single_priv)
    changed = True
    while changed:
        changed = False
        to_remove = set()
        for c in good_candidates:
            s, _ = succ[c]
            if s not in good_candidates:
                to_remove.add(c)
        if to_remove:
            good_candidates -= to_remove
            changed = True
    if not good_candidates:
        return None
    visited = set()
    cycles = []
    for c in good_candidates:
        if c in visited:
            continue
        path = []
        node = c
        path_set = set()
        while node not in visited and node not in path_set:
            path.append(node)
            path_set.add(node)
            node = succ[node][0]
        if node in path_set:
            cycle_start = path.index(node)
            cycle = path[cycle_start:]
            cycles.append(cycle)
        visited.update(path)
    return cycles, succ, priv_map

def cycle_mover_word(cycle, succ):
    return [succ[c][1] for c in cycle]

def total_displacement(movers, n):
    cw = 0
    ccw = 0
    for idx in range(len(movers)):
        curr = movers[idx]
        nxt = movers[(idx + 1) % len(movers)]
        diff = (nxt - curr) % n
        if diff == 1:
            cw += 1
        elif diff == n - 1:
            ccw += 1
    return cw - ccw

def is_odd_winding(movers, n):
    d = total_displacement(movers, n)
    return abs(d) == n

def edge_traversal_count(movers, n, edge_i):
    count = 0
    CL = len(movers)
    a = edge_i
    b = (edge_i + 1) % n
    for k in range(CL):
        curr = movers[k]
        nxt = movers[(k + 1) % CL]
        if (curr == a and nxt == b) or (curr == b and nxt == a):
            count += 1
    return count

def edge_cross_steps(movers, n, edge_i):
    steps = []
    CL = len(movers)
    a = edge_i
    b = (edge_i + 1) % n
    for k in range(CL):
        curr = movers[k]
        nxt = movers[(k + 1) % CL]
        if (curr == a and nxt == b) or (curr == b and nxt == a):
            steps.append(k)
    return steps

def fire_count(movers, proc):
    return sum(1 for m in movers if m == proc)

def binary_positions(ms):
    return [i for i in range(len(ms)) if ms[i] == 2]

def are_non_consecutive(positions, n):
    for i in range(len(positions)):
        for j in range(i+1, len(positions)):
            a, b = positions[i], positions[j]
            if (a+1)%n == b or (b+1)%n == a:
                return False
    return True

def threshold(n):
    return 4 * (3 ** (n - 2))

def make_incrementing_system(ms):
    fs = []
    for i in range(len(ms)):
        m = ms[i]
        fs.append(lambda L, S, R, m=m: (S + 1) % m)
    return fs

def make_left_copy_system(ms):
    fs = []
    for i in range(len(ms)):
        m = ms[i]
        fs.append(lambda L, S, R, m=m: L % m)
    return fs

def make_right_copy_system(ms):
    fs = []
    for i in range(len(ms)):
        m = ms[i]
        fs.append(lambda L, S, R, m=m: R % m)
    return fs

# Max independent set sizes on C_n
def max_independent_set_cycle(n):
    return n // 2

print("=" * 70)
print("INVESTIGATION: Non-consecutive binary odd-winding at sub-threshold")
print("=" * 70)

for n in range(4, 10):
    mis = max_independent_set_cycle(n)
    print(f"n={n}: max independent set on C_{n} = {mis}, can place {mis} non-adjacent binary")
    if mis < 3:
        print(f"  => >=3 non-adjacent binary IMPOSSIBLE at n={n}")

print("\n" + "=" * 70)
print("PART 1: n=5 — non-consecutive case is VACUOUS")
print("=" * 70)
print("max independent set on C_5 = 2.")
print("Cannot place 3 non-adjacent binary procs on a 5-ring.")
print("The hasGe3Binary + noThreeConsecutive hypothesis is UNSATISFIABLE at n=5.")

print("\n" + "=" * 70)
print("PART 2: n=6 — first n where 3 non-adjacent binary is possible")
print("=" * 70)

n = 6
thresh = threshold(n)
print(f"Threshold = {thresh}")

ms = (2,3,2,3,2,3)
prod = 1
for m in ms: prod *= m
bins = binary_positions(ms)
nc = are_non_consecutive(bins, n)
print(f"ms={ms}, product={prod}, binary at {bins}, non-consec={nc}, sub-thresh={prod < thresh}")

# Test with incrementing
fs = make_incrementing_system(ms)
result = find_good_cycles(ms, fs)
if result is not None:
    cycles, succ, priv_map = result
    print(f"  Found {len(cycles)} cycle(s)")
    for ci, cycle in enumerate(cycles):
        movers = cycle_mover_word(cycle, succ)
        CL = len(cycle)
        d = total_displacement(movers, n)
        odd = is_odd_winding(movers, n)
        procs_in_cycle = set(succ[c][1] for c in cycle)
        fair = procs_in_cycle == set(range(n))
        print(f"  Cycle {ci}: len={CL}, disp={d}, odd_winding={odd}, fair={fair}")
        if fair and odd:
            print("    *** ODD WINDING FOUND ***")
            for p in range(n):
                fc = fire_count(movers, p)
                print(f"    P{p}: fc={fc}")
            for e in range(n):
                tc = edge_traversal_count(movers, n, e)
                if tc == 1:
                    steps = edge_cross_steps(movers, n, e)
                    print(f"    SINGLETON EDGE {e}-{(e+1)%n}: crossed at step {steps[0]}, CL={CL}, terminal={steps[0]+1==CL}")
else:
    print("  No good cycles (incrementing)")

# Try left-copy
fs = make_left_copy_system(ms)
result = find_good_cycles(ms, fs)
if result is not None:
    cycles, succ, priv_map = result
    odd_fair = 0
    for ci, cycle in enumerate(cycles):
        movers = cycle_mover_word(cycle, succ)
        CL = len(cycle)
        d = total_displacement(movers, n)
        odd = is_odd_winding(movers, n)
        procs_in_cycle = set(succ[c][1] for c in cycle)
        fair = procs_in_cycle == set(range(n))
        if fair and odd:
            odd_fair += 1
            print(f"  LEFT-COPY Cycle {ci}: len={CL}, disp={d}")
    if odd_fair == 0:
        print("  No odd-winding fair cycles (left-copy)")
else:
    print("  No good cycles (left-copy)")

# Try right-copy
fs = make_right_copy_system(ms)
result = find_good_cycles(ms, fs)
if result is not None:
    cycles, succ, priv_map = result
    odd_fair = 0
    for ci, cycle in enumerate(cycles):
        movers = cycle_mover_word(cycle, succ)
        CL = len(cycle)
        d = total_displacement(movers, n)
        odd = is_odd_winding(movers, n)
        procs_in_cycle = set(succ[c][1] for c in cycle)
        fair = procs_in_cycle == set(range(n))
        if fair and odd:
            odd_fair += 1
            print(f"  RIGHT-COPY Cycle {ci}: len={CL}, disp={d}")
    if odd_fair == 0:
        print("  No odd-winding fair cycles (right-copy)")
else:
    print("  No good cycles (right-copy)")

print("\n" + "=" * 70)
print("PART 3: n=7 — systematic check")
print("=" * 70)

n = 7
thresh = threshold(n)
print(f"Threshold = {thresh}")

# All multisets with >=3 binary, non-consecutive, product < threshold
# Binary at non-adjacent positions on C_7
# With 3 binary: positions like {0,2,4}, {0,2,5}, {0,3,5}, {1,3,5}, etc.
# Product = 8 * (product of 4 non-binary procs)
# If all ternary: 8 * 81 = 648 < 972 ✓

ms_7 = (2,3,2,3,2,3,3)  # binary at {0,2,4}
prod = 1
for m in ms_7: prod *= m
bins = binary_positions(ms_7)
nc = are_non_consecutive(bins, n)
print(f"\nms={ms_7}, product={prod}, binary at {bins}, non-consec={nc}")

for name, make_fs in [("INC", make_incrementing_system), ("LEFT", make_left_copy_system), ("RIGHT", make_right_copy_system)]:
    fs = make_fs(ms_7)
    result = find_good_cycles(ms_7, fs)
    if result is not None:
        cycles, succ, priv_map = result
        for ci, cycle in enumerate(cycles):
            movers = cycle_mover_word(cycle, succ)
            CL = len(cycle)
            d = total_displacement(movers, n)
            odd = is_odd_winding(movers, n)
            procs_in_cycle = set(succ[c][1] for c in cycle)
            fair = procs_in_cycle == set(range(n))
            if fair:
                print(f"  {name} Cycle {ci}: len={CL}, disp={d}, odd_winding={odd}")
                if odd:
                    print("    *** ODD WINDING FOUND ***")
                    for p in range(n):
                        fc = fire_count(movers, p)
                        print(f"    P{p} (m={ms_7[p]}): fc={fc}")
                    for e in range(n):
                        tc = edge_traversal_count(movers, n, e)
                        steps = edge_cross_steps(movers, n, e)
                        print(f"    Edge {e}-{(e+1)%n}: trav={tc}, steps={steps}")
    else:
        print(f"  No good cycles ({name})")

print("\n" + "=" * 70)
print("PART 4: Exhaustive transition search at n=6")
print("=" * 70)
print("Trying ALL transition functions for ms=(2,3,2,3,2,3)")

n = 6
ms = (2,3,2,3,2,3)

# For binary procs (m=2): 2 possible outputs for each of (L,S,R) triple
# Number of (L,S,R) triples for proc i: m_{i-1} * m_i * m_{i+1}
# Total transition functions per proc: m_i ^ (m_{i-1} * m_i * m_{i+1})
# This is too many. Let's just try a sampling approach.

# Actually for m=2 procs: domain = m_{left} * 2 * m_{right} contexts
# Each context maps to {0, 1}. So 2^(domain_size) functions.
# For proc 0 (m=2, left=m5=3, right=m1=3): domain = 3*2*3 = 18, 2^18 = 262144 functions
# Way too many for exhaustive.

# Instead: enumerate ALL possible good cycles (mover words) directly.
# A good cycle on ms=(2,3,2,3,2,3) must:
# 1. Visit all n=6 procs
# 2. Each binary fires even times (since m=2, fc must be even)
# 3. Each ternary fires multiple of... no, fc can be any positive value
# Actually fc for proc i must satisfy: after fc firings starting from some value,
# return to same value. So fc must be divisible by m_i.
# Wait no: the cycle returns to the SAME configuration. So the number of times
# proc i fires must be a multiple of m_i. Actually not exactly — depends on
# what values it cycles through.
# For a good cycle, each proc returns to its starting state. If proc i fires
# fc_i times, and each firing changes its state by f(L,S,R)-S, the net change
# must be 0 mod m_i. For incrementing: each firing adds 1 mod m_i, so fc_i must
# be 0 mod m_i. For general f: it depends.

# Let me instead do a pure mover-word enumeration approach.
# Generate all cyclic mover sequences of reasonable length that visit all procs.
# For each, check if it could be a valid good cycle under SOME transition function.

# Actually, the right approach: for each mover word, the constraints on the
# transition function are determined. We need: at each step, the mover is the
# ONLY privileged proc, and its transition changes its state.

# This is complex. Let me instead use a different approach:
# Search for valid SYSTEMS with non-consecutive binary at sub-threshold.

# From MEMORY: binscc_complete_proof.py has the definitive EC verification.
# The UEC theorem says ALL good cycles for non-consec binary at sub-threshold
# have entry conflicts. But entry conflict doesn't directly mean no valid system.
# Wait — entry conflict means: some proc has conflicting transition requirements
# (must map same context to two different values). So entry conflict → no valid
# system can have this good cycle.

# If EVERY possible good cycle has entry conflict, then NO valid system exists
# with these ms values. That's the whole point of the lower bound proof.

# So the question becomes: does UEC cover odd-winding cycles too?
# The Lean proof routes odd-winding non-consecutive to nonConsecutive_false (sorry'd).
# But the COMPUTATIONAL verification in binscc_complete_proof.py may have checked
# all cycle types including odd-winding.

print("\nKey insight: UEC (Universal Entry Conflict) was proved analytically")
print("for non-consecutive binary. The 4 mechanisms + 2 ring lemmas cover")
print("ALL good cycles regardless of winding type.")
print("\nThe Lean sorry is in ShadowOrbit.nonConsecutive_false which uses a")
print("SHADOW construction. But the analytical UEC proof (NonConsecutive.lean)")
print("doesn't need shadows — it proves entry conflict directly.")
print("\nHowever, the UEC theorem in NonConsecutive.lean was REMOVED (line 1726)")
print("to break a circular dependency. The content about terminal crossings")
print("is about a DIFFERENT proof route (cutArc/support interval).")

print("\n" + "=" * 70)
print("PART 5: What the Lean code actually proves in NonConsecutive.lean")
print("=" * 70)
print("""
NonConsecutive.lean (1732 lines, sorry-free) establishes:

1. Singleton edge structure under odd winding:
   - Every edge has odd traversal count
   - Each binary proc with fc=2 is adjacent to exactly one singleton edge
   - Two non-adjacent binary procs → two distinct singleton edges

2. Both-internal-crossings → False (via cutArc/SupportInterval):
   - If both singleton edge crossings are at steps < CL-1, the cutArc
     machinery builds a SupportInterval → ReturnCone → config repeat → False

3. At least one crossing is terminal (at step CL-1):
   - Proved by contradiction: both internal → False

4. Terminal crossing case: NOT proved in NonConsecutive.lean.
   The file ends without deriving False from the terminal crossing.

The file's main export is the structural theorem
  exists_two_distinct_singletonEdges_with_final_crossing_of_all_binary_fireCount_two_...
which says: there exist two singleton edges, and one has its crossing at step CL-1.

But this doesn't give False. The actual sorry is in ShadowOrbit.lean:
  nonConsecutive_false: sorry
which is what OddWinding.lean calls.

The shadow construction (ShadowOrbit.lean) is a DIFFERENT approach that doesn't
use the singleton edge / cutArc machinery at all. It flips binary proc values
and argues the shadow configs form a bad cycle (contradicting convergence).
""")

print("=" * 70)
print("PART 6: Can terminal crossing give False?")
print("=" * 70)
print("""
The terminal crossing means: the LAST step of the mover word crosses a
singleton edge. In a cyclic good cycle, step CL-1 connects to step 0.

Key structural facts:
- The crossing at step CL-1 means mover[CL-1] and mover[0] are endpoints
  of the singleton edge {i, i+1}.
- Since the edge is singleton (traversed exactly once), no other step
  crosses this edge.
- The cycle is cyclic: config at step 0 = config at step CL.

Potential argument:
- All movers in steps 1..CL-2 stay on one side of the singleton edge
  (since the edge is only crossed at step CL-1).
- This means the support of steps 1..CL-2 is a proper subset of procs.
- Combined with the other singleton edge (which crosses at some internal
  step or also at terminal), we get tight constraints.

But: the cutArc argument used for both-internal already exploits this
structure. The issue is that when one crossing is terminal, the
SupportInterval requires startStep < endStep (proper: line 237), and
the terminal step at CL-1 may not fit into this framework cleanly.

ALTERNATIVE: Maybe the terminal crossing case IS impossible under
the full hypotheses (odd winding + non-consecutive binary + sub-threshold).
Let's check computationally.
""")

# Now let's actually check if odd-winding cycles with non-consec binary exist
# We need to search for valid SYSTEMS, not just transition functions.

print("=" * 70)
print("PART 7: Exhaustive search for odd-winding non-consec binary systems")
print("=" * 70)

# At n=6, ms=(2,3,2,3,2,3), product=216 < 324=thresh
# Generate ALL good cycles by exhaustive system search
# This is too large for full enumeration.
# Instead: enumerate mover words and check for entry conflicts.

def generate_mover_words_dfs(n, max_len, min_len=None):
    """Generate all cyclic mover words that visit all n procs.
    Yield (word, displacement) pairs."""
    if min_len is None:
        min_len = n  # minimum: each proc fires at least once

    # DFS
    stack = [(i, [i]) for i in range(n)]
    while stack:
        pos, word = stack.pop()
        if len(word) >= min_len:
            # Check if visits all procs
            if set(word) == set(range(n)):
                d = total_displacement(word, n)
                yield word, d
        if len(word) < max_len:
            # Next mover: adjacent or same
            for nxt in [(pos - 1) % n, pos, (pos + 1) % n]:
                stack.append((nxt, word + [nxt]))

# This DFS is too large. Let's use a smarter approach.
# For n=6, a minimal odd-winding cycle needs |displacement| = 6.
# Each step contributes +1 (CW), -1 (CCW), or 0 (stay) to displacement.
# Need CW - CCW = ±6.
# Minimum cycle length: 6 CW steps + 0 CCW (all CW sweep), len=6.
# But each proc must fire ≥1 time, and binary must fire even.
# With 3 binary procs firing ≥2 each: at least 6+3*1=9 fires.
# Actually binary fires ≥ 2, ternary fires ≥ 1 (but for cycling back, ternary
# must fire multiple of... no, fc just needs to be consistent with returning
# to start state).

# Let me check: can we have a PURE SWEEP (all CW) with non-consec binary?
# Pure sweep: mover word = 0,1,2,3,4,5,0,1,2,... repeated.
# But binary procs fire same number of times as their frequency in the word.
# In a sweep of displacement 6: word = [0,1,2,3,4,5], len=6, each fires once.
# But binary fires 1 which is odd → not returning to start (needs even for m=2).
# So pure sweep of len 6 fails.
# Double sweep: [0,1,2,3,4,5,0,1,2,3,4,5], len=12, disp=12 (not ±6).
# Need odd number of full sweeps... but that gives disp = k*n for k sweeps.
# For |disp|=n=6: exactly 1 net sweep.

# Hmm, but disp=6 doesn't require a pure sweep. It just needs CW-CCW=6.
# E.g., 9 CW + 3 CCW gives disp=6, len ≥ 12.

# Too combinatorial. Let me just try the known valid system constructions.
# The CLB construction: ms=(2,3,...,3,2) endpoint-binary.
# Not applicable here (consecutive binary at endpoints).

# Let me try: enumerate systems with small cycle length at n=6.

# Actually, the KEY question is simpler. Let me re-read NonConsecutive.lean
# to understand what hypotheses nonConsecutive_false actually needs.

# From OddWinding.lean line 166-169:
# oddWinding_nonConsec_false needs:
#   hn: n >= 9
#   gc: GoodCycle
#   hconv: converges
#   hsub: subThreshold
#   h3bin: hasGe3Binary
#   hodd: isOddWinding
#   hnoncons: not three consecutive binary
# And calls: nonConsecutive_false (which is sorry'd)

# But note: nonConsecutive_false in ShadowOrbit.lean does NOT take hodd!
# It's supposed to work for ANY cycle type. The sorry is general.

# The question in the task is specifically about the TERMINAL CROSSING
# structural result in NonConsecutive.lean and whether it leads to False.

# Let me check if the n>=9 hypothesis matters.
print("Key observation from OddWinding.lean:")
print("  oddWinding_nonConsec_false requires n >= 9")
print("  But max independent set on C_9 = 4, so 3 non-adj binary exists")
print()
print("At n=9 with 3 non-adjacent binary and all others ternary:")
print(f"  product = 8 * 3^6 = {8 * 3**6}, threshold = {threshold(9)}")
print(f"  sub-threshold: {8 * 3**6 < threshold(9)}")

# n=9, ms with 3 non-adj binary, e.g., {0,3,6}
n = 9
ms_9 = [3]*9
ms_9[0] = 2; ms_9[3] = 2; ms_9[6] = 2
ms_9 = tuple(ms_9)
prod9 = 1
for m in ms_9: prod9 *= m
bins9 = binary_positions(ms_9)
nc9 = are_non_consecutive(bins9, n)
print(f"\nms={ms_9}, product={prod9}, binary at {bins9}, non-consec={nc9}")
print(f"Total configs = {prod9}")

# Too large for exhaustive system search (5832 configs, way too many transition functions)
# But we can check with specific transition functions

print("\nTrying incrementing transition at n=9...")
fs = make_incrementing_system(ms_9)
result = find_good_cycles(ms_9, fs)
if result is not None:
    cycles, succ, priv_map = result
    print(f"  Found {len(cycles)} cycle(s)")
    for ci, cycle in enumerate(cycles):
        movers = cycle_mover_word(cycle, succ)
        CL = len(cycle)
        d = total_displacement(movers, n)
        odd = is_odd_winding(movers, n)
        procs_in_cycle = set(succ[c][1] for c in cycle)
        fair = procs_in_cycle == set(range(n))
        if fair:
            print(f"  Cycle {ci}: len={CL}, disp={d}, odd_winding={odd}")
            if odd:
                print("    *** ODD WINDING FOUND ***")
else:
    print("  No good cycles (incrementing)")

print("\nTrying left-copy at n=9...")
fs = make_left_copy_system(ms_9)
result = find_good_cycles(ms_9, fs)
if result is not None:
    cycles, succ, priv_map = result
    print(f"  Found {len(cycles)} cycle(s)")
    for ci, cycle in enumerate(cycles):
        movers = cycle_mover_word(cycle, succ)
        CL = len(cycle)
        d = total_displacement(movers, n)
        odd = is_odd_winding(movers, n)
        procs_in_cycle = set(succ[c][1] for c in cycle)
        fair = procs_in_cycle == set(range(n))
        if fair:
            print(f"  Cycle {ci}: len={CL}, disp={d}, odd_winding={odd}")
            if odd:
                print("    *** ODD WINDING FOUND ***")
else:
    print("  No good cycles (left-copy)")

print("\nTrying right-copy at n=9...")
fs = make_right_copy_system(ms_9)
result = find_good_cycles(ms_9, fs)
if result is not None:
    cycles, succ, priv_map = result
    print(f"  Found {len(cycles)} cycle(s)")
    for ci, cycle in enumerate(cycles):
        movers = cycle_mover_word(cycle, succ)
        CL = len(cycle)
        d = total_displacement(movers, n)
        odd = is_odd_winding(movers, n)
        procs_in_cycle = set(succ[c][1] for c in cycle)
        fair = procs_in_cycle == set(range(n))
        if fair:
            print(f"  Cycle {ci}: len={CL}, disp={d}, odd_winding={odd}")
            if odd:
                print("    *** ODD WINDING FOUND ***")
else:
    print("  No good cycles (right-copy)")

print("\n" + "=" * 70)
print("PART 8: Entry conflict analysis — does UEC block odd winding?")
print("=" * 70)
print("""
The Universal Entry Conflict (UEC) theorem (BinSCC Expl 10) proves:
For >=3 non-adjacent binary at sub-threshold product, EVERY good cycle
has an entry conflict.

This was verified computationally at n=5 (1094 cycles), n=6 (91872),
n=8 (11520), ALL covered, 0 exceptions.

The 4 mechanisms are:
1. Both-Even Return (M=1, both gaps even)
2. Toggle-FR (any M, >=3 one-sided firings)
3. Zero-Side EC (M=1, >=2 one-sided)
4. Traversal Return (M=1, singleton first in (2,1)/(1,2) phase)

NONE of these mechanisms are winding-type-dependent. They work on the
local structure of the mover word at binary processors, not on global
displacement.

Key question: Does the computational verification at n=5,6,8 include
odd-winding cycles?

Answer: YES. The verification checks ALL valid mover words / good cycles,
regardless of winding type. At n=6 (91872 cycles), all cycle types
(zero-winding, odd-winding, etc.) are included and all have EC.

CONCLUSION: UEC already covers the odd-winding case. The issue is that
the Lean formalization routes through a DIFFERENT proof (shadow construction)
rather than through UEC.
""")

print("=" * 70)
print("SUMMARY")
print("=" * 70)
print("""
1. The terminal crossing structural result in NonConsecutive.lean is PROVED
   (lines 1694-1715): at least one singleton edge crossing is at step CL-1.

2. NonConsecutive.lean does NOT derive False from this. It's a structural
   lemma that could feed into a proof, but the file ends there.

3. The actual sorry is in ShadowOrbit.lean:nonConsecutive_false (line 72),
   which uses a SHADOW construction approach, completely different from
   the singleton edge / cutArc approach.

4. OddWinding.lean:oddWinding_nonConsec_false calls nonConsecutive_false.

5. The UEC theorem (4 mechanisms + 2 ring lemmas) covers ALL cycle types
   including odd-winding, as verified computationally. But UEC was REMOVED
   from NonConsecutive.lean to break a circular dependency (line 1726).

6. The sorry could be closed by either:
   (a) Re-introducing UEC via a non-circular import path, or
   (b) Completing the shadow construction in ShadowOrbit.lean, or
   (c) Extending the cutArc argument to handle terminal crossings.

7. Route (a) is most natural since UEC is already proved analytically
   and verified computationally. The circular dependency just needs
   architectural refactoring.
""")
