"""Search for a syntactic potential that decreases on all 787 non-DAG boundary transitions.

If found, this replaces PhiFull entirely.
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_final_verify import T_bot, T_low, T_mid, T_high, T_top
from itertools import product as cartesian
from collections import Counter

def build_system(n):
    ms = [2] + [3]*(n-2) + [2]
    tables = [None]*n
    tables[0] = T_bot; tables[1] = T_low
    for i in range(2, n-2): tables[i] = T_mid
    tables[n-2] = T_high; tables[n-1] = T_top
    return ms, tables

def move(ms, tables, c, i):
    n = len(ms)
    L, S, R = c[(i-1)%n], c[i], c[(i+1)%n]
    new = tables[i][(L,S,R)]
    if new == S: return None
    return c[:i] + (new,) + c[i+1:]

def boundary6(c, n):
    return (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])

def encode6(b):
    return b[0] + 2*b[1] + 6*b[2] + 18*b[3] + 54*b[4] + 162*b[5]

def build_good_cycle(n):
    def v(n, t, j):
        if t < n: return 0 if j <= t else (2 if j < n-1 else 1)
        elif t < 2*n-2:
            m = 2*n-2-t; return 0 if j < m else (2 if j < n-1 else 1)
        elif t == 2*n-2: return 1 if j == 0 else (2 if j < n-1 else 1)
        else:
            k = t-(2*n-2)
            if k == 0: return 1 if j == 0 else (2 if j < n-1 else 1)
            return 0 if j < k else (2 if j < n-1 else 1)
    return {tuple(v(n, t, j) for j in range(n)) for t in range(3*n-2)}

# Step 1: Find the 617-edge DAG and the 787 non-DAG transitions
n = 9
ms, tables = build_system(n)
good = build_good_cycle(n)

dag_edges = set()  # CΦ edges (need TP + PhiFull constant — approximate as all bad boundary edges)
all_bad_bdry = set()  # All bad boundary-changing transitions
non_dag_transitions = []  # (src_config, dst_config, mover, src_bdry, dst_bdry) for non-DAG

# First pass: collect ALL bad boundary transitions as (src_6tuple, dst_6tuple)
for c in cartesian(*[range(m) for m in ms]):
    if c in good: continue
    for i in range(n):
        d = move(ms, tables, c, i)
        if d is None: continue
        if d in good: continue
        bs, bd = boundary6(c, n), boundary6(d, n)
        if bs != bd:
            edge = (encode6(bd), encode6(bs))
            all_bad_bdry.add(edge)

print(f"Total bad boundary edges at n={n}: {len(all_bad_bdry)}")

# Now check: which of these 1404 are "DAG" vs "non-DAG"
# The 617-edge set is the sixTupleEdge set. Let me compute it from the Lean definition.
# Actually, let's just check: at n=9, compute fc for every bad config, then find steps 
# where fc doesn't drop AND boundary changes. Those are the CΦ boundary edges.

from collections import defaultdict

def compute_fc(config, good_configs):
    """fc = number of good-cycle configs that match this config at every position."""
    # Actually fc in CUP-2 = number of good cycle configs reachable... that's expensive.
    # Simpler: fc = |{g in good : g agrees with c on all privileged positions}|
    # Actually no, fc is just the count of good cycle configs where the config "matches"
    # In the Lean code, fc is more complex. Let me just count boundary edges by whether
    # the boundary change is in the known 617 set.
    pass

# Let me just use a different approach: compute the 617 set from the verification script
# The 617 edges are the SixTupleEdge set. Let me read it from the Lean constants.
# Actually easier: the 617 set is computed in clb_convergence_proof105.py or similar.

# For now, let me just characterize the distribution of ALL 1404 edges.
edge_counts = Counter()
mover_positions = Counter()
for c in cartesian(*[range(m) for m in ms]):
    if c in good: continue
    for i in range(n):
        d = move(ms, tables, c, i)
        if d is None: continue
        if d in good: continue
        bs, bd = boundary6(c, n), boundary6(d, n)
        if bs != bd:
            edge = (bd, bs)
            edge_counts[edge] += 1
            mover_positions[i] += 1

print(f"\nMover position distribution for bad boundary transitions:")
for pos in sorted(mover_positions):
    print(f"  position {pos}: {mover_positions[pos]} transitions")

print(f"\nTop 20 most common boundary edges:")
for edge, count in edge_counts.most_common(20):
    dst6, src6 = edge
    print(f"  {src6} -> {dst6}: {count} configs")

# Step 2: Try simple syntactic potentials
print("\n--- Syntactic potential search ---")

def pos_type(i, n):
    """Position type: 0=P0, 1=P1, 2=P2, 3=mid, 4=P_{n-3}, 5=P_{n-2}, 6=P_{n-1}"""
    if i == 0: return 0
    if i == 1: return 1
    if i == 2: return 2
    if i == n-3: return 4
    if i == n-2: return 5
    if i == n-1: return 6
    return 3

# Candidate 1: fc (number of good configs that are "compatible")
# This is expensive to compute properly. Skip for now.

# Candidate 2: Sum of per-position "displacement from good cycle"
# For each position, min over good configs of |c[i] - g[i]|
good_list = list(good)

def hamming_to_good(c):
    return min(sum(1 for j in range(len(c)) if c[j] != g[j]) for g in good_list)

# Test Hamming distance
print("Testing Hamming distance to good cycle...")
violations = 0
tested = 0
for c in cartesian(*[range(m) for m in ms]):
    if c in good: continue
    for i in range(n):
        d = move(ms, tables, c, i)
        if d is None: continue
        if d in good: continue
        bs, bd = boundary6(c, n), boundary6(d, n)
        if bs != bd:
            hc = hamming_to_good(c)
            hd = hamming_to_good(d)
            tested += 1
            if hd > hc:
                violations += 1
if tested > 0:
    print(f"  Hamming: {violations}/{tested} violations ({100*violations/tested:.1f}%)")

# Candidate 3: Weighted boundary value sum
def boundary_potential(c, n):
    """Simple boundary-based potential."""
    return c[0]*100 + c[1]*30 + c[2]*10 + c[n-3]*10 + c[n-2]*30 + c[n-1]*100

violations_bp = 0
for c in cartesian(*[range(m) for m in ms]):
    if c in good: continue
    for i in range(n):
        d = move(ms, tables, c, i)
        if d is None: continue
        if d in good: continue
        bs, bd = boundary6(c, n), boundary6(d, n)
        if bs != bd:
            if boundary_potential(d, n) >= boundary_potential(c, n):
                violations_bp += 1
print(f"  Boundary potential: {violations_bp}/{tested} violations ({100*violations_bp/tested:.1f}%)")

# Candidate 4: Interior defect count  
def interior_defects(c, n):
    """Count positions where c[j] differs from c[j-1] for interior positions."""
    return sum(1 for j in range(1, n) if c[j] != c[j-1])

violations_id = 0
for c in cartesian(*[range(m) for m in ms]):
    if c in good: continue
    for i in range(n):
        d = move(ms, tables, c, i)
        if d is None: continue
        if d in good: continue
        bs, bd = boundary6(c, n), boundary6(d, n)
        if bs != bd:
            if interior_defects(d, n) >= interior_defects(c, n):
                violations_id += 1
print(f"  Interior defects: {violations_id}/{tested} violations ({100*violations_id/tested:.1f}%)")

print(f"\nTotal time: {time.time() - (time.time())}s")  # placeholder
