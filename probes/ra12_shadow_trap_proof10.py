"""
Shadow Trap Proof — Part 10: Check if the counterexamples are sweeps.

The theorem requires:
1. sweep (|totalDisplacement| >= 2n)
2. non-consecutive binary
3. isolated firings at some binary proc

What's the total displacement?
displacement(k) = sum over steps k of (mover_k - mover_{k-1}) measured on the ring.
Actually, total displacement of a mover word is the sum of signed steps.

For a sweep, the mover moves monotonically in one direction for a while,
then reverses. The total displacement is how far the mover "travels."

Actually, let me define it more carefully:
A "sweep" means the mover visits every position at least once going right,
then visits every position at least once going left (or vice versa).
This is characterized by the mover sequence having large total displacement.

For a right-left sweep:
  Rightward pass: movers 0,1,...,n-1 (displacement +n)
  Leftward pass: movers n-1,...,0 (displacement -n)
  Total |displacement| = 2n

For words where movers jump around randomly, the displacement is small.

Let me compute displacement and filter.
"""

import itertools
from collections import defaultdict
import random

def get_context(cfg, p, n):
    return (cfg[(p-1) % n], cfg[p], cfg[(p+1) % n])

def total_displacement(word, n):
    """Compute total displacement of the mover word.
    At each step, displacement is the signed distance from prev mover to current mover.
    We use the convention: positive = clockwise.
    """
    total = 0
    for i in range(1, len(word)):
        diff = (word[i] - word[i-1]) % n
        if diff > n // 2:
            diff -= n  # Take shorter path
        total += abs(diff)
    # Also from last to first (cycle)
    diff = (word[0] - word[-1]) % n
    if diff > n // 2:
        diff -= n
    total += abs(diff)
    return total

def is_sweep(word, n):
    """Check if word is a sweep: displacement >= 2n."""
    return total_displacement(word, n) >= 2 * n

def check_forced_graph_cycles(n, ms, word):
    """Check if forced graph has cycles. Returns (nontrivial_sccs, configs)."""
    CL = len(word)
    cfg = [0] * n
    configs = [tuple(cfg)]
    for p in word:
        cfg = list(configs[-1])
        cfg[p] = (cfg[p] + 1) % ms[p]
        configs.append(tuple(cfg))
    if configs[-1] != configs[0]:
        return None, "doesn't close"
    configs = configs[:-1]
    good_set = set(configs)

    cmap = {}
    for k in range(CL):
        p = word[k]
        g = configs[k]
        L, S, R = get_context(g, p, n)
        Sp = configs[(k+1) % CL][p]
        key = (p, L, S, R)
        if key in cmap:
            return None, "duplicate context"
        cmap[key] = (Sp, k)

    all_configs = list(itertools.product(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]

    forced_graph = {}
    for c in non_good:
        successors = []
        for p in range(n):
            ctx = get_context(c, p, n)
            key = (p,) + ctx
            if key in cmap:
                Sp, step = cmap[key]
                new_cfg = list(c)
                new_cfg[p] = Sp
                nc = tuple(new_cfg)
                if nc not in good_set:
                    successors.append(nc)
        forced_graph[c] = successors

    # Tarjan
    index_counter = [0]
    stack = []
    lowlink = {}
    index = {}
    on_stack = set()
    sccs = []

    def strongconnect(v):
        index[v] = index_counter[0]
        lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack.add(v)
        for w in forced_graph.get(v, []):
            if w not in index:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], index[w])
        if lowlink[v] == index[v]:
            scc = []
            while True:
                w = stack.pop()
                on_stack.remove(w)
                scc.append(w)
                if w == v:
                    break
            sccs.append(scc)

    import sys
    sys.setrecursionlimit(10000)
    for v in non_good:
        if v not in index:
            strongconnect(v)

    nontrivial = [s for s in sccs if len(s) > 1]
    return nontrivial, configs

def has_isolated_binary(word, ms, n):
    CL = len(word)
    for q in range(n):
        if ms[q] != 2:
            continue
        fire_steps = [k for k in range(CL) if word[k] == q]
        if len(fire_steps) != 2:
            continue
        isolated = True
        for k in fire_steps:
            k_prev = (k - 1) % CL
            k_next = (k + 1) % CL
            for neighbor in [(q - 1) % n, (q + 1) % n]:
                if word[k_prev] == neighbor or word[k_next] == neighbor:
                    isolated = False
                    break
            if not isolated:
                break
        if isolated:
            return True, q
    return False, None

# Full test with sweep condition
n = 5
ms = [2, 3, 2, 3, 2]
CL = sum(ms)
random.seed(42)

mover_pool = []
for p in range(n):
    mover_pool.extend([p] * ms[p])

sweep_iso_cycle = 0
sweep_iso_no_cycle = 0
sweep_no_iso_cycle = 0
sweep_no_iso_no_cycle = 0
non_sweep = 0

counterexamples = []

for trial in range(20000):
    word = list(mover_pool)
    random.shuffle(word)

    if not is_sweep(word, n):
        non_sweep += 1
        continue

    result, configs = check_forced_graph_cycles(n, ms, word)
    if result is None:
        continue

    is_iso, q = has_isolated_binary(word, ms, n)
    has_cycle = len(result) > 0

    if is_iso:
        if has_cycle:
            sweep_iso_cycle += 1
        else:
            sweep_iso_no_cycle += 1
            counterexamples.append(word[:])
    else:
        if has_cycle:
            sweep_no_iso_cycle += 1
        else:
            sweep_no_iso_no_cycle += 1

print(f"Sweep + isolated + cycle: {sweep_iso_cycle}")
print(f"Sweep + isolated + NO cycle: {sweep_iso_no_cycle}")
print(f"Sweep + no isolated + cycle: {sweep_no_iso_cycle}")
print(f"Sweep + no isolated + NO cycle: {sweep_no_iso_no_cycle}")
print(f"Non-sweep: {non_sweep}")

if counterexamples:
    print(f"\nCounterexamples (sweep + isolated + no cycle):")
    for w in counterexamples[:10]:
        disp = total_displacement(w, n)
        is_iso, q = has_isolated_binary(w, ms, n)
        print(f"  word={w}, displacement={disp}, isolated at proc {q}")

# Also check with stricter sweep definition
print("\n=== With stricter sweep definition ===")
# A sweep should have the mover moving monotonically
# Let me compute the "sweep quality" differently:
# Check if there's a contiguous subsequence where movers increase,
# followed by a contiguous subsequence where movers decrease

def is_strict_sweep(word, n):
    """Check if word is a right-then-left sweep:
    a prefix where movers are non-decreasing, followed by non-increasing."""
    CL = len(word)
    # Find the peak
    for peak in range(1, CL):
        # Check if word[0:peak] is non-decreasing and word[peak:] is non-increasing
        increasing = all(word[i] <= word[i+1] for i in range(peak-1))
        # For the decreasing part, need to handle the wrap
        if peak < CL:
            decreasing = all(word[i] >= word[i+1] for i in range(peak, CL-1))
        else:
            decreasing = True
        if increasing and decreasing:
            return True
    return False

strict_sweep_iso_cycle = 0
strict_sweep_iso_no_cycle = 0

for trial in range(20000):
    word = list(mover_pool)
    random.shuffle(word)

    if not is_strict_sweep(word, n):
        continue

    result, configs = check_forced_graph_cycles(n, ms, word)
    if result is None:
        continue

    is_iso, q = has_isolated_binary(word, ms, n)
    has_cycle = len(result) > 0

    if is_iso:
        if has_cycle:
            strict_sweep_iso_cycle += 1
        else:
            strict_sweep_iso_no_cycle += 1
            print(f"  STRICT COUNTEREXAMPLE: word={word}")

print(f"\nStrict sweep + isolated + cycle: {strict_sweep_iso_cycle}")
print(f"Strict sweep + isolated + NO cycle: {strict_sweep_iso_no_cycle}")
