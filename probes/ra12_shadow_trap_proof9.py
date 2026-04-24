"""
Shadow Trap Proof — Part 9: Rethinking the approach.

The complementary pair approach fails for many words with non-consecutive binary.
But the problem statement says "isolated firings at SOME binary proc."

Let me understand "isolated firings" precisely:
- Binary proc q fires at steps k1 and k2
- "Isolated" means: at step k1, the mover jumps to q from a distant proc,
  and at step k1+1, the mover jumps away from q to a distant proc.
  Similarly for k2.

More precisely: in a sweep, proc q fires during the forward pass and
during the backward pass. "Isolated" means q's neighbors DON'T fire
immediately before or after q fires.

Why would isolation guarantee the shadow trap?

ALTERNATIVE APPROACH: Instead of 2-cycles via complementary pairs,
look for the GENERAL shadow cycle.

The existing proofs use a very specific construction:
  s_k[j] = g_shifted[j] where the shift depends on j and k.
The key is that the mover contexts are PERMUTED, not replicated.

Let me go back to the ACTUAL shadow cycle construction from the proofs
and understand exactly what structure it relies on.

Actually, let me think about this more carefully from the non-good
config perspective. The claim is:

CLAIM: For any sweep with non-consecutive binary and isolated firing at
some binary proc q, the forced graph on non-good configs has a cycle.

A forced transition from config c fires some proc p where p's context
matches a mover table entry. The key question is: does the forced graph
always have a cycle?

Let me check: in the n=5 non-consecutive case, for words WITHOUT
complementary pairs, does the forced graph still have nontrivial SCCs?
"""

import itertools
from collections import defaultdict

def get_context(cfg, p, n):
    return (cfg[(p-1) % n], cfg[p], cfg[(p+1) % n])

def check_forced_graph_cycles(n, ms, movers):
    """Check if forced graph has cycles."""
    CL = len(movers)

    # Build configs
    cfg = [0] * n
    configs = [tuple(cfg)]
    for p in movers:
        cfg = list(configs[-1])
        cfg[p] = (cfg[p] + 1) % ms[p]
        configs.append(tuple(cfg))

    if configs[-1] != configs[0]:
        return None, "doesn't close"
    configs = configs[:-1]
    good_set = set(configs)

    # Build mover table
    cmap = {}
    for k in range(CL):
        p = movers[k]
        g = configs[k]
        L, S, R = get_context(g, p, n)
        Sp = configs[(k+1) % CL][p]
        key = (p, L, S, R)
        if key in cmap:
            return None, "duplicate context"
        cmap[key] = (Sp, k)

    # Enumerate non-good configs
    all_configs = list(itertools.product(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]

    # Build forced graph
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

    # Find nontrivial SCCs
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

    for v in non_good:
        if v not in index:
            strongconnect(v)

    nontrivial = [s for s in sccs if len(s) > 1]
    return nontrivial, configs

# Test: n=5, ms=[2,3,2,3,2], various words
n = 5
ms = [2, 3, 2, 3, 2]
CL = sum(ms)
binary_procs = [0, 2, 4]

# Try some words that don't have complementary pairs
test_words = [
    [0, 1, 2, 3, 4, 4, 3, 2, 1, 0, 1, 3],
    [0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 1, 3],
    [0, 1, 2, 3, 4, 4, 3, 2, 1, 0, 3, 1],
    [0, 1, 2, 3, 4, 0, 1, 3, 4, 2, 1, 3],
]

for word in test_words:
    # Verify it's a valid mover sequence
    counts = defaultdict(int)
    for p in word:
        counts[p] += 1
    if not all(counts[p] == ms[p] for p in range(n)):
        continue

    result, configs = check_forced_graph_cycles(n, ms, word)
    if result is None:
        continue

    # Check complementary pairs
    cfg_list = list(configs) if configs else []
    table = []
    cmap = {}
    cfg = [0] * n
    cfgs = [tuple(cfg)]
    for p in word:
        cfg = list(cfgs[-1])
        cfg[p] = (cfg[p] + 1) % ms[p]
        cfgs.append(tuple(cfg))
    cfgs = cfgs[:-1]

    for k in range(len(word)):
        p = word[k]
        g = cfgs[k]
        L, S, R = get_context(g, p, n)
        Sp = cfgs[(k+1) % len(word)][p]
        table.append((p, L, S, R, Sp))
        cmap[(p, L, S, R)] = (Sp, k)

    comp = []
    for q in binary_procs:
        fire_steps = [k for k in range(len(word)) if word[k] == q]
        if len(fire_steps) != 2:
            continue
        k1, k2 = fire_steps
        _, L1, S1, R1, _ = table[k1]
        _, L2, S2, R2, _ = table[k2]
        if L1 == L2 and R1 == R2:
            comp.append(q)

    has_scc = len(result) > 0
    scc_sizes = [len(s) for s in result]
    print(f"Word {word}: comp_procs={comp}, nontrivial SCCs: {len(result)}, sizes={scc_sizes[:5]}, has_cycle={has_scc}")

# Broader test: sample many words, check if ALL have forced graph cycles
print("\n=== Broader test: 1000 random valid words ===")
import random
random.seed(42)

mover_pool = []
for p in range(n):
    mover_pool.extend([p] * ms[p])

has_cycle_count = 0
no_cycle_count = 0
total_valid = 0

for trial in range(5000):
    word = list(mover_pool)
    random.shuffle(word)

    result, configs = check_forced_graph_cycles(n, ms, word)
    if result is None:
        continue  # Invalid word
    total_valid += 1

    if len(result) > 0:
        has_cycle_count += 1
    else:
        no_cycle_count += 1
        if no_cycle_count <= 5:
            print(f"  NO CYCLE: word={word}")

print(f"\nTotal valid words tested: {total_valid}")
print(f"Has forced cycle: {has_cycle_count}")
print(f"No forced cycle: {no_cycle_count}")

# Now try specifically with "isolated binary firing" condition
print("\n\n=== Testing ISOLATED BINARY FIRING condition ===")
# "Isolated firing" at binary proc q means:
# At q's firing steps k1, k2: the movers at k1-1 and k1+1 are NOT q±1,
# and similarly for k2.
# This means q fires in isolation: its neighbors don't fire right next to it.

def has_isolated_binary(word, ms, n):
    """Check if any binary proc has isolated firings."""
    CL = len(word)
    for q in range(n):
        if ms[q] != 2:
            continue
        fire_steps = [k for k in range(CL) if word[k] == q]
        if len(fire_steps) != 2:
            continue

        isolated = True
        for k in fire_steps:
            # Check if neighbor fires immediately before or after
            k_prev = (k - 1) % CL
            k_next = (k + 1) % CL
            if abs(word[k_prev] - q) <= 1 or (word[k_prev] - q) % n <= 1 or (q - word[k_prev]) % n <= 1:
                # Check more carefully: is word[k_prev] a neighbor of q?
                if word[k_prev] == (q - 1) % n or word[k_prev] == (q + 1) % n:
                    isolated = False
                    break
            if word[k_next] == (q - 1) % n or word[k_next] == (q + 1) % n:
                isolated = False
                break

        if isolated:
            return True, q
    return False, None

isolated_has_cycle = 0
isolated_no_cycle = 0
non_isolated_has_cycle = 0
non_isolated_no_cycle = 0

for trial in range(10000):
    word = list(mover_pool)
    random.shuffle(word)

    result, configs = check_forced_graph_cycles(n, ms, word)
    if result is None:
        continue

    is_iso, q = has_isolated_binary(word, ms, n)
    has_cycle = len(result) > 0

    if is_iso:
        if has_cycle:
            isolated_has_cycle += 1
        else:
            isolated_no_cycle += 1
            if isolated_no_cycle <= 3:
                print(f"  ISOLATED + NO CYCLE: word={word}, binary proc={q}")
    else:
        if has_cycle:
            non_isolated_has_cycle += 1
        else:
            non_isolated_no_cycle += 1

print(f"\nIsolated binary firing + has cycle: {isolated_has_cycle}")
print(f"Isolated binary firing + NO cycle: {isolated_no_cycle}")
print(f"Non-isolated + has cycle: {non_isolated_has_cycle}")
print(f"Non-isolated + NO cycle: {non_isolated_no_cycle}")
