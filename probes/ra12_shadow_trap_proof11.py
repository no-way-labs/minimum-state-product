"""
Shadow Trap Proof — Part 11: Construct proper sweeps.

For ms = [2,3,2,3,2] at n=5:
Binary at 0, 2, 4 (non-consecutive).
CL = 12.

A proper sweep should have:
- Phase 1 (right): movers go 0,1,2,3,4 (each fires once)
- Phase 2 (left): movers go 4,3,2,1,0 (each fires once)
- Phase 3 (extra ternary): procs 1,3 each fire once more (third firing)

In Phase 1, all procs go from 0 to 1.
In Phase 2, binary goes 1->0, ternary goes 1->2.
In Phase 3, ternary goes 2->0.

For binary proc 0:
  Step 0: context (0,0,0) -> fires 0->1 (neighbors: left=proc4=0, right=proc1=0)
  Step 9: context (?,1,?) -> fires 1->0

At step 9 (during left sweep, when proc 0 fires second time):
  Before step 9, in the left sweep: proc 4 fired (step 5), 3 (step 6), 2 (step 7), 1 (step 8)
  After their firings: proc 4 went 1->0, proc 3 went 1->2, proc 2 went 1->0, proc 1 went 1->2
  So at step 9, proc 0's left neighbor (proc 4) has value 0,
  and right neighbor (proc 1) has value 2.
  Context: (0, 1, 2) -> fires 1->0

For binary proc 0:
  Step 0: (0, 0, 0) -> 1
  Step 9: (0, 1, 2) -> 0
  L matches (both 0): YES! R doesn't match (0 vs 2).

Hmm, for proc 0 the left neighbor (proc 4) value IS the same at both firings!
It's 0 both times because: at step 0, proc 4 hasn't fired yet (value 0).
At step 9, proc 4 has gone 0->1->0 (fired twice), so value is 0 again.

But the right neighbor (proc 1) changed: 0 at step 0, 2 at step 9.

For a complementary pair, we need BOTH L and R to match.

CRITICAL QUESTION: Is there a sweep structure where some binary proc
has matching (L,R) at both firings?

For binary proc q with LEFT neighbor L_q and RIGHT neighbor R_q:
- At q's first firing (right sweep): L_q hasn't fired yet, R_q hasn't fired yet.
  L = initial(L_q) = 0, R = initial(R_q) = 0
- At q's second firing (left sweep): L_q has fired twice (back to 0 if binary)
  or twice (value 2 if ternary). R_q has fired twice (back to 0 if binary)
  or twice (value 2 if ternary).

So L_q at second firing = 0 if L_q is binary, 2 if L_q is ternary.
R_q at second firing = 0 if R_q is binary, 2 if R_q is ternary.

For L match: 0 == L_at_second. This requires L_q is BINARY (so it returns to 0).
For R match: 0 == R_at_second. This requires R_q is BINARY (so it returns to 0).

So for binary proc q to form a complementary pair, BOTH its neighbors
must be binary! But we have NON-CONSECUTIVE binary, meaning no two
binary procs are adjacent. So no binary proc has a binary neighbor.

THIS IS WHY THE COMPLEMENTARY PAIR APPROACH FAILS FOR NON-CONSECUTIVE BINARY!

The ternary neighbors DON'T return to their original value after 2 firings.
They go 0->1->2, and at the second firing of q, they're at value 2 ≠ 0.

So the shadow trap for non-consecutive binary CANNOT be a simple 2-cycle.
It must be a longer cycle using a different mechanism.

Let me now investigate what shadow cycles ACTUALLY exist for non-consecutive binary.
"""

import itertools
from collections import defaultdict
import sys
sys.setrecursionlimit(10000)

def get_context(cfg, p, n):
    return (cfg[(p-1) % n], cfg[p], cfg[(p+1) % n])

n = 5
ms = [2, 3, 2, 3, 2]
CL = sum(ms)  # 12

# Build proper right-left-extra sweep
# Right: 0,1,2,3,4
# Left: 4,3,2,1,0
# Extra: 1,3
movers = [0,1,2,3,4, 4,3,2,1,0, 1,3]

cfg = [0] * n
configs = [tuple(cfg)]
for p in movers:
    cfg = list(configs[-1])
    cfg[p] = (cfg[p] + 1) % ms[p]
    configs.append(tuple(cfg))

if configs[-1] == configs[0]:
    print("Sweep closes!")
    configs = configs[:-1]
else:
    print(f"Doesn't close: start={configs[0]}, end={configs[-1]}")
    # Fix: the extra phase should be ternary procs going 2->0
    # After right+left: binary at 0, ternary at 2
    # Extra: 1,3 go 2->0
    # But movers 1,3 each fires ms[1]-2=1 time in the extra phase
    # Let me trace manually

    print("\nManual trace:")
    cfg = [0] * n
    print(f"  Start: {tuple(cfg)}")
    all_movers = [0,1,2,3,4, 4,3,2,1,0, 1,3]
    for i, p in enumerate(all_movers):
        cfg[p] = (cfg[p] + 1) % ms[p]
        print(f"  Step {i}: fire proc {p} -> {tuple(cfg)}")

# The order matters. Let me try specific orderings.
# Right sweep: 0,1,2,3,4 — all go from 0 to 1
# Left sweep: 4,3,2,1,0 — binary goes 1->0, ternary goes 1->2
# Extra right: 1,3 — ternary goes 2->0

movers = [0,1,2,3,4, 4,3,2,1,0, 1,3]

cfg = [0] * n
configs = [tuple(cfg)]
print(f"\nTrace with movers {movers}:")
for i, p in enumerate(movers):
    cfg_list = list(configs[-1])
    cfg_list[p] = (cfg_list[p] + 1) % ms[p]
    configs.append(tuple(cfg_list))
    print(f"  Step {i}: fire proc {p}: {configs[-2]} -> {configs[-1]}")

print(f"Start: {configs[0]}, End: {configs[-1]}")

if configs[-1] == configs[0]:
    configs = configs[:-1]
    good_set = set(configs)
    print(f"\nGood cycle of length {len(configs)}, distinct configs: {len(good_set)}")

    # Build mover context table
    cmap = {}
    for k in range(CL):
        p = movers[k]
        g = configs[k]
        L, S, R = get_context(g, p, n)
        Sp = configs[(k+1) % CL][p]
        key = (p, L, S, R)
        cmap[key] = (Sp, k)
        print(f"  Step {k:2d}: proc {p}, ctx=({L},{S},{R})->{Sp}")

    # Build forced graph on non-good configs
    all_configs = list(itertools.product(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]

    print(f"\nNon-good configs: {len(non_good)}")

    forced_graph = {}
    for c in non_good:
        successors = set()
        for p in range(n):
            ctx = get_context(c, p, n)
            key = (p,) + ctx
            if key in cmap:
                Sp, step = cmap[key]
                new_cfg = list(c)
                new_cfg[p] = Sp
                nc = tuple(new_cfg)
                if nc not in good_set:
                    successors.add(nc)
        forced_graph[c] = list(successors)

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

    for v in non_good:
        if v not in index:
            strongconnect(v)

    nontrivial = [s for s in sccs if len(s) > 1]
    print(f"\nNontrivial SCCs: {len(nontrivial)}")
    for i, scc in enumerate(nontrivial):
        print(f"  SCC {i}: size {len(scc)}")

    # Analyze each SCC in detail
    for scc in nontrivial:
        scc_set = set(scc)
        print(f"\n  Detailed SCC analysis (size {len(scc)}):")
        for c in sorted(scc)[:10]:
            # Which procs are forced in this config?
            forced_procs = []
            for p in range(n):
                ctx = get_context(c, p, n)
                key = (p,) + ctx
                if key in cmap:
                    Sp, step = cmap[key]
                    new = list(c)
                    new[p] = Sp
                    nc = tuple(new)
                    if nc in scc_set:
                        forced_procs.append((p, step))
            min_hamming = min(sum(1 for a,b in zip(c,g) if a!=b) for g in configs)
            print(f"    {c}: forced={forced_procs}, Hamming={min_hamming}")

    # Are there configs where transitions go TO good configs?
    to_good = 0
    for c in non_good:
        for p in range(n):
            ctx = get_context(c, p, n)
            key = (p,) + ctx
            if key in cmap:
                Sp, step = cmap[key]
                new = list(c)
                new[p] = Sp
                nc = tuple(new)
                if nc in good_set:
                    to_good += 1
    print(f"\nTransitions from non-good TO good: {to_good}")
else:
    print("Cycle doesn't close, trying alternative ordering...")

    # Try: extra phase goes 3,1 instead of 1,3
    movers = [0,1,2,3,4, 4,3,2,1,0, 3,1]
    cfg = [0] * n
    configs = [tuple(cfg)]
    for p in movers:
        cfg_list = list(configs[-1])
        cfg_list[p] = (cfg_list[p] + 1) % ms[p]
        configs.append(tuple(cfg_list))
    print(f"Try 3,1 extra: start={configs[0]}, end={configs[-1]}")
