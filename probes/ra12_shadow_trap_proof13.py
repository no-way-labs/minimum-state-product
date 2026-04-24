"""
Shadow Trap Proof — Part 13: The Two-Proc Interaction Mechanism.

KEY DISCOVERY: In a sweep good cycle, adjacent procs p and p+1 can
interact to form a closed cycle in the forced graph.

This happens when:
1. Procs p and p+1 are each other's neighbors
2. The mover table entries for p and p+1 have compatible contexts
3. There exist "frozen" values for all other procs that create
   the right contexts for p and p+1

The mechanism:
- Proc p fires, changing its value. This changes p+1's left context.
- With the new left context, p+1's entry activates, so p+1 fires.
- p+1 firing changes p's right context.
- With the new right context, another entry for p activates.
- Continue until both return to original values.

This is a LOCAL interaction: only procs p and p+1 change values.
All other procs are frozen at values that make the contexts work.

QUESTION: Does EVERY sweep with non-consecutive binary have such a
two-proc interaction cycle?

For non-consecutive binary:
- Binary procs are at positions i1, i2, i3 with no two adjacent.
- Between each pair of binary procs, there's at least one ternary proc.

Consider binary proc q and its ternary neighbor t = q+1.
In the sweep:
- q fires twice: (L1, 0, R1) -> 1 and (L2, 1, R2) -> 0
- t fires three times through values 0 -> 1 -> 2 -> 0

If we freeze all procs except q and t, we need:
- q's left neighbor value to match L1 or L2
- t's right neighbor value to match some good-cycle value
- The interaction between q and t to close

This is getting complex. Let me instead take a DIFFERENT approach:
prove that the existing shadow cycle construction works, rather than
finding a new mechanism.

Actually, let me reconsider the problem. The claim from the problem
statement is: "Following forced transitions from a shifted good config
creates a cycle of length CL among non-good configs."

Let me verify this claim with the proper interpretation: we START from
a specific shifted config and follow the forced graph (picking a specific
scheduler), and always get a CL-length cycle.

The "shifted good config" might mean: take a good config and shift
it by a GLOBAL offset on the ring (rotate all values).
"""

import itertools
from collections import defaultdict

def get_context(cfg, p, n):
    return (cfg[(p-1) % n], cfg[p], cfg[(p+1) % n])

n = 9
ms = [2, 3, 2, 3, 2, 3, 3, 3, 3]
CL = sum(ms)  # 24

# Build sweep
movers = list(range(n)) + list(range(n-1, -1, -1)) + [p for p in range(n) if ms[p] == 3]

cfg = [0] * n
configs = [tuple(cfg)]
for p in movers:
    cfg = list(configs[-1])
    cfg[p] = (cfg[p] + 1) % ms[p]
    configs.append(tuple(cfg))

print(f"Movers: {movers}")
print(f"CL={CL}, len(movers)={len(movers)}")
print(f"Start: {configs[0]}, End: {configs[-1]}")

if configs[-1] != configs[0]:
    print("Doesn't close! Let me try sorted extra phase")
    ternary = sorted([p for p in range(n) if ms[p] == 3])
    movers = list(range(n)) + list(range(n-1, -1, -1)) + ternary
    cfg = [0] * n
    configs = [tuple(cfg)]
    for p in movers:
        cfg = list(configs[-1])
        cfg[p] = (cfg[p] + 1) % ms[p]
        configs.append(tuple(cfg))
    print(f"Try 2: Start: {configs[0]}, End: {configs[-1]}")

if configs[-1] == configs[0]:
    configs = configs[:-1]
    good_set = set(configs)

    # Build cmap
    cmap = {}
    for k in range(CL):
        p = movers[k]
        g = configs[k]
        L, S, R = get_context(g, p, n)
        Sp = configs[(k+1) % CL][p]
        cmap[(p, L, S, R)] = (Sp, k)

    print(f"\nGood configs: {len(good_set)}")
    print(f"Unique contexts: {len(cmap)}")

    # Now test: for each binary proc q, shift its value in g_0
    # and follow the forced graph
    g0 = configs[0]
    print(f"\ng_0 = {g0}")

    for q in range(n):
        if ms[q] != 2:
            continue
        v = 1 - g0[q]  # Flip binary value
        shifted = list(g0)
        shifted[q] = v
        shifted = tuple(shifted)

        if shifted in good_set:
            print(f"\nFlip proc {q}: {shifted} is GOOD")
            continue

        # Follow forced transitions, using "lowest proc" scheduler
        orbit = [shifted]
        current = shifted
        cycle_len = None
        for step in range(CL * 3):
            forced = []
            for p in range(n):
                ctx = get_context(current, p, n)
                key = (p,) + ctx
                if key in cmap:
                    Sp, k = cmap[key]
                    new_cfg = list(current)
                    new_cfg[p] = Sp
                    nc = tuple(new_cfg)
                    if nc not in good_set:
                        forced.append((p, k, nc))
            if not forced:
                print(f"\nFlip proc {q}: STUCK after {step} steps")
                break
            forced.sort()
            p, k, nc = forced[0]
            if nc == shifted:
                cycle_len = step + 1
                print(f"\nFlip proc {q}: {shifted}")
                print(f"  CYCLE of length {cycle_len}")
                break
            orbit.append(nc)
            current = nc

        if cycle_len is None and len(orbit) > CL:
            # Check if we passed through the start
            pass
else:
    print("Still doesn't close!")

    # Let me just use the KNOWN working sweep pattern for 3 consecutive binary
    print("\n\n=== Using known sweep: consecutive binary ===")
    n = 9
    ms = [2, 2, 2] + [3] * (n - 3)
    CL = sum(ms)

    movers = list(range(n)) + list(range(n-1, -1, -1)) + list(range(3, n))

    cfg = [0] * n
    configs = [tuple(cfg)]
    for p in movers:
        cfg = list(configs[-1])
        cfg[p] = (cfg[p] + 1) % ms[p]
        configs.append(tuple(cfg))

    print(f"n={n}, ms={ms}, CL={CL}")
    print(f"Movers: {movers}")
    print(f"Start: {configs[0]}, End: {configs[-1]}")

    if configs[-1] == configs[0]:
        configs = configs[:-1]
        good_set = set(configs)

        cmap = {}
        for k in range(CL):
            p = movers[k]
            g = configs[k]
            L, S, R = get_context(g, p, n)
            Sp = configs[(k+1) % CL][p]
            cmap[(p, L, S, R)] = (Sp, k)

        print(f"Good configs: {len(good_set)}, Unique contexts: {len(cmap)}")

        # Test shadow cycle via forced graph
        g0 = configs[0]
        print(f"g_0 = {g0}")

        # Check complementary pairs
        for q in range(n):
            if ms[q] != 2:
                continue
            fire_steps = [k for k in range(CL) if movers[k] == q]
            print(f"\nBinary proc {q}: fires at steps {fire_steps}")
            for k in fire_steps:
                p = movers[k]
                g = configs[k]
                L, S, R = get_context(g, p, n)
                Sp = configs[(k+1) % CL][p]
                print(f"  Step {k}: ({L},{S},{R}) -> {Sp}")

        # Now look at the SIZE of the nontrivial SCC
        all_cfgs = list(itertools.product(*[range(m) for m in ms]))
        non_good = [c for c in all_cfgs if c not in good_set]
        print(f"\nTotal: {len(all_cfgs)}, Good: {len(good_set)}, Non-good: {len(non_good)}")

        # This is too large to enumerate for n=9. Let me use n=5 instead.

# Let me go back to n=5 with the KNOWN shadow cycle
print("\n\n=== Known shadow cycle: n=5, ms=[2,2,2,3,3] ===")
n = 5
ms = [2, 2, 2, 3, 3]
CL = sum(ms)  # 12

movers = list(range(n)) + list(range(n-1, -1, -1)) + [3, 4]

cfg = [0] * n
configs = [tuple(cfg)]
for p in movers:
    cfg = list(configs[-1])
    cfg[p] = (cfg[p] + 1) % ms[p]
    configs.append(tuple(cfg))

print(f"Start: {configs[0]}, End: {configs[-1]}")

if configs[-1] == configs[0]:
    configs = configs[:-1]
    good_set = set(configs)

    cmap = {}
    table_entries = []
    for k in range(CL):
        p = movers[k]
        g = configs[k]
        L, S, R = get_context(g, p, n)
        Sp = configs[(k+1) % CL][p]
        cmap[(p, L, S, R)] = (Sp, k)
        table_entries.append((p, L, S, R, Sp))
        print(f"  Step {k:2d}: proc {p}, ({L},{S},{R})->{Sp}")

    # Complementary pairs
    print("\nComplementary pairs:")
    for q in range(n):
        if ms[q] != 2:
            continue
        fire_steps = [k for k in range(CL) if movers[k] == q]
        k1, k2 = fire_steps
        _, L1, S1, R1, _ = table_entries[k1]
        _, L2, S2, R2, _ = table_entries[k2]
        match = "YES" if (L1 == L2 and R1 == R2) else "NO"
        print(f"  Proc {q}: ({L1},{S1},{R1})->({L2},{S2},{R2}) LR match={match}")

    # Build forced graph
    all_cfgs = list(itertools.product(*[range(m) for m in ms]))
    non_good = [c for c in all_cfgs if c not in good_set]
    print(f"\nTotal: {len(all_cfgs)}, Good: {len(good_set)}, Non-good: {len(non_good)}")

    forced_graph = {}
    for c in non_good:
        succs = []
        for p in range(n):
            ctx = get_context(c, p, n)
            key = (p,) + ctx
            if key in cmap:
                Sp, step = cmap[key]
                new = list(c)
                new[p] = Sp
                nc = tuple(new)
                if nc not in good_set:
                    succs.append(nc)
        forced_graph[c] = succs

    # Find nontrivial SCCs
    import sys
    sys.setrecursionlimit(10000)

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
    for scc in nontrivial:
        print(f"  Size {len(scc)}: {sorted(scc)[:5]}...")

    # Check known shadow cycle formula
    from shadow_closure_proof import shadow_config, sigma, d_shift

    print("\n=== Known shadow cycle formula ===")
    shadow_configs = [shadow_config(k, n) for k in range(2*n)]
    print(f"Shadow cycle has {len(shadow_configs)} configs")
    print(f"Distinct: {len(set(shadow_configs))}")
    for k in range(2*n):
        sc = shadow_configs[k]
        in_good = sc in good_set
        print(f"  k={k}: {sc}, in good={in_good}")
