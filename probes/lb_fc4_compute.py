"""
Computational check: enumerate good cycles with all binary fc ≥ 4.

For small n (n=4,5), enumerate all possible "abstract good cycles" —
mover word + value sequence — and check which have all binary fc ≥ 4.

For those that do: check if they have entry conflict.
"""

import itertools
from collections import Counter, defaultdict

def enumerate_abstract_cycles(n, ms, max_cl=30, check_ec=True):
    """Enumerate abstract good cycles for state vector ms.

    An abstract good cycle is a sequence of (config, mover) pairs where:
    1. Each consecutive pair: config_{t+1} differs from config_t only at position mover_t
    2. config_{t+1}[mover_t] ≠ config_t[mover_t]
    3. Cycle: config_0 = config_{CL} (wraps around)
    4. All configs distinct
    5. Each config has exactly one privileged proc (the mover)
       — but we can't check this without a transition function!

    Actually: an abstract good cycle is just a sequence of configs forming a cycle
    in the "single-step" graph, where each step changes exactly one processor's value.
    The mover at each step is the processor that changed.

    For a valid system to realize this cycle: we need consistent transition functions.
    Entry conflict = impossible to find consistent transition functions.

    For this computation: enumerate all simple cycles in the single-step graph.
    """

    # This is expensive. For n=4, ms=(2,3,2,3), product=36.
    # Let me build the graph and find cycles.

    product = 1
    for m in ms:
        product *= m

    if product > 200:
        print(f"  Product {product} too large for enumeration")
        return []

    # Generate all configs
    all_cfgs = list(itertools.product(*(range(m) for m in ms)))
    cfg_to_idx = {c: i for i, c in enumerate(all_cfgs)}

    # Build adjacency: c1 → (c2, mover) where c2 differs from c1 at exactly one position
    adj = defaultdict(list)
    for c in all_cfgs:
        for i in range(n):
            for v in range(ms[i]):
                if v != c[i]:
                    c2 = list(c)
                    c2[i] = v
                    c2 = tuple(c2)
                    adj[c].append((c2, i))

    binary_procs = [i for i in range(n) if ms[i] == 2]
    B = len(binary_procs)

    # For small cycles: use DFS to find all simple cycles
    # Focus on cycles where all binary fc ≥ 4
    # Min CL = 4*B + 2*(n-B) = 2n + 2B

    min_cl = 4 * B + 2 * (n - B)
    print(f"  n={n}, ms={ms}, product={product}, min_cl_for_fc4={min_cl}")

    # DFS from each starting config
    cycles_total = 0
    cycles_allfc2plus = 0
    cycles_allbinfc4 = 0
    cycles_allbinfc4_with_ec = 0
    cycles_allbinfc4_no_ec = 0

    # Only start from config index 0 to avoid counting same cycle multiple times
    # (we'll still count rotations, but limit search)
    start = all_cfgs[0]

    def dfs(cur, path, visited, movers, max_depth):
        nonlocal cycles_total, cycles_allfc2plus, cycles_allbinfc4
        nonlocal cycles_allbinfc4_with_ec, cycles_allbinfc4_no_ec

        if len(path) > max_depth:
            return

        for nxt, mover in adj[cur]:
            if nxt == start and len(path) >= min_cl:
                # Cycle found
                mover_seq = movers + [mover]
                fc = Counter(mover_seq)
                cl = len(mover_seq)

                # Check all procs fire at least once
                if any(fc.get(i, 0) == 0 for i in range(n)):
                    continue

                cycles_total += 1

                # Check all fc ≥ 2
                if any(fc.get(i, 0) < 2 for i in range(n)):
                    continue
                cycles_allfc2plus += 1

                # Check all binary fc ≥ 4
                bin_fcs = [fc[b] for b in binary_procs]
                if not all(f >= 4 for f in bin_fcs):
                    continue

                cycles_allbinfc4 += 1

                # Check entry conflict
                if check_ec:
                    full_path = path + [nxt]  # but nxt == start, so wrap
                    # For each proc i: collect mover contexts and non-mover contexts
                    has_ec = False
                    for i in range(n):
                        mover_contexts = set()
                        nonmover_contexts = set()
                        for t in range(cl):
                            c = path[t]
                            L = c[(i - 1) % n]
                            S = c[i]
                            R = c[(i + 1) % n]
                            ctx = (L, S, R)
                            if mover_seq[t] == i:
                                mover_contexts.add(ctx)
                            else:
                                nonmover_contexts.add(ctx)

                        overlap = mover_contexts & nonmover_contexts
                        if overlap:
                            has_ec = True
                            break

                    if has_ec:
                        cycles_allbinfc4_with_ec += 1
                    else:
                        cycles_allbinfc4_no_ec += 1
                        # Print this cycle for analysis
                        if cycles_allbinfc4_no_ec <= 3:
                            print(f"\n  NO-EC cycle found! CL={cl}, fc={dict(fc)}")
                            print(f"    movers: {mover_seq}")
                            for t in range(min(cl, 20)):
                                print(f"    step {t}: config={path[t]}, mover={mover_seq[t]}")

                if cycles_allbinfc4 >= 1000:
                    return

            elif nxt not in visited and len(path) < max_depth:
                visited.add(nxt)
                dfs(nxt, path + [nxt], visited, movers + [mover], max_depth)
                visited.remove(nxt)

        if cycles_allbinfc4 >= 1000:
            return

    visited = {start}
    dfs(start, [start], visited, [], max_cl)

    print(f"\n  Results: total={cycles_total}, allfc2+={cycles_allfc2plus}, "
          f"allbinfc4={cycles_allbinfc4}")
    if check_ec:
        print(f"  EC={cycles_allbinfc4_with_ec}, no-EC={cycles_allbinfc4_no_ec}")

    return cycles_allbinfc4_no_ec


# Test at n=4 (small)
print("=== n=4, ms=(2,3,2,3), product=36 ===")
print("Sub-threshold check: 36 < 4*3^2 = 36. NOT sub-threshold (= threshold)")
print("Try ms=(2,2,3,3), product=36 = threshold, skip")
print()

# Actually for n=4: threshold = 4*3^2 = 36.
# Sub-threshold means product < 36. With B=2: 2^2 * 3^2 = 36 = threshold. Not sub-threshold.
# With B=3: 2^3 * 3 = 24 < 36. ✓
# ms=(2,2,2,3): product=24, 3 binary.
# But: 3 binary at n=4 means 3 consecutive binary (only 4 procs, 3 of which binary).

print("=== n=4, ms=(2,2,2,3), product=24 ===")
print("3 consecutive binary at n=4. B=3.")
# Not relevant to non-consecutive case. Let's try n=5.

# n=5: threshold = 4*3^3 = 108.
# B=3: 2^3 * 3^2 = 72 < 108. ✓
# Non-consecutive: ms permutations of (2,2,2,3,3) with no 3 consecutive binary.

# ms=(2,3,2,3,2): binary at 0,2,4 — non-consecutive, pairwise non-adjacent.
# ms=(2,2,3,2,3): binary at 0,1,3 — 0,1 consecutive. 3 binary, no 3 consecutive. ✓

print("\n=== n=5, ms=(2,3,2,3,2), product=72 ===")
print("Non-consecutive binary at 0,2,4. Min CL for allbinfc4: 4*3+2*2=16")
result = enumerate_abstract_cycles(5, [2,3,2,3,2], max_cl=20, check_ec=True)

print(f"\n\n=== SUMMARY ===")
if result == 0:
    print("ALL cycles with all-binary-fc≥4 have entry conflict! (or none exist)")
    print("This supports the theorem.")
elif result is not None and result > 0:
    print(f"{result} cycles with all-binary-fc≥4 and NO entry conflict!")
    print("The theorem might need a different mechanism.")
