#!/usr/bin/env python3
"""
Key insight: we don't need the FULL entry conflict state. We only need
to know if a conflict EXISTS at any of the 3 binary procs.

Better insight: track entry conflict at ONLY the middle proc's neighbors
(procs 1 and 3). The middle proc (2) can't have entry conflict by the
nature of the problem (its M and N are disjoint by construction).

Actually, the simplest approach: just do BFS with full entry conflict
tracking, but represent constraints compactly.

For 3 binary procs (1,2,3), each has 8 contexts.
Each context is: unvisited, mover-only, nonmover-only, or CONFLICT.
That's 4^8 = 65536 per proc. For 3 procs: 65536^3 ≈ 2.8e14. Too big.

BUT: we only care about DETECTING a conflict (which kills the cycle).
If we're searching for cycles that AVOID conflict, we need:
each context is unvisited/mover/nonmover (3 states, no conflict allowed).
3^8 = 6561 per proc. For 3 procs: 6561^3 ≈ 2.8e11. Still too big.

BETTER: Don't track per-context. Track per R-bucket.
Each binary proc has 2 R-buckets (R=0, R=1).
Each R-bucket has 4 (L,S) slots.
For each slot: unvisited/mover/nonmover.
3^4 = 81 per bucket. 2 buckets per proc: 81^2 = 6561. Same as before.

EVEN BETTER: we only need to track the MIDDLE proc's entry conflict
and its two neighbors'. And only during the window walk.

Let me try a different approach: just do the DFS but with a MUCH tighter
representation. Use integers to encode constraint masks.

For each proc, use two bitmasks: mover_seen (8 bits) and nonmover_seen (8 bits).
Conflict = mover_seen & nonmover_seen != 0.

Total constraint state per proc: (mover_mask, nonmover_mask) where
mover_mask & nonmover_mask == 0. Number of valid pairs:
sum over k of C(8,k) * 2^(8-k) = 3^8 = 6561. (Each bit is M, N, or neither.)

For 3 procs: 6561^3 ≈ 2.8e11. With config (72) and fc(4) and winding(~30):
72 * 4 * 60 * 2.8e11 ≈ 4.8e15. Way too big.

OK, the full state space IS too big for BFS. But for DFS with pruning,
the ACTUAL reachable states are much smaller (cycles are short).

Let me just try the DFS approach but with compact integer encoding
and see if it's fast enough for the small cases.
"""
from itertools import product as iproduct
import time

def search_with_ec(n, ms, middle, target_fc, max_path_len):
    """DFS with entry conflict tracking. Compact representation."""
    all_configs = list(iproduct(*(range(m) for m in ms)))
    cidx = {c: i for i, c in enumerate(all_configs)}
    total = len(all_configs)

    # For each proc, precompute context index: (L,S,R) -> int 0..7 (binary only)
    # For non-binary procs, context space is larger.
    # We only track entry conflict for procs 1,2,3 (the binary triple).
    binary_procs = [i for i in range(n) if ms[i] == 2]

    # Context index for binary proc p: (c[p-1], c[p], c[p+1])
    # p-1 and p+1 might not be binary, so L and R can be > 1.
    # Context space for proc p: ms[p-1] * 2 * ms[p+1]
    ctx_sizes = {}
    for p in binary_procs:
        ctx_sizes[p] = ms[(p-1)%n] * 2 * ms[(p+1)%n]

    def ctx_idx(p, c):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        return L * 2 * ms[(p+1)%n] + S * ms[(p+1)%n] + R

    def signed_step(a, b):
        d = (b - a) % n
        if d == 1: return 1
        elif d == n - 1: return -1
        return 0

    t0 = time.time()
    found = 0
    nodes = 0

    for start in range(total):
        # State: (ci, fc_mid, wind, mover_masks, nonmover_masks, movs, visited)
        # mover_masks[p] and nonmover_masks[p] are bitmasks for each binary proc
        init_mm = {p: 0 for p in binary_procs}
        init_nm = {p: 0 for p in binary_procs}

        stack = [(start, frozenset([start]), [0]*n, 0, dict(init_mm), dict(init_nm), [])]

        while stack:
            ci, visited, fc, wind, mm, nm, movs = stack.pop()
            nodes += 1

            if len(visited) > max_path_len: continue

            c = all_configs[ci]

            for mover in range(n):
                S = c[mover]
                possible_vals = [v for v in range(ms[mover]) if v != S]

                for new_val in possible_vals:
                    # Check entry conflict constraints
                    # Mover proc: its context becomes mover
                    valid = True
                    new_mm = dict(mm)
                    new_nm = dict(nm)

                    if mover in binary_procs:
                        ci_m = ctx_idx(mover, c)
                        if nm[mover] & (1 << ci_m):
                            continue  # conflict at mover proc
                        new_mm[mover] = mm[mover] | (1 << ci_m)

                    # Non-mover procs: their contexts become nonmover
                    for p in binary_procs:
                        if p == mover: continue
                        ci_p = ctx_idx(p, c)
                        if mm[p] & (1 << ci_p):
                            valid = False; break
                        new_nm[p] = nm[p] | (1 << ci_p)

                    if not valid: continue

                    new_c = list(c)
                    new_c[mover] = new_val
                    new_ci = cidx[tuple(new_c)]
                    new_fc = list(fc); new_fc[mover] += 1
                    new_wind = wind
                    if movs: new_wind += signed_step(movs[-1], mover)

                    # Check cycle closure
                    if new_ci == start and len(visited) >= 3:
                        fw = new_wind + signed_step(mover, movs[0])
                        if fw == 0 and new_fc[middle] >= target_fc:
                            found += 1
                            if found <= 5:
                                print(f"  FOUND: len={len(visited)}, fc={new_fc}")
                            if found > 100:
                                return found, time.time() - t0, nodes
                        continue

                    if new_ci in visited: continue

                    # Prune
                    remaining = max_path_len - len(visited)
                    if new_fc[middle] + remaining < target_fc: continue

                    stack.append((new_ci, visited | {new_ci}, new_fc, new_wind,
                                  new_mm, new_nm, movs + [mover]))

    return found, time.time() - t0, nodes

# Run tests
tests = [
    (5, [2,2,2,2,2], 2, 3, 14, "all binary"),
    (5, [2,2,2,2,2], 2, 3, 32, "all binary (full)"),
]

for n, ms, mid, tf, mpl, desc in tests:
    total = 1
    for m in ms: total *= m
    print(f"\n=== {desc}: ms={ms}, {total} configs, max_path={mpl} ===")
    f, t, nodes = search_with_ec(n, ms, mid, tf, mpl)
    print(f"Result: {f} found, {t:.1f}s, {nodes} nodes")
    if f == 0:
        print("*** CONFIRMED: fc>=3 impossible with entry conflict! ***")

# Now try mixed
print("\n" + "="*60)
print("Now testing mixed systems...")
mixed_tests = [
    (5, [3,2,2,2,3], 2, 3, 18, "ternary boundaries"),
]
for n, ms, mid, tf, mpl, desc in mixed_tests:
    total = 1
    for m in ms: total *= m
    print(f"\n=== {desc}: ms={ms}, {total} configs, max_path={mpl} ===")
    f, t, nodes = search_with_ec(n, ms, mid, tf, mpl)
    print(f"Result: {f} found, {t:.1f}s, {nodes} nodes")
    if f == 0:
        print("*** CONFIRMED: fc>=3 impossible with entry conflict! ***")
