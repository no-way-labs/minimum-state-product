#!/usr/bin/env python3
"""
GPT's approach: reachability on (WinState × Sat3 × WindingSummary).

Instead of DFS with constraint tracking, build the full transition graph
on the LIFTED state and check reachability.

State: (window_config, fc_middle, winding_balance)
- window_config: tuple of values for 5 procs
- fc_middle: 0,1,2,3 (saturating at 3 = ">=3")
- winding: integer tracking CW-CCW displacement

Transitions: for each (state, mover_proc, new_value):
  - compute new window config
  - update fc_middle if mover = middle proc
  - update winding

Entry conflict: NOT tracked in the state. Instead, we check:
  does there exist ANY cycle (s,0,0) -> ... -> (s,>=3,0)?

If no such path exists even WITHOUT entry conflict constraints,
then certainly no valid cycle exists. This is a SOUND OVER-APPROXIMATION.

If a path DOES exist, it might be spurious (entry conflict kills it).
Then we refine.

Key insight: without entry conflict, this is just graph reachability
on a small finite graph. INSTANT.
"""
from itertools import product as iproduct
from collections import deque
import time

def check_reachability(n, ms, middle, max_fc_target):
    """Check if middle proc can reach fc >= max_fc_target in a zero-winding cycle."""
    all_configs = list(iproduct(*(range(m) for m in ms)))
    cidx = {c: i for i, c in enumerate(all_configs)}
    total = len(all_configs)

    # Lifted state: (config_idx, fc_middle_saturated, winding)
    # fc_middle in {0, 1, 2, ..., max_fc_target}
    # winding: bounded by cycle length, which is bounded by total configs
    # For zero-winding cycle: winding must return to 0
    # Max winding: at most total steps, each ±1, so |winding| ≤ total
    max_wind = total  # conservative bound

    # BFS from all (start, 0, 0) states
    # Look for: (start, >=target, 0) reachable from (start, 0, 0)

    t0 = time.time()

    # For each starting config, do BFS
    found = 0

    for start_ci in range(total):
        # BFS state: (config_idx, fc_sat, winding, last_mover)
        # We need last_mover to compute winding steps
        # State for BFS: (config_idx, fc_sat, winding, last_mover)
        # Actually: winding is computed from consecutive movers.
        # wind += signed_step(prev_mover, curr_mover)
        # So we need to track last_mover as part of state.

        # State: (ci, fc_sat, winding, last_mover)
        # last_mover in range(n) or -1 (initial)
        # Start: (start_ci, 0, 0, -1)
        # Goal: (start_ci, >=target, 0, any)... but need final winding
        # which includes step from last_mover back to first_mover.

        # This is complex. Let's simplify:
        # Track (ci, fc_sat, winding, last_mover, first_mover)
        # That's a lot of state. Let's bound it.
        # ci: total configs
        # fc_sat: max_fc_target + 1 values
        # winding: [-total, total]
        # last_mover: n
        # first_mover: n
        # Total: total * (target+1) * (2*total+1) * n * n

        # For ms=[3,2,2,2,3], total=72, target=3, n=5:
        # 72 * 4 * 145 * 5 * 5 = 72*4*145*25 = 1,044,000. Very manageable.

        # But we also need first_mover fixed. So fix it.
        for first_mover in range(n):
            # BFS from (start_ci, 0, 0, first_mover) — first step already taken
            # Actually let's just track from the initial state.
            # Step 1: choose first mover, apply transition.
            c0 = all_configs[start_ci]
            S0 = c0[first_mover]
            possible_vals = [v for v in range(ms[first_mover]) if v != S0]

            for new_val in possible_vals:
                new_c = list(c0)
                new_c[first_mover] = new_val
                new_ci = cidx[tuple(new_c)]
                fc0 = 1 if first_mover == middle else 0
                fc_sat = min(fc0, max_fc_target)

                # BFS state: (ci, fc_sat, winding, last_mover)
                init_state = (new_ci, fc_sat, 0, first_mover)

                visited = {init_state}
                queue = deque([init_state])

                while queue:
                    ci, fc, wind, last_m = queue.popleft()
                    c = all_configs[ci]

                    for mover in range(n):
                        S = c[mover]
                        pvals = [v for v in range(ms[mover]) if v != S]
                        for nv in pvals:
                            nc = list(c)
                            nc[mover] = nv
                            nci = cidx[tuple(nc)]
                            nfc = min(fc + (1 if mover == middle else 0), max_fc_target)

                            # Winding step
                            d = (mover - last_m) % n
                            if d == 1: nwind = wind + 1
                            elif d == n - 1: nwind = wind - 1
                            else: nwind = wind  # non-adjacent: winding contribution = 0

                            # Check cycle closure
                            if nci == start_ci and nfc >= max_fc_target:
                                # Final winding: add step from mover back to first_mover
                                d2 = (first_mover - mover) % n
                                if d2 == 1: fwind = nwind + 1
                                elif d2 == n - 1: fwind = nwind - 1
                                else: fwind = nwind

                                if fwind == 0:
                                    found += 1
                                    if found <= 3:
                                        print(f"  Potential cycle: start={start_ci}, fc_mid>={max_fc_target}, wind=0")
                                    if found > 100:
                                        elapsed = time.time() - t0
                                        return found, elapsed

                            # Bound winding
                            if abs(nwind) > max_wind: continue

                            ns = (nci, nfc, nwind, mover)
                            if ns not in visited:
                                visited.add(ns)
                                queue.append(ns)

    elapsed = time.time() - t0
    return found, elapsed

# Test cases
tests = [
    (5, [2,2,2,2,2], 2, "all binary n=5"),
    (5, [3,2,2,2,3], 2, "ternary boundaries"),
    (5, [4,2,2,2,4], 2, "quaternary boundaries"),
    (5, [3,2,2,2,4], 2, "mixed 3/4 boundaries"),
]

for n, ms, mid, desc in tests:
    total = 1
    for m in ms: total *= m
    print(f"\n=== {desc}: ms={ms}, {total} configs ===")
    print(f"Looking for zero-winding cycle with fc(proc {mid}) >= 3 (NO entry conflict check)")
    f, t = check_reachability(n, ms, mid, 3)
    print(f"Result: {f} potential cycles found in {t:.1f}s")
    if f == 0:
        print("*** NO cycles even without entry conflict! fc>=3 is impossible! ***")
    else:
        print(f"*** {f} potential cycles (may be killed by entry conflict) ***")
