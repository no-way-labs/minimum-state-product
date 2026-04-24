#!/usr/bin/env python3
"""
Open 5-cell window automaton: can the middle binary fire 3+ times
in a zero-winding closed walk?

Window: [bL, b0, b1, b2, bR] where b0,b1,b2 are binary, bL and bR
are boundary procs.

For the sub-threshold case: bL and bR are also binary (3 consecutive
binary means the neighbors could be anything, but let's start with
all-binary boundaries, then try ternary).

Actions: extL (bL fires), fire0 (b0=p-1 fires), fire1 (b1=p fires),
         fire2 (b2=p+1 fires), extR (bR fires)

Transitions:
- fire_i: proc i is privileged (f(L,S,R) != S), toggles.
  But we don't know the transition function! So: any toggle is allowed
  as long as entry conflict is maintained.
- extL: bL toggles (binary). bL's context includes an unseen outer
  neighbor, so we existentially quantify: any toggle of bL is allowed.
- extR: same for bR.

Entry conflict: for each proc in the window, no (L,S,R) context
appears as both mover and non-mover.

State: (bL, b0, b1, b2, bR, fc_middle, winding, entry_constraints)

The entry_constraints are the mover/non-mover sets per proc.
This makes the state space large. Let's see how large.

For each of 5 binary procs: 8 possible (L,S,R) contexts.
Each can be: unseen, mover, or nonmover. That's 3^8 per proc.
3^8 = 6561 per proc, 5 procs: 6561^5 ≈ 1.2 × 10^19. WAY too big.

BETTER: don't track full entry constraints. Instead, just track
the window state + fc counter + winding. The entry conflict check
is done lazily during the walk.

Actually: for the reachability check, we need to track enough state
that revisiting the same state means a valid cycle exists.

Simplest approach: BFS/DFS on (window_config, fc_counter, mover_constraints)
but constraints make state space huge.

ALTERNATIVE: Just do the direct cycle search on the 5-window,
with entry conflict tracked. The window has 2^5 = 32 configs (all binary).
With fc counter up to 3 and entry constraints: manageable.

Let's just do it: DFS from each of 32 starting configs, track
entry constraints, look for cycles where b1 fires >= 3 times.
"""
from itertools import product as iproduct
import time

# All-binary 5-window
window_size = 5
all_configs = list(iproduct(range(2), repeat=window_size))
config_idx = {c: i for i, c in enumerate(all_configs)}
total = len(all_configs)  # 32

print(f"Window: 5 binary procs, {total} configs")
print("Searching for closed walks where middle proc (pos 2) fires >= 3 times...")
print("With entry conflict constraints and zero winding.")
print()

# Mover walk: nearest-neighbor on the 5-window.
# But it's an OPEN window — the mover can "leave" through the boundaries.
# When mover is at pos 0, it can go to pos -1 (= leave left).
# When mover is at pos 4, it can go to pos 5 (= leave right).
# While "outside", the mover can do anything — we model this as:
# the mover returns from the same or opposite boundary with arbitrary
# boundary state changes.

# Actually, let's model it more carefully.
# The 5 procs are indexed 0..4. The mover walk on the ring goes beyond
# this window. When the mover leaves (goes to position -1 or 5), we
# lose track. It can return from either side.

# For the entry conflict argument: we only track constraints at procs 0..4.
# When the mover is outside the window, no new constraints are added
# to window procs (they're all non-movers with contexts we can compute,
# but the mover is outside — window procs are non-movers at every
# external step).

# Hmm, this is getting complex. Let me simplify:
# Track only the 3 binary procs (positions 1,2,3 = p-1, p, p+1).
# Their contexts depend on positions 0,1,2,3,4.
# Boundary procs 0 and 4 change only when they fire.

# SIMPLEST MODEL: direct cycle search on ALL 5 binary procs
# as a ring of size 5 (we already did this and got length-4).
# For mixed: make positions 0 and 4 ternary.

# Let's try: 5-proc ring, procs 0,4 ternary (m=3), procs 1,2,3 binary.
# Total configs: 3 * 2 * 2 * 2 * 3 = 72.
# This is MUCH more tractable than the n=5 mixed ring we tried before,
# because we're only looking at the 5-window, not the full ring.

# Wait — but this IS a ring of size 5. The full ring search was slow
# because non-binary procs have multiple transition values. Let's see:
# 72 configs, up to ~20 steps, 5 movers per step, 2 values for ternary.
# Should be fast.

def search_ring(n, ms, target_proc, target_fc, max_path_len):
    total_configs_list = list(iproduct(*(range(m) for m in ms)))
    cidx = {c: i for i, c in enumerate(total_configs_list)}
    total_c = len(total_configs_list)

    def signed_step(a, b):
        d = (b - a) % n
        if d == 1: return 1
        elif d == n - 1: return -1
        return 0

    t0 = time.time()
    found = 0

    for start in range(total_c):
        stack = [(start, [start], [0]*n, 0, {}, [])]
        while stack:
            ci, path, fc, wind, cons, movs = stack.pop()
            if len(path) > max_path_len: continue
            c = total_configs_list[ci]
            for mover in range(n):
                L = c[(mover-1) % n]; S = c[mover]; R = c[(mover+1) % n]
                key = (mover, L, S, R)
                if key in cons and cons[key] == 'nonmover': continue
                valid = True
                new_cons = dict(cons)
                new_cons[key] = 'mover'
                for p in range(n):
                    if p == mover: continue
                    kp = (p, c[(p-1)%n], c[p], c[(p+1)%n])
                    if kp in new_cons and new_cons[kp] == 'mover':
                        valid = False; break
                    new_cons[kp] = 'nonmover'
                if not valid: continue

                possible_vals = [v for v in range(ms[mover]) if v != S]
                for new_val in possible_vals:
                    new_c = list(c)
                    new_c[mover] = new_val
                    new_ci = cidx[tuple(new_c)]
                    new_fc = list(fc); new_fc[mover] += 1
                    new_wind = wind
                    if movs: new_wind += signed_step(movs[-1], mover)
                    if new_ci == start and len(path) >= 3:
                        fw = new_wind + signed_step(mover, movs[0])
                        if fw == 0:
                            if new_fc[target_proc] >= target_fc:
                                found += 1
                                if found <= 5:
                                    print(f"  FOUND: len={len(path)}, fc={new_fc}, movers={movs+[mover]}")
                        continue
                    if new_ci in path: continue
                    stack.append((new_ci, path+[new_ci], new_fc, new_wind, new_cons, movs+[mover]))

    elapsed = time.time() - t0
    return found, elapsed

# Test 1: All binary ring of size 5 (sanity check)
print("=== Ring n=5, ms=[2,2,2,2,2], target: proc 2 fc>=3 ===")
f, t = search_ring(5, [2,2,2,2,2], 2, 3, 14)
print(f"Found: {f} in {t:.1f}s\n")

# Test 2: Mixed ring n=5, ms=[3,2,2,2,3]
print("=== Ring n=5, ms=[3,2,2,2,3], target: proc 2 fc>=3 ===")
f, t = search_ring(5, [3,2,2,2,3], 2, 3, 20)
print(f"Found: {f} in {t:.1f}s\n")

# Test 3: Mixed ring n=5, ms=[4,2,2,2,4]
print("=== Ring n=5, ms=[4,2,2,2,4], target: proc 2 fc>=3 ===")
f, t = search_ring(5, [4,2,2,2,4], 2, 3, 20)
print(f"Found: {f} in {t:.1f}s\n")

# Test 4: Mixed ring n=5, ms=[3,2,2,2,4]
print("=== Ring n=5, ms=[3,2,2,2,4], target: proc 2 fc>=3 ===")
f, t = search_ring(5, [3,2,2,2,4], 2, 3, 20)
print(f"Found: {f} in {t:.1f}s\n")

# Test 5: Larger boundaries ms=[6,2,2,2,6]
print("=== Ring n=5, ms=[6,2,2,2,6], target: proc 2 fc>=3 ===")
f, t = search_ring(5, [6,2,2,2,6], 2, 3, 20)
print(f"Found: {f} in {t:.1f}s\n")

# Test 6: What about non-middle binary? proc 1 fc>=3
print("=== Ring n=5, ms=[3,2,2,2,3], target: proc 1 fc>=3 ===")
f, t = search_ring(5, [3,2,2,2,3], 2, 3, 20)
print(f"Found: {f} in {t:.1f}s\n")

# Test 7: Large boundaries ms=[10,2,2,2,10]
print("=== Ring n=5, ms=[10,2,2,2,10], target: proc 2 fc>=3 ===")
f, t = search_ring(5, [10,2,2,2,10], 2, 3, 24)
print(f"Found: {f} in {t:.1f}s\n")
