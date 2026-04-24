"""
Shadow Trap Proof — Part 3: The actual theorem setting.
n>=9, ms with >=3 binary (non-consecutive), product < 4*3^(n-2),
sweep good cycle with isolated firings at some binary proc.

Key: "isolated firing" at binary proc q means q fires at some step k
where q is NOT the mover at step k-1 or k+1 (i.e., the mover jumps to q
from far away, then jumps away).

Let's work with a concrete case first:
n=9, ms=(2,3,2,3,2,3,3,3,3), product = 2^3 * 3^6 = 5832 < 4*3^7 = 8748
Binary at positions 0, 2, 4 (non-consecutive).
"""

import itertools
from collections import defaultdict

def build_general_sweep(n, ms, right_order=None, left_order=None):
    """Build a sweep good cycle with given mover orders.
    right_order: procs fired during rightward sweep
    left_order: procs fired during leftward sweep
    Each proc p fires exactly ms[p] times total.
    """
    if right_order is None:
        # Default: fire each proc ceil(ms[p]/2) times going right
        right_order = []
        left_order = []
        for p in range(n):
            right_count = (ms[p] + 1) // 2
            left_count = ms[p] - right_count
            right_order.extend([p] * right_count)
            left_order.extend([p] * left_count)
        # Sort right ascending, left descending for sweep pattern
        right_order.sort()
        left_order.sort(reverse=True)

    cfg = [0] * n
    configs = [tuple(cfg)]
    movers = []

    for p in right_order + left_order:
        movers.append(p)
        cfg = list(configs[-1])
        cfg[p] = (cfg[p] + 1) % ms[p]
        configs.append(tuple(cfg))

    if configs[-1] != configs[0]:
        return None, None
    configs = configs[:-1]
    return configs, movers

def extract_context_map(configs, movers, ms):
    n = len(ms)
    CL = len(configs)
    cmap = {}
    table = []
    for k in range(CL):
        p = movers[k]
        cfg = configs[k]
        L = cfg[(p-1) % n]
        S = cfg[p]
        R = cfg[(p+1) % n]
        Sp = configs[(k+1) % CL][p]
        key = (p, L, S, R)
        cmap[key] = (Sp, k)
        table.append((p, L, S, R, Sp))
    return cmap, table

def follow_deterministic_orbit(start, cmap, ms, good_set, max_steps=500):
    """Follow the unique forced transition. If multiple procs forced,
    we need a deterministic tie-breaking rule."""
    n = len(ms)
    orbit = [start]
    current = start
    for _ in range(max_steps):
        # Find all forced procs
        forced = []
        for p in range(n):
            L = current[(p-1) % n]
            S = current[p]
            R = current[(p+1) % n]
            key = (p, L, S, R)
            if key in cmap:
                Sp, step = cmap[key]
                forced.append((p, Sp, step))
        if not forced:
            return orbit, "stuck"

        # Pick the forced proc matching the next step in sequence
        # This mimics the "shadow cycle" construction: follow the
        # same mover ORDER as the good cycle
        p, Sp, step = forced[0]  # will refine this
        new_cfg = list(current)
        new_cfg[p] = Sp
        current = tuple(new_cfg)

        if current in good_set:
            return orbit + [current], "reached_good"
        if current == start:
            return orbit, "cycle"
        if current in set(orbit):
            idx = orbit.index(current)
            return orbit, f"cycle_at_{idx}"
        orbit.append(current)
    return orbit, "max_steps"


# ============================================================
# APPROACH: The shadow cycle construction
# ============================================================
#
# The known shadow cycle construction (from MEMORY) works for SWEEP cycles.
# Given good cycle g_0, g_1, ..., g_{CL-1} with movers m_0, ..., m_{CL-1}:
#
# Shadow cycle: s_0, s_1, ..., s_{CL-1} defined by
#   s_k = g_{σ(k)} modified at some positions
#
# The shadow permutation σ is known:
#   σ(0)=n-4, σ(1)=n-1, σ(2)=0, σ(k)=k-2 for 3≤k≤n-3, σ(n-2)=n-2, σ(n-1)=n-3
#
# But wait - this is for the specific sweep structure with 3 binary procs.
# Let me re-examine from scratch.
#
# ACTUAL KEY QUESTION: Given a sweep good cycle with "isolated firings"
# at a binary proc, why does a bad cycle (ShadowTrap) exist?

# Let me think about this differently.
#
# THEOREM SETUP:
# - Good cycle gc of length CL = sum(m_i)
# - gc is a sweep: total displacement ≥ 2n
# - At some binary proc q (m_q = 2), the firings are "isolated"
#   meaning the mover moves away from q between q's two firings
#
# The shadow cycle construction exploits the structure of the mover table.
#
# KEY IDEA: In a sweep, the mover table has a very specific structure:
# During the rightward sweep, movers go 0,1,2,...,n-1 (roughly)
# During the leftward sweep, movers go n-1,...,1,0 (roughly)
#
# Each proc p fires m_p times. For binary proc q: fires exactly twice.
# "Isolated" means: between q's two firings, other procs fire.
#
# THE CRITICAL OBSERVATION:
# When binary proc q fires at step k, its value flips: 0→1 or 1→0.
# At step k, q has context (L_k, S_k, R_k) and transitions to S'_k = 1-S_k.
#
# At q's second firing (step k'), it has context (L_{k'}, 1-S_k, R_{k'})
# and transitions back to S_k.
#
# Now: define s = g_k with q's value flipped: s[q] = 1-g_k[q], s[j] = g_k[j] for j≠q.
#
# At config s:
# - Proc q has context (L_k, 1-S_k, R_k). This might match step k'!
#   Because at step k', q has context (L_{k'}, 1-S_k, R_{k'}).
#   For this to match, we need L_k = L_{k'} and R_k = R_{k'}.
#
# - All procs j ≠ q with |j-q| > 1 see the same context as in g_k.
#   So the mover at step k (if it's not q or q's neighbor) is forced in s.
#
# THIS IS THE SEED OF THE SHADOW CYCLE.

# Let me verify this computationally.

print("=" * 60)
print("EXPLORING THE BINARY FLIP MECHANISM")
print("=" * 60)

# n=9, ms with binary at 0, 2, 4
n = 9
ms = [2, 3, 2, 3, 2, 3, 3, 3, 3]
CL = sum(ms)
print(f"n={n}, ms={ms}, CL={CL}, product={eval('*'.join(str(m) for m in ms))}")

# Build a sweep: right then left
# Right sweep: each proc fires ceil(m/2) times going right
# Left sweep: remaining firings going left
right_order = []
left_order = []
for p in range(n):
    right_count = (ms[p] + 1) // 2
    left_count = ms[p] - right_count
    right_order.extend([p] * right_count)
    left_order.extend([p] * left_count)

right_order.sort()
left_order.sort(reverse=True)

print(f"Right order ({len(right_order)}): {right_order}")
print(f"Left order ({len(left_order)}): {left_order}")

configs, movers = build_general_sweep(n, ms)
if configs is None:
    print("Sweep doesn't close!")
else:
    print(f"Sweep closes! CL={len(configs)}")
    cmap, table = extract_context_map(configs, movers, ms)
    good_set = set(configs)
    print(f"Distinct good configs: {len(good_set)}")

    # Find binary proc 0's firing steps
    for q in [0, 2, 4]:
        fire_steps = [k for k in range(CL) if movers[k] == q]
        print(f"\nBinary proc {q} fires at steps: {fire_steps}")
        for k in fire_steps:
            p, L, S, R, Sp = table[k]
            print(f"  Step {k}: ctx=({L},{S},{R}), {S}->{Sp}")

        # Check: does flipping q in g_{fire_steps[0]} create a forced config?
        k0, k1 = fire_steps[0], fire_steps[1]
        g0 = configs[k0]
        flipped = list(g0)
        flipped[q] = 1 - flipped[q]
        flipped = tuple(flipped)

        if flipped in good_set:
            print(f"  Flipped g_{k0} at proc {q}: {flipped} -> GOOD (skip)")
            continue

        # What's forced in the flipped config?
        forced = []
        for pp in range(n):
            L = flipped[(pp-1) % n]
            S = flipped[pp]
            R = flipped[(pp+1) % n]
            key = (pp, L, S, R)
            if key in cmap:
                Sp, step = cmap[key]
                forced.append((pp, Sp, step))

        print(f"  Flipped g_{k0} at proc {q}: {flipped}")
        print(f"  Forced procs: {[(pp, step) for pp, _, step in forced]}")

        # Check if q itself matches the OTHER firing step
        L_q = flipped[(q-1) % n]
        S_q = flipped[q]
        R_q = flipped[(q+1) % n]
        print(f"  Proc {q} context in flipped: ({L_q},{S_q},{R_q})")
        _, L1, S1, R1, _ = table[k1]
        print(f"  Proc {q} context at step {k1}: ({L1},{S1},{R1})")
        if (L_q, S_q, R_q) == (L1, S1, R1):
            print(f"  *** MATCH: flipped proc {q} matches step {k1}! ***")

    # Now: the KEY structural insight.
    # In a sweep, the mover at step k is at position roughly k (for right sweep)
    # and roughly CL-k (for left sweep).
    # If binary proc q fires at step k0 (right sweep) and k1 (left sweep),
    # then between k0 and k1, the mover has moved away from q.
    #
    # When we flip q in g_{k0}:
    # - Procs far from q see the same context as in g_{k0}
    # - The mover at step k0 is q itself. After flip, q has the "wrong" value.
    # - But procs far from q that are forced in g_{k0} are still forced.

    # Let me check: at g_{k0}, which procs besides the mover are forced?
    print("\n\n=== Context propagation in sweep ===")
    for k in range(min(CL, 20)):
        p = movers[k]
        g = configs[k]
        forced = []
        for pp in range(n):
            L = g[(pp-1) % n]
            S = g[pp]
            R = g[(pp+1) % n]
            key = (pp, L, S, R)
            if key in cmap:
                Sp, step = cmap[key]
                forced.append((pp, step))
        print(f"Step {k}: mover={p}, forced={forced}")
