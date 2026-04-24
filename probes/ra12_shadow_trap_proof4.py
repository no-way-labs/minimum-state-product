"""
Shadow Trap Proof — Part 4: The correct construction.

The shadow cycle is NOT about flipping at the mover's step.
It's about: the forced graph on non-good configs has a cycle.

From MEMORY: "Following forced transitions from a shifted good config
creates a cycle of length CL among non-good configs. Verified 512/512 at n=9."

So the claim is: shift a good config, follow forced transitions, get a cycle.

Let me understand WHICH shift and WHICH good config.

The key construction from the existing proofs:
- Good cycle g_0,...,g_{CL-1} with movers m_0,...,m_{CL-1}
- Shadow cycle s_0,...,s_{CL-1} where s_k[j] = g_{σ(k)}[j] for most j,
  but modified at certain positions.

But actually the simplest approach:
For a sweep, consider the "phase-shifted" construction.
At each step k, mover m_k fires. The mover context (L,S,R) at step k
determines the transition. If we construct a non-good config that
agrees with g_k on proc m_k's neighborhood, then m_k fires the same way.

The shadow cycle is: run the same sequence of movers m_0,...,m_{CL-1}
but starting from a different initial config. The resulting configs are
non-good, but each step is forced because the mover's context matches.

Wait - that's the KEY insight. Let me verify:

If s_0 is a non-good config such that proc m_0 has the same context
(L,S,R) as in g_0, then firing m_0 produces s_1. If s_1 is non-good
and proc m_1 has the same context as in g_1, then m_1 fires...

The question is: does this chain hold for ALL CL steps?
"""

import itertools
from collections import defaultdict

def build_sweep(n, ms):
    """Standard right-left sweep."""
    right_order = []
    left_order = []
    for p in range(n):
        rc = (ms[p] + 1) // 2
        lc = ms[p] - rc
        right_order.extend([p] * rc)
        left_order.extend([p] * lc)
    right_order.sort()
    left_order.sort(reverse=True)

    cfg = [0] * n
    configs = [tuple(cfg)]
    movers = right_order + left_order

    for p in movers:
        cfg = list(configs[-1])
        cfg[p] = (cfg[p] + 1) % ms[p]
        configs.append(tuple(cfg))

    if configs[-1] != configs[0]:
        return None, None
    configs = configs[:-1]
    return configs, movers

def get_context(cfg, p, n):
    return (cfg[(p-1) % n], cfg[p], cfg[(p+1) % n])

# ============================================================
# THE CORE CONSTRUCTION
# ============================================================
# Hypothesis: Given a sweep good cycle and a "perturbation" Δ
# (change one proc's value), the forced orbit is a cycle of length CL
# if and only if Δ propagates correctly.
#
# More precisely: define s_0 = g_0 + Δ (modify one position).
# Apply the same mover sequence. At step k, if the mover m_k sees
# the same context in s_k as in g_k, then the same transition applies.
#
# When does the mover's context change? Only when the perturbation
# is at m_k or one of its neighbors.
#
# In a sweep, the mover moves monotonically (right then left).
# A perturbation at position q affects movers at {q-1, q, q+1}.
# These movers fire during a LOCAL window of the sweep.
#
# Outside that window: the mover is far from q, so it sees the same
# context. The perturbation propagates transparently.
#
# Inside the window: the mover is near q. The context differs.
# The forced transition may or may not match a different table entry.

# Let me trace this precisely.

n = 9
ms = [2, 3, 2, 3, 2, 3, 3, 3, 3]
configs, movers = build_sweep(n, ms)
CL = len(configs)
good_set = set(configs)

print(f"n={n}, ms={ms}, CL={CL}")
print(f"Movers: {movers}")

# Build the mover context table
table = []  # (proc, L, S, R, S')
for k in range(CL):
    p = movers[k]
    g = configs[k]
    L, S, R = get_context(g, p, n)
    Sp = configs[(k+1) % CL][p]
    table.append((p, L, S, R, Sp))

# Build context map: (proc, L, S, R) -> (S', step)
cmap = {}
for k, (p, L, S, R, Sp) in enumerate(table):
    cmap[(p, L, S, R)] = (Sp, k)

# THE EXPERIMENT: For each good config g_k and each position q and value v:
# Define s_0 = g_k with s_0[q] = v (where v ≠ g_k[q]).
# Apply the SAME mover sequence m_k, m_{k+1}, ..., m_{k-1}.
# At each step, check if the mover's context matches any table entry.
# If yes, apply the forced transition. If no, the chain breaks.

print("\n=== Shadow orbit construction ===")

def try_shadow_orbit(k_start, q, v, configs, movers, ms, table, cmap, good_set):
    """Try to construct a shadow orbit starting from g_{k_start} with proc q changed to v."""
    n = len(ms)
    CL = len(configs)

    g = configs[k_start]
    s = list(g)
    s[q] = v
    s = tuple(s)

    if s in good_set:
        return None, "is_good"

    orbit = [s]
    current = s

    for step in range(CL):
        k = (k_start + step) % CL
        p = movers[k]
        ctx = get_context(current, p, n)

        # Check if this context matches the table entry at step k
        expected_ctx = (table[k][1], table[k][2], table[k][3])

        if ctx == expected_ctx:
            # Same context as good cycle! Fire the same way.
            Sp = table[k][4]
            new = list(current)
            new[p] = Sp
            current = tuple(new)
        else:
            # Different context. Check if it matches ANY table entry for this proc.
            key = (p,) + ctx
            if key in cmap:
                Sp, matched_step = cmap[key]
                new = list(current)
                new[p] = Sp
                current = tuple(new)
            else:
                return orbit, f"stuck_at_step_{step}_mover_{p}_ctx_{ctx}"

        if step < CL - 1:
            orbit.append(current)

    # Check: does it return to start?
    if current == s:
        return orbit, "cycle"
    else:
        return orbit, f"no_close_gap={sum(1 for a,b in zip(current,s) if a!=b)}"

# Test: try all shifts from g_0
results = defaultdict(int)
for k_start in range(CL):
    for q in range(n):
        for v in range(ms[q]):
            g = configs[k_start]
            if v == g[q]:
                continue
            orbit, status = try_shadow_orbit(k_start, q, v, configs, movers, ms, table, cmap, good_set)
            results[status] += 1

print("Results of shadow orbit attempts (all k_start, all q, all v):")
for status, count in sorted(results.items()):
    print(f"  {status}: {count}")

# Now focus on successful cycles and understand them
print("\n=== Analyzing successful shadow cycles ===")
cycle_orbits = []
for k_start in range(CL):
    for q in range(n):
        for v in range(ms[q]):
            g = configs[k_start]
            if v == g[q]:
                continue
            orbit, status = try_shadow_orbit(k_start, q, v, configs, movers, ms, table, cmap, good_set)
            if status == "cycle":
                cycle_orbits.append((k_start, q, v, orbit))

print(f"Total successful shadow cycles: {len(cycle_orbits)}")

# Group by the set of configs in the orbit
orbit_sets = defaultdict(list)
for k_start, q, v, orbit in cycle_orbits:
    orbit_sets[frozenset(orbit)].append((k_start, q, v))

print(f"Distinct shadow cycle config sets: {len(orbit_sets)}")
for orbit_set, params in orbit_sets.items():
    print(f"  Size {len(orbit_set)}: from {len(params)} different (k_start, q, v) combos")
    # Show one example
    ks, q, v = params[0]
    print(f"    Example: k_start={ks}, q={q}, v={v}")

# KEY: For each shadow cycle, check the Hamming distance to nearest good config
print("\n=== Hamming distance analysis ===")
for orbit_set, params in list(orbit_sets.items())[:3]:
    orbit_list = list(orbit_set)
    print(f"Shadow cycle of size {len(orbit_list)}:")
    for s in sorted(orbit_list)[:5]:
        min_dist = min(sum(1 for a,b in zip(s,g) if a != b) for g in configs)
        print(f"  {s} -> min Hamming dist to good: {min_dist}")
