"""
Locality Bottleneck v4: Why does convergence fail for ms=(2,2,2,3,3)?

Focus on the STRUCTURAL obstacle: anti-sweep configs create
unavoidable bad cycles from determined entries.
"""

import sys
sys.path.insert(0, '.')
from itertools import product as iproduct
from collections import defaultdict

ms = [2, 2, 2, 3, 3]
n = 5

# The consistent cycle from v3
cycle = [
    (0,0,0,0,0), (1,0,0,0,0), (1,1,0,0,0), (1,1,1,0,0),
    (1,1,1,1,0), (1,1,1,1,1), (0,1,1,1,1), (0,0,1,1,1),
    (0,0,0,1,1), (0,0,0,0,1),
]
movers = [0, 1, 2, 3, 4, 0, 1, 2, 3, 4]
good_set = set(cycle)

# Build determined entries
determined = {}
for idx in range(len(cycle)):
    c = cycle[idx]
    mover = movers[idx]
    c_next = cycle[(idx+1) % len(cycle)]

    L = c[(mover-1) % n]
    S = c[mover]
    R = c[(mover+1) % n]
    S_new = c_next[mover]
    determined[(mover, L, S, R)] = S_new

    for i in range(n):
        if i != mover:
            Li = c[(i-1) % n]
            Si = c[i]
            Ri = c[(i+1) % n]
            determined[(i, Li, Si, Ri)] = Si

# ================================================================
# KEY ANALYSIS: Trace what happens at anti-sweep binary configs
# Binary states (0,1,0) and (1,0,1) are NOT on the good cycle.
# The determined entries FORCE certain privilege at these configs.
# ================================================================

print("="*70)
print("FORCED PRIVILEGE AT ANTI-SWEEP CONFIGS")
print("="*70)

all_configs = list(iproduct(*[range(m) for m in ms]))

# For each non-cycle config, check which processors have
# DETERMINED privilege status
for config in sorted(all_configs):
    if config in good_set:
        continue

    binary = config[:3]
    if binary not in [(0,1,0), (1,0,1)]:
        continue

    forced_priv = []
    forced_nopriv = []
    unknown = []

    for i in range(n):
        L = config[(i-1) % n]
        S = config[i]
        R = config[(i+1) % n]
        key = (i, L, S, R)
        if key in determined:
            if determined[key] != S:
                forced_priv.append(i)
            else:
                forced_nopriv.append(i)
        else:
            unknown.append(i)

    if forced_priv:
        print(f"  {config} bin={binary} NB=({config[3]},{config[4]}): "
              f"forced_priv={forced_priv} unknown={unknown}")

# ================================================================
# KEY QUESTION: Can the daemon create a bad cycle using ONLY
# configs where at least one processor has forced privilege?
# ================================================================

print("\n" + "="*70)
print("TRACING DAEMON-ADVERSARIAL PATHS FROM ANTI-SWEEP CONFIGS")
print("="*70)

# For each anti-sweep config with forced privilege, trace what
# happens if the daemon always picks the forced-privilege processor.
# Track if we return to an anti-sweep config (bad cycle).

def trace_forced_path(start, determined, max_steps=30):
    """Trace path where daemon picks forced-privileged processor."""
    path = [start]
    config = start

    for step in range(max_steps):
        if config in good_set:
            return path, "REACHED GOOD CYCLE"

        # Find forced-privileged processors
        forced = []
        for i in range(n):
            L = config[(i-1) % n]
            S = config[i]
            R = config[(i+1) % n]
            key = (i, L, S, R)
            if key in determined and determined[key] != S:
                forced.append((i, determined[key]))

        if not forced:
            return path, "NO FORCED PRIVILEGE (need free entries)"

        # Daemon picks first forced processor (adversarial choice)
        proc, new_val = forced[0]
        config = list(config)
        config[proc] = new_val
        config = tuple(config)

        if config in set(path):
            path.append(config)
            return path, "BAD CYCLE DETECTED"

        path.append(config)

    return path, "MAX STEPS"

# Test from all anti-sweep configs with NB states (0,0)
test_configs = [
    (0,1,0,0,0), (0,1,0,1,0), (0,1,0,0,1), (0,1,0,1,1),
    (1,0,1,0,0), (1,0,1,1,0), (1,0,1,0,1), (1,0,1,1,1),
]

for start in test_configs:
    path, result = trace_forced_path(start, determined)
    print(f"\n  Start: {start}")
    for i, c in enumerate(path):
        forced = []
        for proc in range(n):
            L = c[(proc-1) % n]
            S = c[proc]
            R = c[(proc+1) % n]
            key = (proc, L, S, R)
            if key in determined and determined[key] != S:
                forced.append(proc)
        marker = " ← CYCLE" if i > 0 and c == path[0] else ""
        marker = marker or (" ← GOOD" if c in good_set else "")
        print(f"    {i}: {c} forced_priv={forced}{marker}")
    print(f"    Result: {result}")

# ================================================================
# Now check: can free entries BREAK these bad cycles?
# For each bad cycle, identify configs where free entries could
# add/remove privilege to create an exit.
# ================================================================

print("\n" + "="*70)
print("CAN FREE ENTRIES BREAK BAD CYCLES?")
print("="*70)

# A bad cycle can be broken if at some config in the cycle:
# 1. A free entry makes a NEW processor privileged, whose move
#    leads outside the cycle, OR
# 2. A free entry removes a forced processor's privilege (impossible
#    since forced entries are determined)
#
# So: we need a free entry that creates additional privilege at
# a cycle config, AND the move from that privilege exits the cycle.

for start in [(0,1,0,0,0), (1,0,1,0,0)]:
    path, result = trace_forced_path(start, determined, max_steps=50)
    if result != "BAD CYCLE DETECTED":
        continue

    # Find the cycle portion
    cycle_start_idx = path.index(path[-1])
    bad_cycle = path[cycle_start_idx:-1]

    print(f"\n  Bad cycle from {start} (length {len(bad_cycle)}):")

    for c in bad_cycle:
        # Find processors with unknown privilege
        unknowns = []
        for i in range(n):
            L = c[(i-1) % n]
            S = c[i]
            R = c[(i+1) % n]
            key = (i, L, S, R)
            if key not in determined:
                unknowns.append(i)

        if unknowns:
            print(f"    {c}: unknown privilege for P{unknowns}")
            # For each unknown, check what happens if we make them privileged
            for proc in unknowns:
                L = c[(proc-1) % n]
                S = c[proc]
                R = c[(proc+1) % n]
                # Try each possible output
                for new_val in range(ms[proc]):
                    if new_val == S:
                        continue  # not privileged
                    new_config = list(c)
                    new_config[proc] = new_val
                    new_config = tuple(new_config)
                    on_cycle = new_config in good_set
                    in_bad = new_config in set(bad_cycle)
                    status = "GOOD CYCLE!" if on_cycle else ("in bad cycle" if in_bad else "other bad config")
                    print(f"      P{proc}→{new_val}: {new_config} [{status}]")

# ================================================================
# EXHAUSTIVE CHECK: For ms=(2,2,2,3,3), try ALL cycle structures
# that start with (0,0,0,0,0) and have the "sweep" pattern for
# binary processors, but allow different NB move orderings.
# ================================================================

print("\n" + "="*70)
print("CHECKING ALTERNATIVE CYCLE STRUCTURES")
print("="*70)

# Generate cycles by DFS. A cycle must:
# 1. Start at some config
# 2. Each step: exactly one processor changes state
# 3. All configs distinct (until return to start)
# 4. Each processor moves at least once
# 5. The transition entries are consistent

# For efficiency, only check cycles starting at (0,0,0,0,0)
# with length 10-14 (short cycles).

from itertools import combinations

def find_short_cycles(start, ms, max_length=14, max_found=100):
    """Find valid good cycles by DFS."""
    n = len(ms)
    found = []

    def dfs(path, movers_used):
        if len(found) >= max_found:
            return

        config = path[-1]

        # Try to close the cycle
        if len(path) >= 10 and len(movers_used) == n:
            # Check if we can return to start
            for proc in range(n):
                for new_val in range(ms[proc]):
                    if new_val == config[proc]:
                        continue
                    new_config = list(config)
                    new_config[proc] = new_val
                    new_config = tuple(new_config)
                    if new_config == start:
                        cycle = list(path)
                        cycle_movers = []
                        for i in range(len(cycle)):
                            c = cycle[i]
                            c_next = cycle[(i+1) % len(cycle)] if i < len(cycle)-1 else start
                            for j in range(n):
                                if c[j] != c_next[j]:
                                    cycle_movers.append(j)
                                    break
                        # Check consistency
                        req = {}
                        consistent = True
                        for i in range(len(cycle)):
                            c = cycle[i]
                            m = cycle_movers[i]
                            c_next = cycle[(i+1) % len(cycle)]

                            L = c[(m-1) % n]
                            S = c[m]
                            R = c[(m+1) % n]
                            S_new = c_next[m]

                            key = (m, L, S, R)
                            if key in req and req[key] != S_new:
                                consistent = False
                                break
                            req[key] = S_new

                            for j in range(n):
                                if j != m:
                                    Lj = c[(j-1) % n]
                                    Sj = c[j]
                                    Rj = c[(j+1) % n]
                                    key = (j, Lj, Sj, Rj)
                                    if key in req and req[key] != Sj:
                                        consistent = False
                                        break
                                    req[key] = Sj
                            if not consistent:
                                break

                        if consistent:
                            found.append((list(path), cycle_movers))

        if len(path) >= max_length:
            return

        # Extend path
        visited = set(path)
        for proc in range(n):
            for new_val in range(ms[proc]):
                if new_val == config[proc]:
                    continue
                new_config = list(config)
                new_config[proc] = new_val
                new_config = tuple(new_config)
                if new_config in visited:
                    continue
                new_movers = movers_used | {proc}
                dfs(path + [new_config], new_movers)

    dfs([start], set())
    return found

# This DFS is too slow for max_length=14. Let's limit to length 10.
print("Searching for consistent cycles of length 10...")
cycles_found = find_short_cycles((0,0,0,0,0), ms, max_length=10, max_found=50)
print(f"Found {len(cycles_found)} consistent cycles of length 10")

for i, (cyc, mvrs) in enumerate(cycles_found[:10]):
    nb_pairs = set()
    for c in cyc:
        nb_pairs.add((c[3], c[4]))
    mvr_counts = defaultdict(int)
    for m in mvrs:
        mvr_counts[m] += 1
    print(f"  Cycle {i}: movers={dict(sorted(mvr_counts.items()))}, "
          f"NB pairs={len(nb_pairs)}, pairs={sorted(nb_pairs)}")
