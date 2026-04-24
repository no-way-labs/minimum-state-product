"""
Investigate WHY all 128 conflict-free 8-cycles on Q4 (all-binary n=4 ring)
have inescapable complements.

An 8-cycle on Q4: a directed cycle visiting exactly 8 of 16 configs, each step
flips exactly one bit (one proc fires). Fair: each proc fires exactly 2 times.
"""
from collections import Counter, defaultdict

N = 4
NCONFIGS = 16

def bit(c, j):
    return (c >> j) & 1

def flip(c, j):
    return c ^ (1 << j)

def context(c, j):
    """TF context for proc j at config c: (L, S, R) = (c[(j-1)%4], c[j], c[(j+1)%4])"""
    return (bit(c, (j-1)%N), bit(c, j), bit(c, (j+1)%N))

def partner(c, m):
    """Partner: flip the antipodal proc (m+2)%4"""
    return c ^ (1 << ((m+2) % N))

# Enumerate all fair 8-cycles on Q4
# Start from config 0, find all length-8 cycles that return to 0
# with each proc firing exactly 2 times

def find_all_8cycles():
    """Find all directed 8-cycles on Q4 where each proc fires exactly 2 times."""
    cycles = []

    def dfs(path, visited, movers, fire_count):
        if len(path) == 8:
            # Check return to start
            c = path[-1]
            for j in range(N):
                if flip(c, j) == path[0] and fire_count[j] + 1 == 2:
                    # This closing step makes proc j fire its 2nd time
                    # But wait, we need fire_count to be exactly 2 for all procs AFTER closing
                    new_fc = list(fire_count)
                    new_fc[j] += 1
                    if all(f == 2 for f in new_fc):
                        cycles.append((tuple(path), tuple(movers + [j])))
            return
        c = path[-1]
        for j in range(N):
            if fire_count[j] >= 2:
                continue  # Already fired 2 times
            nxt = flip(c, j)
            if nxt in visited:
                continue
            visited.add(nxt)
            path.append(nxt)
            movers.append(j)
            fire_count[j] += 1
            dfs(path, visited, movers, fire_count)
            fire_count[j] -= 1
            movers.pop()
            path.pop()
            visited.discard(nxt)

    # Start from 0
    visited = {0}
    dfs([0], visited, [], [0, 0, 0, 0])
    return cycles

print("Finding all fair 8-cycles on Q4 starting from 0...")
raw_cycles = find_all_8cycles()
print(f"Found {len(raw_cycles)} cycles starting from 0")

# Each 8-cycle has 8 rotations. Cycles starting from 0 give us one per rotation group
# that contains config 0. But some 8-cycles might not contain config 0.
# Let's find ALL 8-cycles by starting from each config.

all_cycles_set = set()
all_cycles_list = []

def canonical(path, movers):
    """Canonical form: smallest (config, mover) sequence over all rotations."""
    n = len(path)
    best = None
    for i in range(n):
        rot_path = path[i:] + path[:i]
        rot_movers = movers[i:] + movers[:i]
        candidate = (rot_path, rot_movers)
        if best is None or candidate < best:
            best = candidate
    return best

for start in range(NCONFIGS):
    def dfs2(path, visited, movers, fire_count, start_config):
        if len(path) == 8:
            c = path[-1]
            for j in range(N):
                if flip(c, j) == start_config and fire_count[j] + 1 == 2:
                    new_fc = list(fire_count)
                    new_fc[j] += 1
                    if all(f == 2 for f in new_fc):
                        cm = canonical(tuple(path), tuple(movers + [j]))
                        if cm not in all_cycles_set:
                            all_cycles_set.add(cm)
                            all_cycles_list.append((cm[0], cm[1]))
            return
        c = path[-1]
        for j in range(N):
            if fire_count[j] >= 2:
                continue
            nxt = flip(c, j)
            if nxt in visited:
                continue
            visited.add(nxt)
            path.append(nxt)
            movers.append(j)
            fire_count[j] += 1
            dfs2(path, visited, movers, fire_count, start_config)
            fire_count[j] -= 1
            movers.pop()
            path.pop()
            visited.discard(nxt)

    visited = {start}
    dfs2([start], visited, [], [0,0,0,0], start)

print(f"Total unique fair 8-cycles: {len(all_cycles_list)}")

# Check TF conflicts
def has_tf_conflict(path, movers):
    """Check if a cycle has TF entry conflict."""
    for j in range(N):
        ctx_as_mover = set()
        ctx_as_nonmover = set()
        for step in range(8):
            c = path[step]
            m = movers[step]
            ctx = context(c, j)
            if m == j:
                ctx_as_mover.add(ctx)
            else:
                ctx_as_nonmover.add(ctx)
        if ctx_as_mover & ctx_as_nonmover:
            return True
    return False

conflict_free = []
conflict_cycles = []
for path, movers in all_cycles_list:
    if has_tf_conflict(path, movers):
        conflict_cycles.append((path, movers))
    else:
        conflict_free.append((path, movers))

print(f"Conflict-free cycles: {len(conflict_free)}")
print(f"Cycles with TF conflict: {len(conflict_cycles)}")

if len(conflict_free) == 0:
    print("\nNo conflict-free cycles found! Let me check if the fairness constraint is correct...")
    # Maybe fairness doesn't require each proc to fire exactly 2 times?
    # Let's try: just 8-cycles (visiting 8 distinct configs) without the fairness constraint
    print("Trying without fairness constraint...")

    unfair_cycles = []
    def dfs3(path, visited, movers, start_config):
        if len(path) == 8:
            c = path[-1]
            for j in range(N):
                if flip(c, j) == start_config:
                    cm = canonical(tuple(path), tuple(movers + [j]))
                    key = cm
                    unfair_cycles.append((cm[0], cm[1]))
            return
        c = path[-1]
        for j in range(N):
            nxt = flip(c, j)
            if nxt in visited:
                continue
            visited.add(nxt)
            path.append(nxt)
            movers.append(j)
            dfs3(path, visited, movers, start_config)
            movers.pop()
            path.pop()
            visited.discard(nxt)

    unfair_set = set()
    for start in range(NCONFIGS):
        def dfs4(path, visited, movers, start_config):
            if len(path) == 8:
                c = path[-1]
                for j in range(N):
                    if flip(c, j) == start_config:
                        cm = canonical(tuple(path), tuple(movers + [j]))
                        if cm not in unfair_set:
                            unfair_set.add(cm)
                return
            c = path[-1]
            for j in range(N):
                nxt = flip(c, j)
                if nxt in visited:
                    continue
                visited.add(nxt)
                path.append(nxt)
                movers.append(j)
                dfs4(path, visited, movers, start_config)
                movers.pop()
                path.pop()
                visited.discard(nxt)

        visited = {start}
        dfs4([start], visited, [], start)

    print(f"Total unique 8-cycles (no fairness): {len(unfair_set)}")

    # Check fire counts
    fc_dist = Counter()
    for path, movers in list(unfair_set)[:100]:
        fc = Counter(movers)
        fc_key = tuple(sorted(fc.values()))
        fc_dist[fc_key] += 1
    print(f"Fire count distribution (sample): {dict(fc_dist)}")

    # Recheck conflicts on unfair cycles
    cf2 = 0
    cc2 = 0
    cf_list = []
    for path, movers in unfair_set:
        if has_tf_conflict(path, movers):
            cc2 += 1
        else:
            cf2 += 1
            cf_list.append((path, movers))
    print(f"Conflict-free (no fairness): {cf2}")
    print(f"With conflict (no fairness): {cc2}")

    if cf2 > 0:
        conflict_free = cf_list
        print(f"\nUsing {len(conflict_free)} conflict-free cycles for further analysis")
