"""Count ALL simple directed cycles on Q4 (4-cube graph).

GoodCycle doesn't require fairness (all procs firing), so we need
to check ALL cycles, not just those with all positions changing.
"""
from collections import defaultdict

n = 4
N = 1 << n  # 16 vertices

def cube_neighbors(v):
    """Neighbors of vertex v in Q4 (flip each bit)."""
    return [(v ^ (1 << b), b) for b in range(n)]

# Enumerate all simple directed cycles via DFS
# A directed cycle: v_0 -> v_1 -> ... -> v_{L-1} -> v_0
# Canonical: start at minimum vertex, next vertex < last vertex (to pick direction)

cycle_counts = defaultdict(int)  # length -> count of unique directed cycles
total_unique = 0

for start in range(N):
    # DFS from start, looking for paths that return to start
    # Only consider start as the minimum vertex in the cycle
    stack = [(start, [start], 1 << start)]  # (current, path, visited_bitmask)

    while stack:
        cur, path, visited = stack.pop()

        for nbr, bit in cube_neighbors(cur):
            if nbr == start and len(path) >= 3:
                # Found a cycle! Only count if start is minimum
                if start == min(path):
                    # Canonical direction: path[1] < path[-1]
                    if path[1] < path[-1]:
                        cycle_counts[len(path)] += 1
                        total_unique += 1
            elif nbr > start and not (visited & (1 << nbr)):
                # Only visit vertices > start (ensures start is min)
                stack.append((nbr, path + [nbr], visited | (1 << nbr)))

print("Simple directed cycles on Q4 (up to rotation, canonical direction):")
for length in sorted(cycle_counts):
    print(f"  Length {length:2d}: {cycle_counts[length]:6d}")
print(f"  Total:     {total_unique:6d}")

# Now check ALL of these for blocking
print("\n--- Checking all cycles for TF conflict + forced kernel ---")

ms = [2] * n
all_cfgs = [tuple((v >> b) & 1 for b in range(n)) for v in range(N)]

def code_to_cfg(v):
    return tuple((v >> b) & 1 for b in range(n))

def check_blocked(path_codes):
    """Check if a cycle (given as vertex codes) is blocked."""
    L = len(path_codes)
    path = [code_to_cfg(v) for v in path_codes]

    # Determine movers: consecutive configs differ at exactly one bit
    movers = []
    for k in range(L):
        c = path_codes[k]
        c_next = path_codes[(k + 1) % L]
        diff = c ^ c_next
        assert diff != 0 and (diff & (diff - 1)) == 0, f"Not cube-adjacent: {c} {c_next}"
        bit = diff.bit_length() - 1
        movers.append(bit)

    # Collect forced TF entries
    forced = {}
    for k in range(L):
        c = path[k]
        m = movers[k]
        c_next = path[(k + 1) % L]

        # Mover entry
        key = (m, c[(m-1) % n], c[m], c[(m+1) % n])
        val = c_next[m]
        if key in forced and forced[key] != val:
            return True, "TF_CONFLICT"
        forced[key] = val

        # Non-mover entries
        for j in range(n):
            if j == m:
                continue
            key_j = (j, c[(j-1) % n], c[j], c[(j+1) % n])
            val_j = c[j]
            if key_j in forced and forced[key_j] != val_j:
                return True, "TF_CONFLICT"
            forced[key_j] = val_j

    # No TF conflict. Check forced kernel.
    good_set = set(path)
    bad_cfgs = [c for c in all_cfgs if c not in good_set]
    bad_set = set(bad_cfgs)

    changed = True
    while changed:
        changed = False
        to_remove = set()
        for c in bad_set:
            has_forced_bad_succ = False
            has_unknown = False

            for p in range(n):
                key = (p, c[(p-1) % n], c[p], c[(p+1) % n])
                if key in forced:
                    new_val = forced[key]
                    if new_val != c[p]:  # privileged
                        succ = list(c)
                        succ[p] = new_val
                        succ = tuple(succ)
                        if succ in bad_set:
                            has_forced_bad_succ = True
                else:
                    has_unknown = True

            if not has_forced_bad_succ and not has_unknown:
                to_remove.add(c)

        if to_remove:
            bad_set -= to_remove
            changed = True

    if bad_set:
        return True, f"FORCED_KERNEL({len(bad_set)})"
    else:
        return False, "SURVIVES"

blocked_tf = 0
blocked_kernel = 0
survives = 0

for start in range(N):
    stack = [(start, [start], 1 << start)]
    while stack:
        cur, path, visited = stack.pop()
        for nbr, bit in cube_neighbors(cur):
            if nbr == start and len(path) >= 3:
                if start == min(path) and path[1] < path[-1]:
                    is_blocked, reason = check_blocked(path)
                    if "TF_CONFLICT" in reason:
                        blocked_tf += 1
                    elif "FORCED_KERNEL" in reason:
                        blocked_kernel += 1
                    else:
                        survives += 1
                        print(f"  SURVIVOR: {path}")
            elif nbr > start and not (visited & (1 << nbr)):
                stack.append((nbr, path + [nbr], visited | (1 << nbr)))

print(f"\nBlocked by TF conflict:  {blocked_tf}")
print(f"Blocked by forced kernel: {blocked_kernel}")
print(f"Survives:                 {survives}")
print(f"Total:                    {blocked_tf + blocked_kernel + survives}")

if survives == 0:
    print("\n=== ALL CYCLES BLOCKED — ms=(2,2,2,2) admits no valid system ===")
