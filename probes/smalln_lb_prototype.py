"""Prototype: enumerate all possible good cycles for ms=(2,2,2,2) n=4.

For the Lean lower bound proof, we need to show that NO TransFn on this
RingSpec yields a valid system. Approach: enumerate all candidate good-cycle
shapes and show each has a TF entry conflict.

A "cycle shape" is a sequence of distinct configs where consecutive configs
differ at exactly one position (the mover). The TF entries implied by the
cycle must be self-consistent.
"""
from itertools import product as cartesian

n = 4
ms = [2, 2, 2, 2]
P = 16  # product

# All configs
all_cfgs = list(cartesian(*(range(m) for m in ms)))
assert len(all_cfgs) == P

def neighbors(c):
    """Configs reachable by changing exactly one position."""
    result = []
    for i in range(n):
        for v in range(ms[i]):
            if v != c[i]:
                c2 = list(c)
                c2[i] = v
                result.append((i, tuple(c2)))  # (mover, new_config)
    return result

def check_cycle(cycle, movers):
    """Check if a cycle with given movers has TF entry conflicts.

    Returns (has_conflict, conflict_details).

    TF entries forced by the cycle:
    - Mover at step k: f_{m_k}(L, S, R) = new_val  (privileged)
    - Non-mover j at step k: f_j(L, S, R) = S  (not privileged)
    """
    forced = {}  # (proc, L, S, R) -> set of forced values
    L = len(cycle)

    for k in range(L):
        c = cycle[k]
        m = movers[k]
        c_next = cycle[(k + 1) % L]

        # Mover entry: f_m(L, S, R) = c_next[m] (must differ from c[m])
        key = (m, c[(m-1) % n], c[m], c[(m+1) % n])
        val = c_next[m]
        if key not in forced:
            forced[key] = set()
        forced[key].add(val)

        # Non-mover entries: f_j(L, S, R) = c[j] (must equal c[j])
        for j in range(n):
            if j == m:
                continue
            key_j = (j, c[(j-1) % n], c[j], c[(j+1) % n])
            val_j = c[j]
            if key_j not in forced:
                forced[key_j] = set()
            forced[key_j].add(val_j)

    # Check for conflicts: any key forced to 2+ different values
    for key, vals in forced.items():
        if len(vals) > 1:
            return True, (key, vals)

    return False, None

def dfs_cycles():
    """Enumerate all candidate good cycles via DFS."""
    cycles_found = []
    conflicts = 0
    no_conflict = 0

    for start in all_cfgs:
        # DFS from start
        stack = [(start, [start], [], set([start]))]

        while stack:
            cur, path, movers_so_far, visited = stack.pop()

            for mover, nxt in neighbors(cur):
                if nxt == start and len(path) >= 4:
                    # Found a cycle! Check if each proc fires at least once (fairness)
                    full_movers = movers_so_far + [mover]
                    if len(set(full_movers)) == n:
                        has_conflict, details = check_cycle(path, full_movers)
                        if has_conflict:
                            conflicts += 1
                        else:
                            no_conflict += 1
                            cycles_found.append((list(path), full_movers, details))

                elif nxt not in visited and len(path) < P:
                    stack.append((nxt, path + [nxt], movers_so_far + [mover], visited | {nxt}))

    return cycles_found, conflicts, no_conflict

print("Enumerating all candidate good cycles for ms=(2,2,2,2) n=4...")
print("(This checks all cycle shapes with TF consistency)")
print()

survivors, conflicts, no_conflict = dfs_cycles()

# Divide by cycle length to account for rotational duplicates
# Actually, each cycle of length L is found L times (once per starting config in the cycle)
# and also from each starting config, so total = L * (number of occurrences of start in cycle)
# Since configs are distinct, each cycle is found exactly L times.

print(f"Cycles with TF conflict (raw count): {conflicts}")
print(f"Cycles without TF conflict (raw count): {no_conflict}")
print(f"Survivors: {len(survivors)}")

if survivors:
    print("\n=== SURVIVORS (no TF conflict) ===")
    for path, movers, details in survivors[:5]:
        print(f"  Cycle length {len(path)}: {path[:6]}...")
        print(f"  Movers: {movers[:6]}...")
else:
    print("\n=== ALL CYCLES BLOCKED by TF entry conflict ===")
    print("This confirms: no valid system exists for ms=(2,2,2,2)")
