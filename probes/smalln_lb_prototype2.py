"""Extended prototype: check forced kernel on survivors for ms=(2,2,2,2).

For cycles without TF entry conflict, check if the forced TF entries
create an inescapable bad cycle (nonempty forced kernel).
"""
from itertools import product as cartesian

n = 4
ms = [2, 2, 2, 2]
P = 16

all_cfgs = list(cartesian(*(range(m) for m in ms)))
all_cfgs_set = set(all_cfgs)

def neighbors(c):
    result = []
    for i in range(n):
        for v in range(ms[i]):
            if v != c[i]:
                c2 = list(c)
                c2[i] = v
                result.append((i, tuple(c2)))
    return result

def get_forced_entries(cycle, movers):
    """Get all TF entries forced by this cycle."""
    forced = {}  # (proc, L, S, R) -> value
    L = len(cycle)
    for k in range(L):
        c = cycle[k]
        m = movers[k]
        c_next = cycle[(k + 1) % L]
        # Mover
        key = (m, c[(m-1) % n], c[m], c[(m+1) % n])
        forced[key] = c_next[m]
        # Non-movers
        for j in range(n):
            if j == m:
                continue
            key_j = (j, c[(j-1) % n], c[j], c[(j+1) % n])
            forced[key_j] = c[j]
    return forced

def check_forced_kernel(cycle, movers):
    """Check if the forced TF entries create an inescapable bad cycle.

    Build the graph on bad configs using only forced TF entries.
    Do iterative sink removal. If anything remains, convergence fails
    for ANY TF completion.
    """
    forced = get_forced_entries(cycle, movers)
    good_set = set(cycle)
    bad_cfgs = [c for c in all_cfgs if c not in good_set]

    # For each bad config, find its possible successors using forced entries
    # A bad config c has some privileged procs. For each privileged proc p,
    # the successor is move(c, p). But we only know the move if f_p(L,S,R)
    # is in the forced entries.
    bad_set = set(bad_cfgs)
    changed = True
    rounds = 0

    while changed:
        changed = False
        to_remove = set()
        for c in bad_set:
            # For convergence failure, we need to show the adversary CAN keep
            # the system in bad configs forever. So we check: does every
            # successor of c (under forced entries) leave bad_set?
            # If ALL forced successors leave bad_set, c is a sink -> remove.
            #
            # But if some entries are NOT forced, the adversary might still
            # choose a bad successor via unforced entries. So we're conservative:
            # a config is a sink only if ALL possible moves (forced or not)
            # lead out of bad_set.
            #
            # For forced entries: we know the successor exactly.
            # For unforced entries: the successor could be anything, so
            # the adversary might stay in bad_set.
            #
            # Wait - for the CENTRAL daemon, the adversary picks ONE privileged
            # proc. We need: for EVERY daemon choice, the execution reaches good.
            # So convergence fails if there EXISTS a daemon strategy keeping
            # the system in bad configs.
            #
            # For forced kernel: we check using only forced entries.
            # A bad config c is "stuck" if there EXISTS a privileged proc p
            # such that the forced successor is also in bad_set.
            # (The adversary can choose that proc.)
            #
            # If we don't know which procs are privileged (depends on f),
            # we check: for each proc p and each context (L,S,R) at c,
            # is f_p(L,S,R) forced? If forced and ≠ S, then p is privileged.
            # If forced and = S, then p is not privileged.
            # If not forced, we don't know.

            # Let me simplify: check if c has any successor in bad_set
            # via forced privileged entries
            has_bad_succ = False
            all_succs_known_and_leave = True

            for p in range(n):
                L_val = c[(p-1) % n]
                S_val = c[p]
                R_val = c[(p+1) % n]
                key = (p, L_val, S_val, R_val)

                if key in forced:
                    new_val = forced[key]
                    if new_val != S_val:  # p is privileged
                        succ = list(c)
                        succ[p] = new_val
                        succ = tuple(succ)
                        if succ in bad_set:
                            has_bad_succ = True
                    # else: p is not privileged (forced to stay)
                else:
                    # Unknown: could be privileged or not
                    # Conservatively: can't remove this config
                    all_succs_known_and_leave = False

            if not has_bad_succ and all_succs_known_and_leave:
                to_remove.add(c)

        if to_remove:
            bad_set -= to_remove
            changed = True
            rounds += 1

    return len(bad_set), bad_set

def dfs_cycles():
    """Enumerate all candidate good cycles via DFS."""
    seen_cycles = set()  # canonical form to deduplicate
    survivors = []

    for start in all_cfgs:
        stack = [(start, [start], [], set([start]))]
        while stack:
            cur, path, movers_so_far, visited = stack.pop()
            for mover, nxt in neighbors(cur):
                if nxt == start and len(path) >= 4:
                    full_movers = movers_so_far + [mover]
                    if len(set(full_movers)) == n:
                        # Deduplicate: use canonical form (min rotation)
                        cycle_key = tuple(path)
                        rotations = [tuple(path[i:] + path[:i]) for i in range(len(path))]
                        canon = min(rotations)
                        if canon not in seen_cycles:
                            seen_cycles.add(canon)
                            # Check TF conflict
                            forced = get_forced_entries(path, full_movers)
                            has_conflict = False
                            # Re-check with sets
                            forced_check = {}
                            for k in range(len(path)):
                                c = path[k]
                                m = full_movers[k]
                                c_next = path[(k + 1) % len(path)]
                                key = (m, c[(m-1)%n], c[m], c[(m+1)%n])
                                if key in forced_check and forced_check[key] != c_next[m]:
                                    has_conflict = True
                                    break
                                forced_check[key] = c_next[m]
                                for j in range(n):
                                    if j == m:
                                        continue
                                    key_j = (j, c[(j-1)%n], c[j], c[(j+1)%n])
                                    if key_j in forced_check and forced_check[key_j] != c[j]:
                                        has_conflict = True
                                        break
                                    forced_check[key_j] = c[j]
                                if has_conflict:
                                    break

                            if not has_conflict:
                                survivors.append((list(path), full_movers))

                elif nxt not in visited and len(path) < P:
                    stack.append((nxt, path + [nxt], movers_so_far + [mover], visited | {nxt}))

    return survivors

print("Enumerating unique good cycles for ms=(2,2,2,2) n=4...")
survivors = dfs_cycles()
print(f"Unique cycles without TF conflict: {len(survivors)}")

print("\nChecking forced kernel for each survivor...")
all_blocked = True
for i, (cycle, movers) in enumerate(survivors):
    kernel_size, kernel = check_forced_kernel(cycle, movers)
    forced = get_forced_entries(cycle, movers)
    status = "BLOCKED (nonempty kernel)" if kernel_size > 0 else "SURVIVES"
    if kernel_size == 0:
        all_blocked = False
        # Check: are all entries forced? If not, we can't conclude
        total_entries = sum(ms[(p-1)%n] * ms[p] * ms[(p+1)%n] for p in range(n))
        print(f"  Cycle {i}: len={len(cycle)}, {status}, forced={len(forced)}/{total_entries} entries")
        print(f"    Cycle: {cycle}")
        print(f"    Movers: {movers}")
    else:
        print(f"  Cycle {i}: len={len(cycle)}, {status} (kernel={kernel_size})")

if all_blocked:
    print("\n=== ALL CYCLES BLOCKED ===")
    print("Every cycle without TF conflict has nonempty forced kernel.")
    print("Therefore no valid system exists for ms=(2,2,2,2).")
else:
    print("\n=== SOME CYCLES SURVIVE ===")
    print("Need additional analysis for surviving cycles.")

    # For survivors with unforced entries, try all completions
    print("\nTrying all TF completions for surviving cycles...")
    for i, (cycle, movers) in enumerate(survivors):
        kernel_size, _ = check_forced_kernel(cycle, movers)
        if kernel_size > 0:
            continue
        forced = get_forced_entries(cycle, movers)
        good_set = set(cycle)

        # Find unforced entries
        all_entries = []
        for p in range(n):
            for L in range(ms[(p-1)%n]):
                for S in range(ms[p]):
                    for R in range(ms[(p+1)%n]):
                        key = (p, L, S, R)
                        if key not in forced:
                            all_entries.append(key)

        print(f"\n  Cycle {i}: {len(all_entries)} unforced entries")
        if len(all_entries) > 20:
            print(f"    Too many unforced entries for brute force ({2**len(all_entries)} combos)")
            continue

        # Try all assignments of unforced entries
        found_valid = False
        for assignment in cartesian(*(range(ms[key[0]]) for key in all_entries)):
            full_tf = dict(forced)
            for j, key in enumerate(all_entries):
                full_tf[key] = assignment[j]

            # Build system and check validity
            bad_cfgs = [c for c in all_cfgs if c not in good_set]

            # Check: all good configs have exactly 1 privileged
            good_ok = True
            for c in cycle:
                priv_count = 0
                for p in range(n):
                    key = (p, c[(p-1)%n], c[p], c[(p+1)%n])
                    if full_tf[key] != c[p]:
                        priv_count += 1
                if priv_count != 1:
                    good_ok = False
                    break
            if not good_ok:
                continue

            # Check: all configs have at least 1 privileged (liveness)
            live_ok = True
            for c in all_cfgs:
                priv_count = 0
                for p in range(n):
                    key = (p, c[(p-1)%n], c[p], c[(p+1)%n])
                    if full_tf[key] != c[p]:
                        priv_count += 1
                if priv_count == 0:
                    live_ok = False
                    break
            if not live_ok:
                continue

            # Check convergence: iterative sink removal on bad configs
            bad_set = set(bad_cfgs)
            changed = True
            while changed:
                changed = False
                to_remove = set()
                for c in bad_set:
                    priv_procs = []
                    for p in range(n):
                        key = (p, c[(p-1)%n], c[p], c[(p+1)%n])
                        if full_tf[key] != c[p]:
                            priv_procs.append(p)
                    all_leave = True
                    for p in priv_procs:
                        succ = list(c)
                        succ[p] = full_tf[(p, c[(p-1)%n], c[p], c[(p+1)%n])]
                        if tuple(succ) in bad_set:
                            all_leave = False
                            break
                    if all_leave and priv_procs:
                        to_remove.add(c)
                if to_remove:
                    bad_set -= to_remove
                    changed = True

            if not bad_set:
                found_valid = True
                print(f"    FOUND VALID COMPLETION!")
                print(f"    Unforced assignment: {assignment}")
                break

        if found_valid:
            print(f"    ms=(2,2,2,2) HAS a valid system!")
        else:
            print(f"    All {2**len(all_entries)} completions checked, none valid")
