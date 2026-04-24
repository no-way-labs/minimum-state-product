"""
ra5_debug.py — Investigate the "no EC" cases.
Are they real counterexamples or bugs in the cycle generator?
"""

import random
from collections import defaultdict


def ring_dist(a, b, n):
    d = abs(a - b)
    return min(d, n - d)


def verify_cycle_properties(path, movers, n):
    """Verify that the cycle is valid: ring-adjacent, all configs distinct, returns to start."""
    CL = len(movers)
    if CL != len(path) - 1 and CL != len(path):
        # path might have CL+1 entries (last = first) or CL entries
        pass

    errors = []

    # Check ring-adjacency
    for i in range(len(movers) - 1):
        if ring_dist(movers[i], movers[i+1], n) > 1:
            errors.append(f"Non-adjacent movers at steps {i},{i+1}: {movers[i]},{movers[i+1]}")

    # Check wraparound adjacency
    if len(movers) >= 2:
        if ring_dist(movers[-1], movers[0], n) > 1:
            errors.append(f"Non-adjacent wraparound: {movers[-1]},{movers[0]}")

    # Check all configs distinct
    configs = [tuple(c) for c in path[:CL]]
    if len(set(configs)) != CL:
        errors.append(f"Duplicate configs: {CL} steps but {len(set(configs))} distinct")

    # Check each step changes exactly one processor
    for i in range(CL):
        next_idx = (i + 1) % CL
        if next_idx >= len(path):
            continue
        diff = sum(1 for j in range(n) if path[i][j] != path[next_idx][j])
        if diff != 1:
            errors.append(f"Step {i}: {diff} processors changed (expected 1)")
        elif diff == 1:
            changed = [j for j in range(n) if path[i][j] != path[next_idx][j]]
            if changed[0] != movers[i]:
                errors.append(f"Step {i}: mover={movers[i]} but proc {changed[0]} changed")

    return errors


def find_good_cycles_ra(n, ms, max_attempts=5000, max_depth=None):
    """Generate good cycles with ring-adjacent movers."""
    if max_depth is None:
        total = 1
        for m in ms:
            total *= m
        max_depth = total + 10

    cycles = []

    for attempt in range(max_attempts):
        config = tuple(random.randint(0, ms[i]-1) for i in range(n))
        path = [config]
        movers = []
        visited = {config}

        for step in range(max_depth):
            candidates = []
            for i in range(n):
                if movers and ring_dist(movers[-1], i, n) > 1:
                    continue
                for v in range(ms[i]):
                    if v == config[i]:
                        continue
                    new_config = list(config)
                    new_config[i] = v
                    new_config = tuple(new_config)
                    if new_config == path[0] and len(path) >= 3:
                        # Check wraparound ring-adjacency too
                        if ring_dist(i, movers[0], n) <= 1:
                            candidates.append((i, v, new_config, True))
                    elif new_config not in visited:
                        candidates.append((i, v, new_config, False))

            if not candidates:
                break

            closing = [c for c in candidates if c[3]]
            if closing and len(path) >= n:
                i, v, new_config, _ = random.choice(closing)
                movers.append(i)
                cycles.append((list(path), list(movers)))
                break
            else:
                non_closing = [c for c in candidates if not c[3]]
                if not non_closing:
                    # Try closing even if short
                    if closing:
                        i, v, new_config, _ = random.choice(closing)
                        movers.append(i)
                        cycles.append((list(path), list(movers)))
                        break
                    break
                i, v, new_config, _ = random.choice(non_closing)
                movers.append(i)
                config = new_config
                path.append(config)
                visited.add(config)

    return cycles


def check_ec_all_procs(path, movers, arc, n):
    """Check EC at all 3 arc processors. Return details."""
    CL = len(movers)
    for q in arc:
        left = (q - 1) % n
        right = (q + 1) % n

        mt = {}
        nmt = {}
        for k in range(CL):
            triple = (path[k][left], path[k][q], path[k][right])
            if movers[k] == q:
                if triple not in mt:
                    mt[triple] = k
            else:
                if triple not in nmt:
                    nmt[triple] = k

        for t in mt:
            if t in nmt:
                return True, q, mt[t], nmt[t], t

    return False, None, None, None, None


def investigate_failures():
    """Find and investigate cycles where EC check fails."""
    print("=== Investigating EC Failures ===")
    print()

    random.seed(42)
    n = 7
    failures = []

    for ms in [[2]*7, [3]*7, [2,2,2,3,3,3,3]]:
        cycles = find_good_cycles_ra(n, ms, max_attempts=10000, max_depth=80)
        print(f"ms={ms}: {len(cycles)} cycles")

        for path, movers in cycles:
            CL = len(movers)

            # Verify cycle
            errors = verify_cycle_properties(path, movers, n)
            if errors:
                continue  # Skip invalid cycles

            fire_set = set(movers)
            for p in range(n):
                arc = [p, (p+1)%n, (p+2)%n]
                if not all(q in fire_set for q in arc):
                    continue

                found, q, k_m, k_nm, t = check_ec_all_procs(path, movers, arc, n)
                if not found:
                    failures.append((ms, path, movers, arc))

    print(f"\nTotal failures: {len(failures)}")

    for i, (ms, path, movers, arc) in enumerate(failures[:5]):
        CL = len(movers)
        print(f"\n--- Failure {i+1} ---")
        print(f"ms={ms}, arc={arc}, CL={CL}")
        print(f"Movers: {movers}")

        # Verify ring-adjacency including wraparound
        ra_ok = True
        for j in range(CL):
            nxt = (j + 1) % CL
            if ring_dist(movers[j], movers[nxt], n) > 1:
                print(f"  RING-ADJACENCY VIOLATION at step {j}: "
                      f"mover {movers[j]} → {movers[nxt]}, dist={ring_dist(movers[j], movers[nxt], n)}")
                ra_ok = False

        if not ra_ok:
            print("  This is a bug in the cycle generator (non-adjacent movers)")
            continue

        # Show triples at each arc processor
        for q in arc:
            left = (q - 1) % n
            right = (q + 1) % n
            print(f"\n  Proc {q} (left={left}, right={right}):")
            mt_set = set()
            nmt_set = set()
            for k in range(CL):
                triple = (path[k][left], path[k][q], path[k][right])
                if movers[k] == q:
                    mt_set.add(triple)
                    print(f"    Step {k}: MOVER triple={triple}")
                # Show nearby non-mover steps
            for k in range(CL):
                triple = (path[k][left], path[k][q], path[k][right])
                if movers[k] != q:
                    nmt_set.add(triple)

            overlap = mt_set & nmt_set
            print(f"    Mover triples: {len(mt_set)}, Non-mover triples: {len(nmt_set)}")
            print(f"    Overlap: {len(overlap)}")
            if overlap:
                print(f"    WAIT — overlap exists! Bug in check_ec_all_procs!")

        # Double check with exhaustive comparison
        print(f"\n  Exhaustive check:")
        for q in arc:
            left = (q - 1) % n
            right = (q + 1) % n
            for k1 in range(CL):
                if movers[k1] != q:
                    continue
                t1 = (path[k1][left], path[k1][q], path[k1][right])
                for k2 in range(CL):
                    if movers[k2] == q:
                        continue
                    t2 = (path[k2][left], path[k2][q], path[k2][right])
                    if t1 == t2:
                        print(f"    EC at proc {q}: mover step {k1} = non-mover step {k2}, triple={t1}")
                        break


if __name__ == "__main__":
    investigate_failures()
