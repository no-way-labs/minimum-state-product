"""
ra5_deep_debug.py — Analyze failures to find the TRUE lemma.

The lemma as stated fails even with high fire counts.
Key question: what additional property distinguishes success from failure?

Hypothesis 1: The failures involve arcs where the walk is "concentrated" —
the walk stays mostly in the 3-arc without leaving.

Hypothesis 2: The failures involve cycles that aren't "good cycles" in the
Dijkstra sense (not visiting all good configs of a system).

Hypothesis 3: Need a different formulation — maybe all n procs must fire,
not just 3 adjacent ones.
"""

import random
from collections import defaultdict


def ring_dist(a, b, n):
    d = abs(a - b)
    return min(d, n - d)


def find_and_analyze_failures():
    """Find failures and analyze their structure."""
    print("=== Analyzing Failures ===")

    random.seed(42)
    failures = []

    for n in [7, 8]:
        for ms_type in ['ternary', 'mixed']:
            if ms_type == 'ternary':
                ms = [3]*n
            else:
                ms = [2,2,2] + [3]*(n-3)

            for trial in range(30000):
                config = tuple(random.randint(0, ms[i]-1) for i in range(n))
                path = [config]
                movers = []
                visited = {config}

                for step in range(200):
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
                        break
                    else:
                        non_closing = [c for c in candidates if not c[3]]
                        if not non_closing:
                            if closing:
                                i, v, new_config, _ = random.choice(closing)
                                movers.append(i)
                                break
                            break
                        i, v, new_config, _ = random.choice(non_closing)
                        movers.append(i)
                        config = new_config
                        path.append(config)
                        visited.add(config)
                else:
                    continue

                CL = len(movers)
                if CL < 3:
                    continue

                fire_counts = defaultdict(int)
                for m in movers:
                    fire_counts[m] += 1

                fire_set = set(movers)

                for p in range(n):
                    arc = [p, (p+1)%n, (p+2)%n]
                    if not all(q in fire_set for q in arc):
                        continue

                    total_fc = sum(fire_counts[q] for q in arc)

                    # Check EC at all 3 arc procs
                    found = False
                    for q in arc:
                        left = (q - 1) % n
                        right = (q + 1) % n
                        mt = set()
                        nmt = set()
                        for k in range(CL):
                            triple = (path[k][left], path[k][q], path[k][right])
                            if movers[k] == q:
                                mt.add(triple)
                            else:
                                nmt.add(triple)
                        if mt & nmt:
                            found = True
                            break

                    if not found:
                        # How many of the n procs fire?
                        n_firing = len(fire_set)
                        # How many procs are involved in the walk?
                        # Is the walk concentrated in the arc?
                        arc_steps = sum(1 for m in movers if m in arc)
                        arc_frac = arc_steps / CL
                        # Distance from arc to farthest mover
                        max_dist = max(min(ring_dist(m, q, n) for q in arc) for m in fire_set)

                        failures.append({
                            'n': n, 'ms': ms, 'CL': CL,
                            'arc': arc, 'total_fc': total_fc,
                            'fire_counts': dict(fire_counts),
                            'n_firing': n_firing,
                            'arc_frac': arc_frac,
                            'max_dist': max_dist,
                            'movers': movers[:],
                            'path': [p[:] for p in path[:CL]],
                        })

    print(f"Total failures: {len(failures)}")

    if not failures:
        print("No failures found!")
        return

    # Analyze failure properties
    print("\nKey properties of failures:")
    print(f"  n_firing distribution:")
    nf_dist = defaultdict(int)
    for f in failures:
        nf_dist[f['n_firing']] += 1
    for k in sorted(nf_dist):
        print(f"    {k} procs fire: {nf_dist[k]}")

    print(f"\n  arc_frac distribution:")
    af_buckets = defaultdict(int)
    for f in failures:
        bucket = round(f['arc_frac'], 1)
        af_buckets[bucket] += 1
    for k in sorted(af_buckets):
        print(f"    arc_frac ~ {k:.1f}: {af_buckets[k]}")

    print(f"\n  All n procs fire?")
    all_fire = sum(1 for f in failures if f['n_firing'] == f['n'])
    print(f"    Yes: {all_fire}, No: {len(failures) - all_fire}")

    # Focus on failures where ALL n procs fire
    all_fire_failures = [f for f in failures if f['n_firing'] == f['n']]
    print(f"\n  Failures with ALL procs firing: {len(all_fire_failures)}")

    if all_fire_failures:
        print("  Detailed look at first 5:")
        for f in all_fire_failures[:5]:
            print(f"    n={f['n']}, CL={f['CL']}, arc={f['arc']}, "
                  f"total_fc={f['total_fc']}, arc_frac={f['arc_frac']:.2f}")
            print(f"    fire_counts={f['fire_counts']}")
            print(f"    movers={f['movers']}")

    # Check: do failures always have the arc as a "concentrated" region?
    print(f"\n  arc_frac for ALL-procs-fire failures:")
    for f in all_fire_failures:
        print(f"    n={f['n']}, CL={f['CL']}, arc_frac={f['arc_frac']:.2f}, total_fc={f['total_fc']}")


def check_all_procs_fire_hypothesis():
    """
    Test: if ALL n processors fire at least once, does the 3-arc obstruction hold?
    """
    print("\n=== Testing ALL-Procs-Fire Hypothesis ===")

    random.seed(42)
    total_tested = 0
    failures = 0

    for n in [7, 8, 9]:
        for ms_type in ['binary', 'ternary', 'mixed']:
            if ms_type == 'binary':
                ms = [2]*n
            elif ms_type == 'ternary':
                ms = [3]*n
            else:
                ms = [2,2,2] + [3]*(n-3)

            for trial in range(20000):
                config = tuple(random.randint(0, ms[i]-1) for i in range(n))
                path = [config]
                movers = []
                visited = {config}

                for step in range(200):
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
                        break
                    else:
                        non_closing = [c for c in candidates if not c[3]]
                        if not non_closing:
                            if closing:
                                i, v, new_config, _ = random.choice(closing)
                                movers.append(i)
                                break
                            break
                        i, v, new_config, _ = random.choice(non_closing)
                        movers.append(i)
                        config = new_config
                        path.append(config)
                        visited.add(config)
                else:
                    continue

                CL = len(movers)
                if CL < 3:
                    continue

                fire_set = set(movers)
                if len(fire_set) != n:
                    continue  # Skip if not all procs fire

                fire_counts = defaultdict(int)
                for m in movers:
                    fire_counts[m] += 1

                for p in range(n):
                    arc = [p, (p+1)%n, (p+2)%n]
                    # All 3 fire (guaranteed since all n fire)
                    total_tested += 1

                    found = False
                    for q in arc:
                        left = (q - 1) % n
                        right = (q + 1) % n
                        mt = set()
                        nmt = set()
                        for k in range(CL):
                            triple = (path[k][left], path[k][q], path[k][right])
                            if movers[k] == q:
                                mt.add(triple)
                            else:
                                nmt.add(triple)
                        if mt & nmt:
                            found = True
                            break

                    if not found:
                        failures += 1
                        if failures <= 3:
                            print(f"FAILURE: n={n}, ms={ms}, CL={CL}")
                            print(f"  fire_counts={dict(fire_counts)}")
                            arc_fc = sum(fire_counts[q] for q in arc)
                            print(f"  arc={arc}, arc_total_fc={arc_fc}")

    print(f"\nTotal 3-arcs tested (all n procs fire): {total_tested}")
    print(f"Failures: {failures}")
    if total_tested > 0:
        print(f"EC rate: {(total_tested - failures)/total_tested:.6f}")


def check_n_ge_4_neighbors_fire():
    """
    Stronger hypothesis: the 3-arc {p, p+1, p+2} AND its neighbors {p-1, p+3} all fire.
    This gives a 5-arc where at least the middle 3 fire.
    With neighbors firing, there MUST be non-arc steps between arc sojourns,
    potentially providing the "gap" needed for EC.
    """
    print("\n=== Testing 5-Neighborhood Hypothesis ===")
    print("(Require p-1, p, p+1, p+2, p+3 all fire)")

    random.seed(42)
    total_tested = 0
    failures = 0

    for n in [7, 8, 9]:
        for ms_type in ['binary', 'ternary', 'mixed']:
            if ms_type == 'binary':
                ms = [2]*n
            elif ms_type == 'ternary':
                ms = [3]*n
            else:
                ms = [2,2,2] + [3]*(n-3)

            for trial in range(20000):
                config = tuple(random.randint(0, ms[i]-1) for i in range(n))
                path = [config]
                movers = []
                visited = {config}

                for step in range(200):
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
                        break
                    else:
                        non_closing = [c for c in candidates if not c[3]]
                        if not non_closing:
                            if closing:
                                i, v, new_config, _ = random.choice(closing)
                                movers.append(i)
                                break
                            break
                        i, v, new_config, _ = random.choice(non_closing)
                        movers.append(i)
                        config = new_config
                        path.append(config)
                        visited.add(config)
                else:
                    continue

                CL = len(movers)
                if CL < 3:
                    continue

                fire_set = set(movers)
                fire_counts = defaultdict(int)
                for m in movers:
                    fire_counts[m] += 1

                for p in range(n):
                    arc = [p, (p+1)%n, (p+2)%n]
                    neighborhood = [(p-1)%n, p, (p+1)%n, (p+2)%n, (p+3)%n]
                    if not all(q in fire_set for q in neighborhood):
                        continue

                    total_tested += 1

                    found = False
                    for q in arc:
                        left = (q - 1) % n
                        right = (q + 1) % n
                        mt = set()
                        nmt = set()
                        for k in range(CL):
                            triple = (path[k][left], path[k][q], path[k][right])
                            if movers[k] == q:
                                mt.add(triple)
                            else:
                                nmt.add(triple)
                        if mt & nmt:
                            found = True
                            break

                    if not found:
                        failures += 1
                        if failures <= 5:
                            print(f"FAILURE: n={n}, ms={ms}, CL={CL}")
                            print(f"  fire_counts={dict(fire_counts)}")
                            print(f"  arc={arc}, neighborhood={neighborhood}")

    print(f"\nTotal 3-arcs tested (5-neighborhood): {total_tested}")
    print(f"Failures: {failures}")
    if total_tested > 0:
        print(f"EC rate: {(total_tested - failures)/total_tested:.6f}")


def check_concentrated_walk_hypothesis():
    """
    The opposite hypothesis: failures occur when the walk is concentrated
    in the arc. Test: if the walk visits at least n-2 distinct procs
    (not just the 3 in the arc), does EC always hold?

    Actually, let me look at the failures differently.
    The walk never leaves the 3-arc in some failures (all movers in {p,p+1,p+2}).
    In that case, the triple at the middle proc changes at EVERY step,
    and the "gap" argument doesn't apply.

    For the lower bound proof: the good cycle of a self-stabilizing system
    visits ALL configs. Every proc fires at least m_i - 1 >= 1 times.
    The cycle has length equal to the number of good configs.
    This is typically much larger than the 3-arc fire count.
    """
    print("\n=== Checking if walk leaves arc ===")

    random.seed(42)
    total_tested = 0
    failures_in_arc = 0
    failures_leave_arc = 0

    for n in [7, 8, 9]:
        for ms in [[3]*n, [2,2,2]+[3]*(n-3)]:
            for trial in range(20000):
                config = tuple(random.randint(0, ms[i]-1) for i in range(n))
                path = [config]
                movers = []
                visited = {config}

                for step in range(200):
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
                        break
                    else:
                        non_closing = [c for c in candidates if not c[3]]
                        if not non_closing:
                            if closing:
                                i, v, new_config, _ = random.choice(closing)
                                movers.append(i)
                                break
                            break
                        i, v, new_config, _ = random.choice(non_closing)
                        movers.append(i)
                        config = new_config
                        path.append(config)
                        visited.add(config)
                else:
                    continue

                CL = len(movers)
                if CL < 3:
                    continue

                fire_set = set(movers)
                fire_counts = defaultdict(int)
                for m in movers:
                    fire_counts[m] += 1

                for p in range(n):
                    arc = [p, (p+1)%n, (p+2)%n]
                    arc_set = set(arc)
                    if not all(q in fire_set for q in arc):
                        continue

                    total_tested += 1

                    found = False
                    for q in arc:
                        left = (q - 1) % n
                        right = (q + 1) % n
                        mt = set()
                        nmt = set()
                        for k in range(CL):
                            triple = (path[k][left], path[k][q], path[k][right])
                            if movers[k] == q:
                                mt.add(triple)
                            else:
                                nmt.add(triple)
                        if mt & nmt:
                            found = True
                            break

                    if not found:
                        # Does the walk ever leave the arc?
                        non_arc_steps = sum(1 for m in movers if m not in arc_set)
                        if non_arc_steps == 0:
                            failures_in_arc += 1
                        else:
                            failures_leave_arc += 1
                            if failures_leave_arc <= 5:
                                print(f"FAILURE (leaves arc): n={n}, ms={ms}, CL={CL}")
                                print(f"  arc={arc}, non_arc_steps={non_arc_steps}")
                                print(f"  fire_counts={dict(fire_counts)}")

                                # How many non-arc steps are there between flanking fires and p+1 fires?
                                q = arc[1]  # middle
                                for j_idx, k in enumerate(k for k in range(CL) if movers[k] == q):
                                    prev = (k - 1) % CL
                                    if movers[prev] not in arc_set:
                                        print(f"    Fire of q={q} at step {k}: "
                                              f"preceded by non-arc mover {movers[prev]} — should give EC!")

    print(f"\nTotal 3-arcs: {total_tested}")
    print(f"Failures with walk IN arc only: {failures_in_arc}")
    print(f"Failures with walk LEAVING arc: {failures_leave_arc}")


if __name__ == "__main__":
    find_and_analyze_failures()
    check_all_procs_fire_hypothesis()
    check_n_ge_4_neighbors_fire()
    check_concentrated_walk_hypothesis()
