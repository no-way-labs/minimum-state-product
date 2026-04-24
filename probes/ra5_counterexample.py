"""
ra5_counterexample.py — Analyze the counterexamples to understand the true lemma.

The "failures" have CL=14=2n on all-binary n=7. Each proc fires exactly 2 times.
Is the lemma actually false as stated, or do the counterexamples violate some
implicit assumption?

Key question: does the lemma require that the cycle visits ALL good configs
of some self-stabilizing system? Or just "any sequence of distinct configs"?

If the former: the cycle must be the full good cycle, which for all-binary n=7
has length 2^7 - 7·2^5 + ... Actually, the good cycle length depends on the system.

Let me carefully re-examine: these short cycles are NOT the good cycles of any
actual self-stabilizing system. The lemma should probably require that the cycle
IS the good cycle of a self-stabilizing system.

But the problem statement says just "good cycle (all configs distinct)".
Let me verify whether the counterexamples truly have no EC.
"""

import random
from collections import defaultdict


def ring_dist(a, b, n):
    d = abs(a - b)
    return min(d, n - d)


def verify_no_ec(path, movers, arc, n):
    """Exhaustively verify no EC at any arc processor."""
    CL = len(movers)
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
                    return False, q, k1, k2, t1
    return True, None, None, None, None


def analyze_counterexample():
    """Look at Failure 1 in detail."""
    print("=== Counterexample Analysis ===")
    print()

    n = 7
    ms = [2]*7

    # Failure 1 from debug output:
    # Movers: [5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6, 0, 6]
    # Arc: [6, 0, 1]
    movers = [5, 4, 3, 2, 1, 0, 1, 2, 3, 4, 5, 6, 0, 6]
    CL = len(movers)

    # Verify ring-adjacency (including wraparound)
    print("Ring-adjacency check:")
    for i in range(CL):
        nxt = (i + 1) % CL
        d = ring_dist(movers[i], movers[nxt], n)
        if d > 1:
            print(f"  VIOLATION: step {i}→{nxt}: mover {movers[i]}→{movers[nxt]}, dist={d}")
    print("  All adjacent: OK" if all(ring_dist(movers[i], movers[(i+1)%CL], n) <= 1 for i in range(CL)) else "  VIOLATIONS FOUND")

    print(f"\nMover sequence: {movers}")
    print(f"Fire counts: {dict((i, movers.count(i)) for i in range(n))}")
    print(f"Arc {[6,0,1]}: all fire at least once: "
          f"6→{movers.count(6)}, 0→{movers.count(0)}, 1→{movers.count(1)}")

    # Reconstruct the path
    # Start with arbitrary config, apply movers
    config = [0]*n
    path = [tuple(config)]
    for k in range(CL - 1):
        m = movers[k]
        config = list(path[-1])
        config[m] = 1 - config[m]  # binary toggle
        path.append(tuple(config))

    # Check the cycle closes
    final = list(path[-1])
    final[movers[-1]] = 1 - final[movers[-1]]
    closes = (tuple(final) == path[0])
    print(f"\nCycle closes: {closes}")

    # Check all configs distinct
    distinct = len(set(path)) == CL
    print(f"All configs distinct: {distinct} ({len(set(path))} out of {CL})")

    if not distinct:
        print("  NOT A VALID CYCLE — duplicate configs!")
        for i in range(CL):
            for j in range(i+1, CL):
                if path[i] == path[j]:
                    print(f"  Duplicate: path[{i}] = path[{j}] = {path[i]}")
        return

    # Show path
    print("\nPath:")
    arc = [6, 0, 1]
    for k in range(CL):
        triple_6 = (path[k][5], path[k][6], path[k][0])
        triple_0 = (path[k][6], path[k][0], path[k][1])
        triple_1 = (path[k][0], path[k][1], path[k][2])
        tag = f"  mover={movers[k]}"
        if movers[k] == 6:
            tag += " [MOVER for proc 6]"
        elif movers[k] == 0:
            tag += " [MOVER for proc 0]"
        elif movers[k] == 1:
            tag += " [MOVER for proc 1]"
        print(f"  Step {k:2d}: config={path[k]}, triples: 6={triple_6}, 0={triple_0}, 1={triple_1}{tag}")

    # Verify no EC
    no_ec, q, k1, k2, t = verify_no_ec(path, movers, arc, n)
    if no_ec:
        print("\nCONFIRMED: No EC at any arc processor!")
    else:
        print(f"\nEC found at proc {q}: steps {k1} (mover) and {k2} (non-mover), triple={t}")


def count_failures_by_cycle_length():
    """How do failures correlate with cycle length?"""
    print("\n=== Failures by Cycle Length ===")

    random.seed(42)
    n = 7

    for ms in [[2]*7, [3]*7]:
        print(f"\nms={ms}:")
        cycles = []
        for attempt in range(20000):
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
                    cycles.append((list(path), list(movers)))
                    break
                else:
                    non_closing = [c for c in candidates if not c[3]]
                    if not non_closing:
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

        # Analyze by cycle length
        by_len = defaultdict(lambda: {'total': 0, 'no_ec': 0})

        for path, movers in cycles:
            CL = len(movers)
            fire_set = set(movers)
            fire_counts = defaultdict(int)
            for m in movers:
                fire_counts[m] += 1

            for p in range(n):
                arc = [p, (p+1)%n, (p+2)%n]
                if not all(q in fire_set for q in arc):
                    continue

                by_len[CL]['total'] += 1

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
                    by_len[CL]['no_ec'] += 1

        print(f"  {'CL':>4s} {'total':>6s} {'no_ec':>6s} {'rate':>8s}")
        for cl in sorted(by_len):
            t = by_len[cl]['total']
            ne = by_len[cl]['no_ec']
            print(f"  {cl:4d} {t:6d} {ne:6d} {ne/t:8.4f}")


def check_min_fire_count():
    """
    For the counterexamples: what are the fire counts in the 3-arc?
    If each proc fires only 1-2 times, the triple space is small.

    Perhaps the lemma needs: each of the 3 procs fires at least m_i times?
    Or at least: the arc contributes enough fires?
    """
    print("\n=== Fire Count Analysis for Failures ===")

    random.seed(42)
    n = 7
    ms = [2]*7

    cycles = []
    for attempt in range(20000):
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
                cycles.append((list(path), list(movers)))
                break
            else:
                non_closing = [c for c in candidates if not c[3]]
                if not non_closing:
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

    failures_by_fc = defaultdict(int)
    success_by_fc = defaultdict(int)

    for path, movers in cycles:
        CL = len(movers)
        fire_set = set(movers)
        fc = defaultdict(int)
        for m in movers:
            fc[m] += 1

        for p in range(n):
            arc = [p, (p+1)%n, (p+2)%n]
            if not all(q in fire_set for q in arc):
                continue

            arc_fc = tuple(sorted([fc[q] for q in arc]))

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

            if found:
                success_by_fc[arc_fc] += 1
            else:
                failures_by_fc[arc_fc] += 1

    print(f"\nFire count patterns (sorted fc of 3 arc procs):")
    all_fcs = sorted(set(list(failures_by_fc.keys()) + list(success_by_fc.keys())))
    print(f"  {'fc':>12s} {'success':>8s} {'failure':>8s} {'fail_rate':>10s}")
    for fc in all_fcs:
        s = success_by_fc[fc]
        f = failures_by_fc[fc]
        rate = f / (s + f) if s + f > 0 else 0
        print(f"  {str(fc):>12s} {s:8d} {f:8d} {rate:10.4f}")


def check_total_fire_threshold():
    """
    Does the lemma hold when total fires of the 3-arc ≥ some threshold?
    """
    print("\n=== Total Fire Threshold ===")

    random.seed(42)
    n = 7
    ms = [2]*7

    cycles = []
    for attempt in range(20000):
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
                cycles.append((list(path), list(movers)))
                break
            else:
                non_closing = [c for c in candidates if not c[3]]
                if not non_closing:
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

    by_total_fc = defaultdict(lambda: [0, 0])  # [success, failure]

    for path, movers in cycles:
        CL = len(movers)
        fire_set = set(movers)
        fc = defaultdict(int)
        for m in movers:
            fc[m] += 1

        for p in range(n):
            arc = [p, (p+1)%n, (p+2)%n]
            if not all(q in fire_set for q in arc):
                continue

            total_fc = sum(fc[q] for q in arc)

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

            if found:
                by_total_fc[total_fc][0] += 1
            else:
                by_total_fc[total_fc][1] += 1

    print(f"\n  {'total_fc':>10s} {'success':>8s} {'failure':>8s} {'fail_rate':>10s}")
    for tfc in sorted(by_total_fc):
        s, f = by_total_fc[tfc]
        rate = f / (s + f) if s + f > 0 else 0
        print(f"  {tfc:10d} {s:8d} {f:8d} {rate:10.4f}")


if __name__ == "__main__":
    analyze_counterexample()
    count_failures_by_cycle_length()
    check_min_fire_count()
    check_total_fire_threshold()
