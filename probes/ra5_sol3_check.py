"""
ra5_sol3_check.py — Check why Sol3 v1 fails and understand real RA systems.

The issue: Sol3 v1's transition function f0(L,S,R) = 1-S if L==S, else S.
For proc 0 (binary): privileged when L == S. L = config[n-1] (ternary).
S = config[0] (binary: 0 or 1). L = 0, 1, or 2.
L == S when L ∈ {0, 1} and S = L. Since S is binary: S ∈ {0, 1}.
So proc 0 is privileged when config[n-1] == config[0].
But config[n-1] can be 2 and config[0] is binary. If config[n-1] = 2: proc 0 is never privileged (since S = 0 or 1, neither equals 2).

For ternary proc i: f(L, S, R) = (S+1)%3 if L != S, else S.
Privileged when L != S.

The good cycle should work. Let me check with a concrete small example.
"""

from itertools import product as iproduct
from collections import defaultdict


def ring_dist(a, b, n):
    d = abs(a - b)
    return min(d, n - d)


def test_sol3v1_small():
    """Test Sol 3 v1 at n=3 (smallest)."""
    n = 3
    ms = [2, 3, 3]

    def f0(L, S, R):
        if L == S:
            return 1 - S
        return S

    def fi(L, S, R):
        if L != S:
            return (S + 1) % 3
        return S

    fs = [f0, fi, fi]

    all_cfgs = list(iproduct(*(range(m) for m in ms)))
    print(f"n={n}, ms={ms}, total configs={len(all_cfgs)}")

    # Find privileged processors for each config
    good = []
    for c in all_cfgs:
        priv = []
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            if fs[i](L, S, R) != S:
                priv.append(i)
        if len(priv) == 1:
            good.append(c)

    print(f"Good configs: {len(good)}")

    # Follow good cycle
    start = good[0]
    path = [start]
    movers = []
    current = start
    while True:
        priv = []
        for i in range(n):
            L = current[(i-1)%n]; S = current[i]; R = current[(i+1)%n]
            if fs[i](L, S, R) != S:
                priv.append(i)
        if len(priv) != 1:
            print(f"ERROR: config {current} has {len(priv)} privileged: {priv}")
            break
        mover = priv[0]
        movers.append(mover)
        L = current[(mover-1)%n]; S = current[mover]; R = current[(mover+1)%n]
        new_S = fs[mover](L, S, R)
        nc = list(current); nc[mover] = new_S; current = tuple(nc)
        if current == start:
            break
        path.append(current)

    CL = len(movers)
    print(f"Good cycle length: {CL}")
    print(f"Movers: {movers}")

    # Check ring-adjacency
    for i in range(CL):
        j = (i+1) % CL
        d = ring_dist(movers[i], movers[j], n)
        if d > 1:
            print(f"Not ring-adjacent at step {i}: {movers[i]} -> {movers[j]} (dist={d})")

    print()
    for k in range(CL):
        print(f"  Step {k}: config={path[k]}, mover={movers[k]}")


def test_all_binary():
    """Test all-binary systems — these should have ring-adjacent good cycles more often."""
    print("\n=== All-Binary Systems ===")

    for n in [5, 6, 7]:
        ms = [2]*n

        # Dijkstra's original solution: f_i(L, S, R) = (L + 1) % 2 for bottom, etc.
        # Actually, for all-binary unidirectional ring:
        # f_0(L, S, R) = 1 - L  (bottom: takes complement of left neighbor's state)
        # f_i(L, S, R) = L      (others: copy left neighbor)

        def f_bottom(L, S, R):
            return 1 - L

        def f_other(L, S, R):
            return L

        fs = [f_bottom] + [f_other]*(n-1)

        all_cfgs = list(iproduct(*(range(m) for m in ms)))

        good = []
        for c in all_cfgs:
            priv = []
            for i in range(n):
                L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                if fs[i](L, S, R) != S:
                    priv.append(i)
            if len(priv) == 1:
                good.append(c)

        print(f"n={n}: good configs = {len(good)}")

        if len(good) == 0:
            continue

        # Follow good cycle
        start = good[0]
        path = [start]
        movers = []
        current = start
        while True:
            priv = []
            for i in range(n):
                L = current[(i-1)%n]; S = current[i]; R = current[(i+1)%n]
                if fs[i](L, S, R) != S:
                    priv.append(i)
            if len(priv) != 1:
                print(f"  ERROR: {len(priv)} privileged at {current}")
                break
            mover = priv[0]
            movers.append(mover)
            L = current[(mover-1)%n]; S = current[mover]; R = current[(mover+1)%n]
            new_S = fs[mover](L, S, R)
            nc = list(current); nc[mover] = new_S; current = tuple(nc)
            if current == start:
                break
            path.append(current)

        CL = len(movers)
        print(f"  CL={CL}, movers={movers[:20]}{'...' if CL > 20 else ''}")

        # Check RA
        ra_violations = sum(1 for i in range(CL) if ring_dist(movers[i], movers[(i+1)%CL], n) > 1)
        print(f"  RA violations: {ra_violations}")

        if ra_violations == 0:
            fire_counts = defaultdict(int)
            for m in movers:
                fire_counts[m] += 1
            print(f"  fire counts: {dict(fire_counts)}")

            # Check 3-arc EC
            total_arcs = 0
            ec_found = 0
            for p in range(n):
                arc = [p, (p+1)%n, (p+2)%n]
                if not all(fire_counts[q] > 0 for q in arc):
                    continue
                total_arcs += 1
                found = False
                for q in arc:
                    left = (q-1)%n; right = (q+1)%n
                    mt = set(); nmt = set()
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
                    ec_found += 1
            print(f"  3-arcs: {total_arcs}, EC: {ec_found}")


def test_bidirectional_binary():
    """Test bidirectional binary systems — movers can be any adjacent proc."""
    print("\n=== Bidirectional Binary Systems ===")

    import random
    random.seed(42)

    for n in [5, 6, 7]:
        ms = [2]*n
        ra_systems = 0
        total_arcs = 0
        ec_found = 0

        for trial in range(10000):
            # Random transition function tables
            fs = []
            for i in range(n):
                table = {}
                for L in range(ms[(i-1)%n]):
                    for S in range(ms[i]):
                        for R in range(ms[(i+1)%n]):
                            table[(L, S, R)] = random.randint(0, ms[i]-1)
                def make_f(t):
                    def f(L, S, R):
                        return t[(L, S, R)]
                    return f
                fs.append(make_f(table))

            all_cfgs = list(iproduct(*(range(m) for m in ms)))

            good = set()
            for c in all_cfgs:
                priv = []
                for i in range(n):
                    L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                    if fs[i](L, S, R) != S:
                        priv.append(i)
                if len(priv) == 1:
                    good.add(c)

            if len(good) < 3:
                continue

            # Check closure
            closure_ok = True
            for c in good:
                priv = [i for i in range(n) if fs[i](c[(i-1)%n], c[i], c[(i+1)%n]) != c[i]]
                assert len(priv) == 1
                mover = priv[0]
                nc = list(c)
                nc[mover] = fs[mover](c[(mover-1)%n], c[mover], c[(mover+1)%n])
                if tuple(nc) not in good:
                    closure_ok = False
                    break

            if not closure_ok:
                continue

            # Find good cycle
            start = next(iter(good))
            path = [start]
            movers = []
            current = start
            seen = {start}
            ok = True
            while True:
                priv = [i for i in range(n) if fs[i](current[(i-1)%n], current[i], current[(i+1)%n]) != current[i]]
                if len(priv) != 1:
                    ok = False; break
                mover = priv[0]
                movers.append(mover)
                nc = list(current)
                nc[mover] = fs[mover](current[(mover-1)%n], current[mover], current[(mover+1)%n])
                current = tuple(nc)
                if current == start:
                    break
                if current in seen:
                    ok = False; break
                seen.add(current)
                path.append(current)

            if not ok or len(movers) != len(good):
                continue

            CL = len(movers)
            ra_ok = all(ring_dist(movers[i], movers[(i+1)%CL], n) <= 1 for i in range(CL))
            if not ra_ok:
                continue

            ra_systems += 1

            fire_counts = defaultdict(int)
            for m in movers:
                fire_counts[m] += 1

            for p in range(n):
                arc = [p, (p+1)%n, (p+2)%n]
                if not all(fire_counts[q] > 0 for q in arc):
                    continue
                total_arcs += 1
                found = False
                for q in arc:
                    left = (q-1)%n; right = (q+1)%n
                    mt = set(); nmt = set()
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
                    ec_found += 1
                else:
                    print(f"  NO EC at n={n}: CL={CL}, arc={arc}, "
                          f"fc=({fire_counts[arc[0]]},{fire_counts[arc[1]]},{fire_counts[arc[2]]})")

        print(f"n={n}: {ra_systems} RA systems, {total_arcs} arcs, {ec_found} EC")


if __name__ == "__main__":
    test_sol3v1_small()
    test_all_binary()
    test_bidirectional_binary()
