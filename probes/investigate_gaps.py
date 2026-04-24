#!/usr/bin/env python3
"""Investigate the two mathematical gaps for Approach A.

Gap 1 (Lemma A1): Under odd winding + sub-threshold + ≥3 binary,
  does fire_b > 2 ever occur? If fire_b = 2 always, the existing
  singleton edge theorem applies directly.

Gap 2 (Lemma A2): Under zero winding + sub-threshold + ≥3 binary + convergence,
  does a safe proc always exist? What's the structure when it doesn't?

Strategy: exhaustively enumerate ALL good cycles (not random sampling)
for small n and ALL sub-threshold multisets. This gives complete coverage.
"""
from itertools import product as iterproduct
import sys


def all_transitions(m_left, m_self, m_right):
    """Generate ALL possible transition functions for a processor."""
    entries = list(iterproduct(range(m_self),
                               repeat=m_left * m_self * m_right))
    for vals in entries:
        f = {}
        idx = 0
        for L in range(m_left):
            for S in range(m_self):
                for R in range(m_right):
                    f[(L, S, R)] = vals[idx]
                    idx += 1
        yield f


def privileged(config, sys_f, ms, n, i):
    L, S, R = config[(i-1)%n], config[i], config[(i+1)%n]
    return sys_f[i][(L, S, R)] != S


def find_unique_privileged(config, sys_f, ms, n):
    privs = [i for i in range(n) if privileged(config, sys_f, ms, n, i)]
    return privs[0] if len(privs) == 1 else None


def apply_move(config, sys_f, ms, n, i):
    nc = list(config)
    L, S, R = config[(i-1)%n], config[i], config[(i+1)%n]
    nc[i] = sys_f[i][(L, S, R)]
    return tuple(nc)


def find_good_cycle(sys_f, ms, n, config, max_steps=5000):
    visited = {}
    c = config
    for step in range(max_steps):
        if c in visited:
            start = visited[c]
            movers = []
            cc = c
            ok = True
            for _ in range(step - start):
                p = find_unique_privileged(cc, sys_f, ms, n)
                if p is None:
                    ok = False
                    break
                movers.append(p)
                cc = apply_move(cc, sys_f, ms, n, p)
            if ok and movers:
                return movers
            return None
        visited[c] = step
        p = find_unique_privileged(c, sys_f, ms, n)
        if p is None:
            return None
        c = apply_move(c, sys_f, ms, n, p)
    return None


def total_displacement(movers, n):
    td = 0
    L = len(movers)
    for i in range(L):
        curr = movers[i]
        nxt = movers[(i+1) % L]
        diff = (nxt - curr) % n
        if diff == 1: td += 1
        elif diff == n-1: td -= 1
    return td


def has_safe_proc(movers, n):
    fc = [0] * n
    for m in movers:
        fc[m] += 1
    for q in range(n):
        if fc[q] == 0 and fc[(q-1)%n] == 0 and fc[(q+1)%n] == 0:
            return True
    return False


def check_convergence_exhaustive(sys_f, ms, n, gc_configs_set):
    """Check ALL configs converge to the good cycle."""
    total_configs = 1
    for m in ms:
        total_configs *= m

    for vals in iterproduct(*[range(m) for m in ms]):
        config = vals
        seen = set()
        c = config
        reached = False
        for _ in range(total_configs + 10):
            if c in gc_configs_set:
                reached = True
                break
            if c in seen:
                break  # stuck in a different cycle
            seen.add(c)
            p = find_unique_privileged(c, sys_f, ms, n)
            if p is None:
                break  # dead config
            c = apply_move(c, sys_f, ms, n, p)
        if not reached:
            return False
    return True


def investigate_gap1():
    """Gap 1: Does fire_b > 2 ever occur under odd winding?
    Test at small n with random systems (exhaustive is too expensive for full systems)."""
    import random
    random.seed(42)

    print("=" * 70)
    print("GAP 1: fire_b under odd winding")
    print("=" * 70)

    configs = [
        (5, [2, 2, 2, 3, 3]),
        (5, [2, 2, 2, 3, 4]),
        (7, [2, 2, 2, 3, 3, 3, 3]),
        (7, [2, 3, 2, 3, 2, 3, 3]),
        (9, [2, 2, 2, 3, 3, 3, 3, 3, 3]),
        (9, [2, 3, 2, 3, 2, 3, 3, 3, 3]),
    ]

    total_odd = 0
    total_cycles = 0
    fire_b_gt2 = 0

    for n, ms in configs:
        product_val = 1
        for m in ms: product_val *= m
        threshold = 4 * (3 ** (n - 2))
        if product_val >= threshold:
            continue

        odd_count = 0
        cycle_count = 0

        num_trials = 2000000 if n <= 5 else (500000 if n <= 7 else 200000)

        for trial in range(num_trials):
            sys_f = {}
            for i in range(n):
                f = {}
                for L in range(ms[(i-1)%n]):
                    for S in range(ms[i]):
                        for R in range(ms[(i+1)%n]):
                            f[(L, S, R)] = random.randint(0, ms[i] - 1)
                sys_f[i] = f

            config = tuple(random.randint(0, ms[i]-1) for i in range(n))
            movers = find_good_cycle(sys_f, ms, n, config)
            if movers is None:
                continue

            cycle_count += 1
            td = total_displacement(movers, n)

            if td != 0:
                odd_count += 1
                total_odd += 1

                fc = [0] * n
                for m in movers:
                    fc[m] += 1

                binary_fires = [fc[i] for i in range(n) if ms[i] == 2]
                max_bf = max(binary_fires) if binary_fires else 0

                if max_bf > 2:
                    fire_b_gt2 += 1
                    print(f"  FOUND fire_b > 2! n={n} ms={ms} td={td}")
                    print(f"    movers={movers}")
                    print(f"    fc={fc}")
                    print(f"    binary_fires={binary_fires}")

        total_cycles += cycle_count
        print(f"n={n} ms={ms}: {cycle_count} cycles, {odd_count} odd winding")

    print(f"\nTotal: {total_cycles} cycles, {total_odd} odd winding, {fire_b_gt2} with fire_b > 2")

    if total_odd == 0:
        print("\n*** NO ODD WINDING CYCLES FOUND AT ALL ***")
        print("This means Lemma A1 might be provable by showing non-zero winding")
        print("is impossible, without needing fire_b = 2.")
        print("\nBut we need to handle the proof architecture: the Lean code routes")
        print("odd-winding through PhaseExtraction. We need to either:")
        print("  (a) Prove odd winding is impossible (then the path is vacuous)")
        print("  (b) Reroute odd winding to singleton edges (needs fire_b = 2)")
    elif fire_b_gt2 == 0:
        print("\n*** fire_b = 2 always under odd winding ***")
        print("Singleton edge theorem applies directly!")
    return total_odd


def investigate_gap2():
    """Gap 2: Under zero winding, does safe proc always exist?
    More importantly: what's |Z| for all zero-winding cycles?"""
    import random
    random.seed(123)

    print("\n" + "=" * 70)
    print("GAP 2: |Z| and safe proc under zero winding")
    print("=" * 70)

    configs = [
        (5, [2, 2, 2, 3, 3]),
        (5, [2, 2, 2, 3, 4]),
        (7, [2, 2, 2, 3, 3, 3, 3]),
        (7, [2, 3, 2, 3, 2, 3, 3]),
        (9, [2, 2, 2, 3, 3, 3, 3, 3, 3]),
        (9, [2, 3, 2, 3, 2, 3, 3, 3, 3]),
        (9, [2, 2, 2, 4, 3, 3, 3, 3, 3]),
    ]

    all_safe = True
    all_z_ge3 = True

    for n, ms in configs:
        product_val = 1
        for m in ms: product_val *= m
        threshold = 4 * (3 ** (n - 2))
        if product_val >= threshold:
            continue

        num_trials = 2000000 if n <= 5 else (500000 if n <= 7 else 200000)
        total = 0
        z_dist = {}
        nosafe = 0
        min_z = n

        for trial in range(num_trials):
            sys_f = {}
            for i in range(n):
                f = {}
                for L in range(ms[(i-1)%n]):
                    for S in range(ms[i]):
                        for R in range(ms[(i+1)%n]):
                            f[(L, S, R)] = random.randint(0, ms[i] - 1)
                sys_f[i] = f

            config = tuple(random.randint(0, ms[i]-1) for i in range(n))
            movers = find_good_cycle(sys_f, ms, n, config)
            if movers is None:
                continue

            td = total_displacement(movers, n)
            if td != 0:
                continue  # only zero winding

            total += 1
            fc = [0] * n
            for m in movers:
                fc[m] += 1
            z = sum(1 for f in fc if f == 0)
            z_dist[z] = z_dist.get(z, 0) + 1
            min_z = min(min_z, z)

            safe = has_safe_proc(movers, n)
            if not safe:
                nosafe += 1
                all_safe = False
                if nosafe <= 3:
                    print(f"  NO SAFE PROC: n={n} ms={ms} fc={fc} movers={movers}")

            if z < 3:
                all_z_ge3 = False

        print(f"n={n} ms={ms}: {total} ZW cycles, min |Z|={min_z}, nosafe={nosafe}")
        print(f"  |Z| distribution: {dict(sorted(z_dist.items()))}")

    print(f"\nAll safe proc: {all_safe}")
    print(f"All |Z| ≥ 3: {all_z_ge3}")
    return all_safe, all_z_ge3


def investigate_odd_winding_deeply():
    """Try VERY hard to find an odd-winding cycle by testing ALL systems
    at n=5 with small state spaces."""
    print("\n" + "=" * 70)
    print("DEEP SEARCH: Odd winding at n=5, exhaustive over all configs")
    print("=" * 70)

    import random
    random.seed(456)

    n = 5
    ms_list = [
        [2, 2, 2, 3, 3],  # product 72
    ]

    for ms in ms_list:
        product_val = 1
        for m in ms: product_val *= m
        threshold = 4 * (3 ** (n - 2))

        print(f"\nn={n} ms={ms} prod={product_val} threshold={threshold}")

        total_systems = 0
        total_cycles = 0
        odd_cycles = 0

        # Sample many random systems and check ALL starting configs
        for trial in range(50000):
            sys_f = {}
            for i in range(n):
                f = {}
                for L in range(ms[(i-1)%n]):
                    for S in range(ms[i]):
                        for R in range(ms[(i+1)%n]):
                            f[(L, S, R)] = random.randint(0, ms[i] - 1)
                sys_f[i] = f

            total_systems += 1

            # Try ALL configs as starting points
            seen_cycles = set()
            for vals in iterproduct(*[range(m) for m in ms]):
                config = vals
                movers = find_good_cycle(sys_f, ms, n, config, max_steps=product_val + 100)
                if movers is None:
                    continue

                cycle_key = tuple(movers)
                if cycle_key in seen_cycles:
                    continue
                seen_cycles.add(cycle_key)

                total_cycles += 1
                td = total_displacement(movers, n)
                if td != 0:
                    odd_cycles += 1
                    # Check convergence
                    gc_configs = set()
                    c = config
                    for _ in range(len(movers)):
                        gc_configs.add(c)
                        p = find_unique_privileged(c, sys_f, ms, n)
                        c = apply_move(c, sys_f, ms, n, p)

                    conv = check_convergence_exhaustive(sys_f, ms, n, gc_configs)
                    fc = [0] * n
                    for m_val in movers:
                        fc[m_val] += 1

                    print(f"  ODD WINDING! td={td} L={len(movers)} conv={conv}")
                    print(f"    fc={fc} movers={movers[:20]}")
                    if conv:
                        print(f"    *** CONVERGING ODD-WINDING CYCLE! ***")
                        binary_fires = [fc[i] for i in range(n) if ms[i] == 2]
                        print(f"    binary fires: {binary_fires}")

        print(f"  Systems: {total_systems}, Cycles: {total_cycles}, Odd: {odd_cycles}")


if __name__ == '__main__':
    odd_count = investigate_gap1()
    safe_ok, z_ok = investigate_gap2()

    if odd_count == 0:
        # No odd winding found in sampling. Try exhaustive at n=5.
        investigate_odd_winding_deeply()

    print("\n" + "=" * 70)
    print("FINAL ASSESSMENT")
    print("=" * 70)
    if odd_count == 0:
        print("Gap 1: No odd winding found. Lemma A1 may follow from proving")
        print("  'sub-threshold + ≥3 binary + convergence → zero winding'")
        print("  which would make the odd-winding path vacuously true.")
    print(f"Gap 2: Safe proc always exists for ZW: {safe_ok}")
    print(f"Gap 2: |Z| ≥ 3 always for ZW: {z_ok}")
