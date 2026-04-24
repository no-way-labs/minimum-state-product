#!/usr/bin/env python3
"""Feasibility test: Does the paper's Layer 3 (binary bounce / No Binary 2-Cycle)
kill ALL zero-winding non-sweep cycles for non-consecutive ≥3 binary sub-threshold?

Layer 3 (Claim 4.6.3): If some binary proc P_a's two firings are split by
both firings of an adjacent binary proc P_b (i.e., binary firings interleaved),
then P_b sees the same (L,R) context at both firings → Binary 2-Cycle → contradiction.

We check: for every good cycle found, is there at least one pair of adjacent
binary procs with interleaved firings?

If YES for all cycles: Layer 3 kills everything, Layer 4 not needed, reroute works.
If NO for some cycle: Layer 3 doesn't suffice, need Layer 4 or another argument.

Also check: do ANY non-sweep zero-winding cycles survive to this point at all?
(They shouldn't for converging systems, but let's see what the mover word structure is.)
"""
import random
from itertools import product as iterproduct


def random_transition(m_left, m_self, m_right):
    f = {}
    for L in range(m_left):
        for S in range(m_self):
            for R in range(m_right):
                f[(L, S, R)] = random.randint(0, m_self - 1)
    return f


def privileged(config, sys_f, ms, n, i):
    return sys_f[i][(config[(i-1)%n], config[i], config[(i+1)%n])] != config[i]


def find_unique_privileged(config, sys_f, ms, n):
    privs = [i for i in range(n) if privileged(config, sys_f, ms, n, i)]
    return privs[0] if len(privs) == 1 else None


def apply_move(config, sys_f, ms, n, i):
    nc = list(config)
    nc[i] = sys_f[i][(config[(i-1)%n], config[i], config[(i+1)%n])]
    return tuple(nc)


def is_sweep(movers, n):
    """Check if the mover word is a uniform sweep (all same direction)."""
    if len(movers) < 2:
        return False
    for i in range(len(movers)):
        curr = movers[i]
        nxt = movers[(i+1) % len(movers)]
        diff = (nxt - curr) % n
        if diff != 1 and diff != n-1:
            return False  # has a stay or jump
    # Check all same direction
    dirs = set()
    for i in range(len(movers)):
        curr = movers[i]
        nxt = movers[(i+1) % len(movers)]
        diff = (nxt - curr) % n
        if diff == 1:
            dirs.add('cw')
        elif diff == n-1:
            dirs.add('ccw')
    return len(dirs) == 1


def total_displacement(movers, n):
    td = 0
    for i in range(len(movers)):
        curr = movers[i]
        nxt = movers[(i+1) % len(movers)]
        diff = (nxt - curr) % n
        if diff == 1:
            td += 1
        elif diff == n-1:
            td -= 1
    return td


def has_reversal(movers, n):
    """Check if the mover word has at least one direction reversal."""
    L = len(movers)
    for i in range(L):
        prev_dir = (movers[i] - movers[(i-1) % L]) % n
        next_dir = (movers[(i+1) % L] - movers[i]) % n
        # prev step was CW (diff=1), next step is CCW (diff=n-1) or vice versa
        if prev_dir == 1 and next_dir == n-1:
            return True
        if prev_dir == n-1 and next_dir == 1:
            return True
    return False


def count_reversals(movers, n):
    """Count direction reversals in the mover word."""
    L = len(movers)
    count = 0
    for i in range(L):
        prev_dir = (movers[i] - movers[(i-1) % L]) % n
        next_dir = (movers[(i+1) % L] - movers[i]) % n
        if prev_dir == 1 and next_dir == n-1:
            count += 1
        if prev_dir == n-1 and next_dir == 1:
            count += 1
    return count


def check_layer3_interleaved(movers, ms, n):
    """Check if Layer 3 (binary bounce) applies.

    Layer 3: some binary P_a's two firings bracket both firings of adjacent binary P_b.
    More precisely: P_a fires at t1 and t2 (t1 < t2), and P_b fires at s1, s2
    with t1 < s1 < s2 < t2.

    We also check the reverse: P_b's firings bracket P_a's.

    Returns (True, detail) if Layer 3 applies, (False, detail) otherwise.
    """
    binary_positions = [i for i in range(n) if ms[i] == 2]

    # Get firing steps for each binary proc
    fire_steps = {p: [] for p in binary_positions}
    for step, mover in enumerate(movers):
        if mover in fire_steps:
            fire_steps[mover].append(step)

    # Check all pairs of adjacent binary procs
    for pa in binary_positions:
        for pb in binary_positions:
            if pa == pb:
                continue
            # Check if pa and pb are ring-adjacent
            if (pa + 1) % n != pb and (pa - 1) % n != pb:
                continue

            steps_a = fire_steps[pa]
            steps_b = fire_steps[pb]

            if len(steps_a) != 2 or len(steps_b) != 2:
                continue

            t1, t2 = steps_a[0], steps_a[1]
            s1, s2 = steps_b[0], steps_b[1]

            # Check if P_a's firings bracket P_b's firings
            if t1 < s1 < s2 < t2:
                return True, f"P_{pa} brackets P_{pb}: {t1}<{s1}<{s2}<{t2}"

            # Also check cyclic bracketing: P_a fires at t2 and then t1 (wrapping)
            # In the cyclic view: t2, ..., L-1, 0, ..., t1 brackets s1, s2
            L = len(movers)
            # P_a fires at t1 and t2. Cyclic intervals: [t1, t2) and [t2, t1+L).
            # Check if both s1, s2 are in [t1+1, t2-1] (already done above)
            # or both in [t2+1, t1+L-1] (cyclic)
            def in_cyclic_interval(s, a, b, L):
                """Check if s is strictly between a and b cyclically."""
                if a < b:
                    return a < s < b
                else:  # wraps around
                    return s > a or s < b

            if in_cyclic_interval(s1, t2, t1, L) and in_cyclic_interval(s2, t2, t1, L):
                # Both s1, s2 in the cyclic interval (t2, t1)
                # Need to check ordering: s1 < s2 in cyclic sense
                return True, f"P_{pa} brackets P_{pb} (cyclic): t2={t2},s1={s1},s2={s2},t1={t1}"

    return False, "no interleaved pair found"


def check_layer2_singleton(movers, ms, n):
    """Check if Layer 2 (two singleton edges) applies.
    For each binary proc with fireCount=2, check if both incident edges are singletons.
    A singleton edge (i, i+1) has exactly 1 crossing in the mover walk.
    """
    binary_positions = [i for i in range(n) if ms[i] == 2]

    # Count edge crossings
    L = len(movers)
    edge_count = {}  # edge (i, i+1) -> count of crossings
    for i in range(n):
        edge_count[i] = 0

    for step in range(L):
        curr = movers[step]
        nxt = movers[(step + 1) % L]
        if (nxt - curr) % n == 1:  # CW: crosses edge (curr, curr+1)
            edge_count[curr] += 1
        elif (nxt - curr) % n == n - 1:  # CCW: crosses edge (curr-1, curr)
            edge_count[(curr - 1) % n] += 1

    singleton_edges = [e for e, c in edge_count.items() if c == 1]
    return len(singleton_edges) >= 2, singleton_edges


def check_return_cone(movers, ms, n):
    """Check if the mover word contains a return cone (a cyclic interval where
    the movers form a contiguous arc and return to start)."""
    L = len(movers)
    fire_steps = {}
    for step, mover in enumerate(movers):
        if mover not in fire_steps:
            fire_steps[mover] = []
        fire_steps[mover].append(step)

    # Check for repeated configs (return cone consequence)
    # A return cone [t, u) has g_t = g_u. With distinct configs, this is impossible.
    # So return cone -> False directly.
    # We check: is there a proper cyclic sub-interval of movers that forms a contiguous arc?
    # This is what two singleton edges give us.
    pass


def main():
    random.seed(42)

    test_configs = [
        # Non-consecutive ≥3 binary, sub-threshold
        (7, [2, 3, 2, 3, 2, 3, 3]),    # alternating, product 648 < 972
        (7, [2, 3, 3, 2, 3, 2, 3]),    # scattered, product 648
        (9, [2, 3, 2, 3, 2, 3, 3, 3, 3]),  # product 5832 < 8748
        (9, [2, 3, 3, 2, 3, 3, 2, 3, 3]),  # product 5832
        (9, [2, 3, 3, 3, 2, 3, 3, 2, 3]),  # product 5832
        # Also test consecutive for comparison
        (9, [2, 2, 2, 3, 3, 3, 3, 3, 3]),  # consecutive, product 5832
    ]

    for n, ms in test_configs:
        product_val = 1
        for m in ms:
            product_val *= m
        threshold = 4 * (3 ** (n - 2))
        num_bin = sum(1 for m in ms if m == 2)

        # Check consecutive
        has_3consec = False
        for i in range(n):
            if ms[i] == 2 and ms[(i+1)%n] == 2 and ms[(i+2)%n] == 2:
                has_3consec = True
                break

        total_cycles = 0
        sweep_count = 0
        zw_nonsweep = 0  # zero winding, non-sweep
        nzw_count = 0    # non-zero winding
        layer2_kills = 0
        layer3_kills = 0
        layer3_fails = 0
        layer3_fail_examples = []

        num_trials = 500000 if n <= 7 else 200000

        for trial in range(num_trials):
            sys_f = {i: random_transition(ms[(i-1)%n], ms[i], ms[(i+1)%n]) for i in range(n)}
            config = tuple(random.randint(0, ms[i]-1) for i in range(n))
            visited = {}
            for step in range(3000):
                if config in visited:
                    start = visited[config]
                    cycle = []
                    c = config
                    ok = True
                    for _ in range(step - start):
                        p = find_unique_privileged(c, sys_f, ms, n)
                        if p is None:
                            ok = False
                            break
                        cycle.append(p)
                        c = apply_move(c, sys_f, ms, n, p)
                    if ok and cycle:
                        total_cycles += 1
                        movers = cycle
                        td = total_displacement(movers, n)

                        if td != 0:
                            nzw_count += 1
                        elif is_sweep(movers, n):
                            sweep_count += 1
                        else:
                            zw_nonsweep += 1

                            # Check Layer 2 (singleton edges)
                            l2, singletons = check_layer2_singleton(movers, ms, n)
                            if l2:
                                layer2_kills += 1
                                continue

                            # Check Layer 3 (binary bounce / interleaved firings)
                            l3, detail = check_layer3_interleaved(movers, ms, n)
                            if l3:
                                layer3_kills += 1
                            else:
                                layer3_fails += 1
                                if len(layer3_fail_examples) < 3:
                                    fc = [0] * n
                                    for m in movers:
                                        fc[m] += 1
                                    layer3_fail_examples.append({
                                        'movers': movers,
                                        'fire_counts': fc,
                                        'length': len(movers),
                                        'reversals': count_reversals(movers, n),
                                        'detail': detail,
                                    })
                    break
                visited[config] = step
                p = find_unique_privileged(config, sys_f, ms, n)
                if p is None:
                    break
                config = apply_move(config, sys_f, ms, n, p)

        consec_label = "CONSEC" if has_3consec else "NON-CONSEC"
        print(f"\nn={n} ms={ms} prod={product_val} bin={num_bin} [{consec_label}]")
        print(f"  Total cycles: {total_cycles}")
        print(f"  Sweep: {sweep_count}, Non-zero winding: {nzw_count}, ZW non-sweep: {zw_nonsweep}")
        if zw_nonsweep > 0:
            print(f"  Layer 2 kills (singleton edges): {layer2_kills}")
            print(f"  Layer 3 kills (binary bounce): {layer3_kills}")
            print(f"  Layer 3 FAILS: {layer3_fails}")
            if layer3_fail_examples:
                for i, ex in enumerate(layer3_fail_examples):
                    print(f"    Example {i+1}: L={ex['length']}, reversals={ex['reversals']}, "
                          f"fc={ex['fire_counts']}")
                    print(f"      movers={ex['movers'][:20]}{'...' if len(ex['movers']) > 20 else ''}")
                    print(f"      detail: {ex['detail']}")
            if layer3_fails == 0:
                print(f"  → Layer 3 kills ALL zero-winding non-sweep cycles!")
        else:
            print(f"  → No zero-winding non-sweep cycles found")

    print("\n" + "="*60)
    print("FEASIBILITY VERDICT:")
    print("If Layer 3 kills ALL ZW non-sweep for non-consecutive binary:")
    print("  → Reroute is viable. Paper's path closes the sorry.")
    print("If Layer 3 has failures:")
    print("  → Need Layer 4 (wiggle shadow) or alternative argument.")


if __name__ == '__main__':
    main()
