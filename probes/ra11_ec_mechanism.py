"""
ra11_ec_mechanism.py — Identify WHICH entry conflict mechanism fires
for odd-winding non-uniform all-isolated cycles at n=9.

Key question: is it always at a binary proc? At the ternary-binary boundary?
What is the gap structure that produces it?
"""

import random
import itertools

random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

def total_displacement(movers, n):
    W = 0
    L = len(movers)
    for i in range(L):
        diff = (movers[(i+1) % L] - movers[i]) % n
        if diff == 0: pass
        elif diff <= n // 2: W += diff
        else: W -= (n - diff)
    return W

def has_isolated_firings(movers, p):
    L = len(movers)
    for i in range(L):
        if movers[i] == p and movers[(i+1) % L] == p:
            return False
    return True

def fire_count(movers, n):
    fc = [0] * n
    for m in movers: fc[m] += 1
    return fc

def find_ec_details(configs, movers, n, ms):
    """Find ALL entry conflicts and return details."""
    ecs = []
    for p in range(n):
        lp = left(p, n)
        rp = right(p, n)
        mover_steps = {}  # ctx -> [step indices]
        nonmover_steps = {}

        for i, m in enumerate(movers):
            ctx = (configs[i][lp], configs[i][p], configs[i][rp])
            if m == p:
                mover_steps.setdefault(ctx, []).append(i)
            else:
                nonmover_steps.setdefault(ctx, []).append(i)

        for ctx in mover_steps:
            if ctx in nonmover_steps:
                ecs.append({
                    'proc': p,
                    'ctx': ctx,
                    'mover_steps': mover_steps[ctx],
                    'nonmover_steps': nonmover_steps[ctx],
                    'is_binary': ms[p] == 2,
                    'left_binary': ms[lp] == 2,
                    'right_binary': ms[rp] == 2,
                })

    return ecs


def random_transition_fn(n, ms):
    trans_fn = {}
    for p in range(n):
        f = {}
        lp = left(p, n)
        rp = right(p, n)
        for L_val in range(ms[lp]):
            for S_val in range(ms[p]):
                for R_val in range(ms[rp]):
                    f[(L_val, S_val, R_val)] = random.choice(range(ms[p]))
        trans_fn[p] = f
    return trans_fn


def find_good_cycles(n, ms, trans_fn, max_cycles=50):
    cycles = []
    for trial in range(10000):
        config = tuple(random.randint(0, ms[p]-1) for p in range(n))
        visited = {config: 0}
        path_configs = [config]
        path_movers = []

        for step in range(200):
            mover = random.randint(0, n-1)
            L_val = config[left(mover, n)]
            S_val = config[mover]
            R_val = config[right(mover, n)]
            new_S = trans_fn[mover][(L_val, S_val, R_val)]
            if new_S == S_val:
                continue

            new_config = list(config)
            new_config[mover] = new_S
            new_config = tuple(new_config)
            path_movers.append(mover)
            path_configs.append(new_config)

            if new_config in visited:
                start = visited[new_config]
                cycle_configs = path_configs[start:-1]
                cycle_movers = path_movers[start:]
                if len(cycle_movers) >= 2:
                    cycles.append((cycle_configs, cycle_movers))
                if len(cycles) >= max_cycles:
                    return cycles
                break

            visited[new_config] = len(path_configs) - 1
            config = new_config

    return cycles


def main():
    n = 9
    ms = [2, 3, 3, 2, 3, 3, 2, 3, 3]  # binary at 0, 3, 6
    binary = [0, 3, 6]

    print(f"n={n}, ms={ms}")
    print(f"Binary: {binary}")
    print()

    ec_at_binary = 0
    ec_at_ternary = 0
    ec_at_boundary = 0  # ternary proc next to binary
    ec_at_interior = 0  # ternary proc not next to binary
    total_found = 0

    ec_proc_counts = [0] * n
    ec_proc_first = [0] * n

    for sys_trial in range(10000):
        trans_fn = random_transition_fn(n, ms)
        cycles = find_good_cycles(n, ms, trans_fn, max_cycles=10)

        for configs, movers in cycles:
            W = total_displacement(movers, n)
            if abs(W) != n:
                continue

            # Non-uniform
            L = len(movers)
            dirs = []
            for i in range(L):
                diff = (movers[(i+1) % L] - movers[i]) % n
                if diff == 0: d = 0
                elif diff <= n // 2: d = 1
                else: d = -1
                dirs.append(d)
            non_stay = [d for d in dirs if d != 0]
            if not non_stay or all(d == non_stay[0] for d in non_stay):
                continue

            # All binary isolated with fc ≥ 2
            fc = fire_count(movers, n)
            all_iso = True
            for p in binary:
                if fc[p] < 2 or not has_isolated_firings(movers, p):
                    all_iso = False
                    break
            if not all_iso:
                continue

            total_found += 1

            # Find EC details
            ecs = find_ec_details(configs, movers, n, ms)

            if not ecs:
                print(f"  WARNING: No EC found! movers={movers[:20]}")
                continue

            # Classify first EC
            first_ec = ecs[0]
            p = first_ec['proc']
            ec_proc_first[p] += 1

            for ec in ecs:
                p = ec['proc']
                ec_proc_counts[p] += 1
                if ms[p] == 2:
                    ec_at_binary += 1
                else:
                    ec_at_ternary += 1
                    # Is p adjacent to a binary proc?
                    if ms[left(p, n)] == 2 or ms[right(p, n)] == 2:
                        ec_at_boundary += 1
                    else:
                        ec_at_interior += 1

    print(f"Total odd-winding non-uniform all-isolated cycles: {total_found}")
    print()
    print(f"EC at binary proc: {ec_at_binary}")
    print(f"EC at ternary proc: {ec_at_ternary}")
    print(f"  - boundary (next to binary): {ec_at_boundary}")
    print(f"  - interior: {ec_at_interior}")
    print()
    print("EC count per processor:")
    for p in range(n):
        print(f"  Proc {p} ({'B' if ms[p]==2 else 'T'}): {ec_proc_counts[p]} total, {ec_proc_first[p]} first")
    print()

    if total_found > 0:
        print(f"EC always exists: {total_found}/{total_found}")
        if ec_at_binary > 0:
            print("EC occurs AT binary procs — the gap-parity mechanism might work")
            print("even for non-consecutive (if the right condition is identified).")
        if ec_at_boundary > 0:
            print("EC occurs AT ternary-binary boundary procs.")
            print("This suggests the EC is related to the ternary proc's transition")
            print("being constrained by the binary neighbor's parity return.")

    # For the first few, print detailed info
    print()
    print("=== Detailed examples ===")
    detail_count = 0
    random.seed(42)
    for sys_trial in range(10000):
        trans_fn = random_transition_fn(n, ms)
        cycles = find_good_cycles(n, ms, trans_fn, max_cycles=10)

        for configs, movers in cycles:
            W = total_displacement(movers, n)
            if abs(W) != n:
                continue
            L = len(movers)
            dirs = []
            for i in range(L):
                diff = (movers[(i+1) % L] - movers[i]) % n
                if diff == 0: d = 0
                elif diff <= n // 2: d = 1
                else: d = -1
                dirs.append(d)
            non_stay = [d for d in dirs if d != 0]
            if not non_stay or all(d == non_stay[0] for d in non_stay):
                continue
            fc = fire_count(movers, n)
            all_iso = True
            for p in binary:
                if fc[p] < 2 or not has_isolated_firings(movers, p):
                    all_iso = False
                    break
            if not all_iso:
                continue

            ecs = find_ec_details(configs, movers, n, ms)

            detail_count += 1
            print(f"\nExample {detail_count}:")
            print(f"  movers = {movers}")
            print(f"  fc = {fc}")
            print(f"  W = {W}")
            print(f"  len = {len(movers)}")

            for ec in ecs[:3]:
                p = ec['proc']
                print(f"  EC at proc {p} ({'B' if ms[p]==2 else 'T'}): ctx={ec['ctx']}")
                print(f"    mover steps: {ec['mover_steps']}")
                print(f"    nonmover steps: {ec['nonmover_steps'][:5]}")

                # Check gap structure
                if ms[p] == 2:
                    # Binary proc: check if min-gap produces this EC
                    fire_steps = sorted(ec['mover_steps'])
                    if len(fire_steps) >= 2:
                        for fi in range(len(fire_steps)):
                            a = fire_steps[fi]
                            b = fire_steps[(fi+1) % len(fire_steps)]
                            if b > a:
                                gap = b - a
                            else:
                                gap = len(movers) - a + b
                            nms = ec['nonmover_steps']
                            in_gap = [s for s in nms if (a < s < b if b > a else (s > a or s < b))]
                            if in_gap:
                                print(f"    Gap a={a}→b={b}, size={gap}, nonmover in gap: {in_gap[:3]}")

            if detail_count >= 5:
                break
        if detail_count >= 5:
            break


if __name__ == "__main__":
    main()
