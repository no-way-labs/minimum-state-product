#!/usr/bin/env python3
"""Derisk Approach A:
Step 1: Does non-zero winding EVER occur for sub-threshold + ≥3 binary + convergence?
Step 2: For zero-winding cycles, does a safe proc ALWAYS exist?

If both hold across all tested configs: Approach A is viable.
"""
import random

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

def total_displacement(movers, n):
    td = 0
    for i in range(len(movers)):
        curr = movers[i]
        nxt = movers[(i+1) % len(movers)]
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

def zero_set_size(movers, n):
    fc = [0] * n
    for m in movers:
        fc[m] += 1
    return sum(1 for f in fc if f == 0)

def find_good_cycle(sys_f, ms, n, config, max_steps=3000):
    """Find good cycle from a starting config. Returns (movers, configs) or None."""
    visited = {}
    c = config
    for step in range(max_steps):
        if c in visited:
            start = visited[c]
            cycle_movers = []
            cycle_configs = []
            cc = c
            ok = True
            for _ in range(step - start):
                p = find_unique_privileged(cc, sys_f, ms, n)
                if p is None: ok = False; break
                cycle_movers.append(p)
                cycle_configs.append(cc)
                cc = apply_move(cc, sys_f, ms, n, p)
            if ok and cycle_movers:
                return cycle_movers, cycle_configs
            return None
        visited[c] = step
        p = find_unique_privileged(c, sys_f, ms, n)
        if p is None: return None
        c = apply_move(c, sys_f, ms, n, p)
    return None

def check_convergence(sys_f, ms, n, good_cycle_configs, sample_size=200):
    """Sample random configs and check they reach the good cycle."""
    gc_set = set(good_cycle_configs)
    for _ in range(sample_size):
        c = tuple(random.randint(0, ms[i]-1) for i in range(n))
        for step in range(5000):
            if c in gc_set:
                break
            p = find_unique_privileged(c, sys_f, ms, n)
            if p is None:
                return False  # dead config
            c = apply_move(c, sys_f, ms, n, p)
        else:
            return False  # didn't reach cycle
    return True

def main():
    random.seed(42)

    # Comprehensive set of sub-threshold multisets with ≥3 binary
    test_configs = [
        # Consecutive binary
        (5, [2,2,2,3,3]),       # prod 72 < 108
        (5, [2,2,2,3,4]),       # prod 96 < 108
        (7, [2,2,2,3,3,3,3]),   # prod 648 < 972
        (9, [2,2,2,3,3,3,3,3,3]),  # prod 5832 < 8748
        # Non-consecutive binary
        (7, [2,3,2,3,2,3,3]),   # prod 648 < 972
        (7, [2,3,3,2,3,2,3]),   # prod 648
        (9, [2,3,2,3,2,3,3,3,3]),  # prod 5832 < 8748
        (9, [2,3,3,2,3,3,2,3,3]),  # prod 5832
        (9, [2,3,3,3,2,3,3,2,3]),  # prod 5832
        # Mixed (quaternary)
        (5, [2,2,2,4,3]),       # prod 96
        (7, [2,2,2,4,3,3,3]),   # prod 864 < 972
        (9, [2,2,2,4,3,3,3,3,3]),  # prod 7776 < 8748
        # 4+ binary
        (7, [2,2,2,2,3,3,3]),   # prod 432 < 972
        (9, [2,2,2,2,3,3,3,3,3]),  # prod 3888 < 8748
        # Large n
        (11, [2,2,2,3,3,3,3,3,3,3,3]), # prod 52488 < 78732
        (13, [2,2,2,3,3,3,3,3,3,3,3,3,3]), # prod 472392 < 708588
    ]

    print("="*80)
    print("APPROACH A DERISK: Zero winding + safe proc for sub-threshold + ≥3 binary")
    print("="*80)

    all_zero_winding = True
    all_safe_proc = True
    all_z_ge3 = True
    total_all = 0

    for n, ms in test_configs:
        product_val = 1
        for m in ms: product_val *= m
        threshold = 4 * (3 ** (n - 2))
        num_bin = sum(1 for m in ms if m == 2)
        is_sub = product_val < threshold

        if not is_sub or num_bin < 3:
            continue

        num_trials = 500000 if n <= 7 else (100000 if n <= 9 else 20000)

        total = 0
        nonzero_wind = 0
        zero_wind = 0
        safe_count = 0
        nosafe_count = 0
        z_lt3 = 0
        max_firing = 0
        converging_nonzero = 0

        nonzero_examples = []

        for trial in range(num_trials):
            sys_f = {i: random_transition(ms[(i-1)%n], ms[i], ms[(i+1)%n]) for i in range(n)}
            config = tuple(random.randint(0, ms[i]-1) for i in range(n))

            result = find_good_cycle(sys_f, ms, n, config)
            if result is None:
                continue

            movers, configs = result
            total += 1

            td = total_displacement(movers, n)
            zs = zero_set_size(movers, n)
            safe = has_safe_proc(movers, n)

            fc = [0] * n
            for m in movers:
                fc[m] += 1
            k = sum(1 for f in fc if f > 0)
            max_firing = max(max_firing, k)

            if td != 0:
                nonzero_wind += 1
                # Check if this is a converging system
                if len(nonzero_examples) < 5:
                    conv = check_convergence(sys_f, ms, n, configs, sample_size=500)
                    if conv:
                        converging_nonzero += 1
                        nonzero_examples.append({
                            'td': td, 'movers': movers, 'fc': fc, 'k': k,
                            'zs': zs, 'safe': safe
                        })
            else:
                zero_wind += 1

            if safe:
                safe_count += 1
            else:
                nosafe_count += 1

            if zs < 3:
                z_lt3 += 1

        total_all += total

        print(f"\nn={n} ms={ms} prod={product_val} bin={num_bin}")
        print(f"  Cycles found: {total}")
        print(f"  STEP 1 - Winding: zero={zero_wind} nonzero={nonzero_wind}")
        if nonzero_wind > 0:
            print(f"    *** NON-ZERO WINDING FOUND! converging={converging_nonzero} ***")
            all_zero_winding = False
            for ex in nonzero_examples:
                print(f"    td={ex['td']} k={ex['k']} zs={ex['zs']} safe={ex['safe']}")
                print(f"    movers={ex['movers'][:15]}...")
        print(f"  STEP 2 - Safe proc: yes={safe_count} no={nosafe_count}")
        if nosafe_count > 0:
            all_safe_proc = False
            print(f"    *** NO SAFE PROC FOUND! ***")
        print(f"  |Z| < 3: {z_lt3} (max firing procs: {max_firing})")
        if z_lt3 > 0:
            all_z_ge3 = False
            print(f"    *** |Z| < 3 FOUND! ***")

    print("\n" + "="*80)
    print("VERDICT")
    print("="*80)
    print(f"Total cycles tested: {total_all}")
    print(f"Step 1 (zero winding always):  {'PASS' if all_zero_winding else 'FAIL'}")
    print(f"Step 2 (safe proc always):     {'PASS' if all_safe_proc else 'FAIL'}")
    print(f"|Z| ≥ 3 always:               {'PASS' if all_z_ge3 else 'FAIL'}")
    print()
    if all_zero_winding and all_safe_proc:
        print("Approach A is VIABLE.")
        print("Need to prove:")
        print("  (1) sub-threshold + ≥3 binary + convergence → zero winding")
        print("  (2) zero winding + sub-threshold + ≥3 binary + convergence → safe proc exists")
    elif all_z_ge3:
        print("|Z| ≥ 3 always holds. Can prove directly without decomposing into A1+A2.")
    else:
        print("Approach A has failures. Need different strategy.")


if __name__ == '__main__':
    main()
