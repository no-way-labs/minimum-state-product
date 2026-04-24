#!/usr/bin/env python3
"""Extended check: does the normal form EVER occur?

Tests both:
1. Ternary sandwiched between binary (non-consecutive case)
2. Binary sandwiched between binary (consecutive case)
3. Various n values and configurations
"""
import random
from itertools import product as iprod

def random_transition(m_left, m_self, m_right):
    f = {}
    for L in range(m_left):
        for S in range(m_self):
            for R in range(m_right):
                f[(L, S, R)] = random.randint(0, m_self - 1)
    return f

def privileged(config, sys_f, ms, n, i):
    L = config[(i - 1) % n]
    S = config[i]
    R = config[(i + 1) % n]
    return sys_f[i][(L, S, R)] != S

def find_unique_privileged(config, sys_f, ms, n):
    privs = [i for i in range(n) if privileged(config, sys_f, ms, n, i)]
    if len(privs) == 1:
        return privs[0]
    return None

def apply_move(config, sys_f, ms, n, i):
    new_config = list(config)
    L = config[(i - 1) % n]
    S = config[i]
    R = config[(i + 1) % n]
    new_config[i] = sys_f[i][(L, S, R)]
    return tuple(new_config)

def find_good_cycle(sys_f, ms, n, max_steps=5000):
    config = tuple(random.randint(0, ms[i]-1) for i in range(n))
    visited = {}
    for step in range(max_steps):
        if config in visited:
            start = visited[config]
            cycle_configs = []
            c = config
            for _ in range(step - start):
                cycle_configs.append(c)
                p = find_unique_privileged(c, sys_f, ms, n)
                if p is None:
                    return None
                c = apply_move(c, sys_f, ms, n, p)
            for c in cycle_configs:
                if find_unique_privileged(c, sys_f, ms, n) is None:
                    return None
            return cycle_configs
        visited[config] = step
        p = find_unique_privileged(config, sys_f, ms, n)
        if p is None:
            return None
        config = apply_move(config, sys_f, ms, n, p)
    return None

def check_normal_form(J, K):
    if J % 2 == 0 and K % 2 == 0:
        return False
    if J >= 2 and K == 0:
        return False
    if J == 0 and K >= 2:
        return False
    return True

def analyze_all_sandwiched(cycle_configs, sys_f, ms, n):
    """Find ALL processors with both neighbors binary, check phases."""
    L = len(cycle_configs)
    movers = [find_unique_privileged(cycle_configs[k], sys_f, ms, n) for k in range(L)]

    normal_forms = []

    for t in range(n):
        lt = (t - 1) % n
        rt = (t + 1) % n
        if ms[lt] != 2 or ms[rt] != 2:
            continue  # Need both neighbors binary

        # Find fire steps for t
        fire_steps = [k for k in range(L) if movers[k] == t]
        if len(fire_steps) < 2:
            continue

        # Check each phase
        for idx in range(len(fire_steps)):
            s = fire_steps[idx]
            prev = fire_steps[(idx - 1) % len(fire_steps)]
            if prev < s:
                a = prev + 1
                ok = all(movers[k] != t for k in range(a, s))
                if ok and a < s:
                    J = sum(1 for k in range(a, s) if movers[k] == lt)
                    K = sum(1 for k in range(a, s) if movers[k] == rt)
                    if check_normal_form(J, K):
                        normal_forms.append({
                            't': t, 'm_t': ms[t], 'J': J, 'K': K,
                            'phase_len': s - a, 'a': a, 's': s
                        })
    return normal_forms

def main():
    random.seed(42)
    total_nf = 0
    total_cycles = 0

    configs = [
        # (n, ms_description, ms)
        (5, "2,3,2,3,3", [2, 3, 2, 3, 3]),
        (5, "2,2,2,3,4", [2, 2, 2, 3, 4]),  # M_5 = 96
        (5, "2,2,2,3,3", [2, 2, 2, 3, 3]),
        (7, "2,3,2,3,3,3,3", [2, 3, 2, 3, 3, 3, 3]),
        (7, "2,2,2,3,3,3,3", [2, 2, 2, 3, 3, 3, 3]),
        (9, "2,3,2,3,3,3,3,3,3", [2, 3, 2, 3, 3, 3, 3, 3, 3]),
        (9, "2,2,2,3,3,3,3,3,3", [2, 2, 2, 3, 3, 3, 3, 3, 3]),
        (9, "2,3,3,2,3,3,2,3,3", [2, 3, 3, 2, 3, 3, 2, 3, 3]),  # 3 binary spaced
        (9, "2,2,3,2,3,3,3,3,3", [2, 2, 3, 2, 3, 3, 3, 3, 3]),
    ]

    for n, desc, ms in configs:
        nf_count = 0
        cycle_count = 0
        for trial in range(20000):
            sys_f = {}
            for i in range(n):
                sys_f[i] = random_transition(ms[(i-1)%n], ms[i], ms[(i+1)%n])
            cycle = find_good_cycle(sys_f, ms, n)
            if cycle is None:
                continue
            cycle_count += 1
            nfs = analyze_all_sandwiched(cycle, sys_f, ms, n)
            if nfs:
                nf_count += len(nfs)
                for nf in nfs[:3]:
                    print(f"  NORMAL FORM at n={n} ms={desc}: t={nf['t']}(m={nf['m_t']}) "
                          f"J={nf['J']} K={nf['K']} phase_len={nf['phase_len']}")
        print(f"n={n} ms={desc}: {cycle_count} cycles, {nf_count} normal-form phases")
        total_nf += nf_count
        total_cycles += cycle_count

    print(f"\n=== TOTAL: {total_cycles} cycles, {total_nf} normal-form phases ===")

    if total_nf == 0:
        print("\nNORMAL FORM NEVER OCCURS!")
        print("palindromic_phase_ec is VACUOUSLY TRUE.")
        print("Proof strategy: show the hypothesis _hnormal is always False.")
        print("That is: for any sandwiched phase, one of BothEven/ToggleFR-L/ToggleFR-R fires.")

if __name__ == '__main__':
    main()
