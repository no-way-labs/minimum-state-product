#!/usr/bin/env python3
"""Investigate the 11% without J=K=0 phases.
What do they look like? Do they have hno_safe?"""
import random
from collections import defaultdict

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

def find_good_cycle(sys_f, ms, n, max_steps=5000):
    config = tuple(random.randint(0, ms[i]-1) for i in range(n))
    visited = {}
    for step in range(max_steps):
        if config in visited:
            start = visited[config]
            cycle = []
            c = config
            for _ in range(step - start):
                p = find_unique_privileged(c, sys_f, ms, n)
                if p is None: return None
                cycle.append((c, p))
                c = apply_move(c, sys_f, ms, n, p)
            for c2, _ in cycle:
                if find_unique_privileged(c2, sys_f, ms, n) is None:
                    return None
            return cycle
        visited[config] = step
        p = find_unique_privileged(config, sys_f, ms, n)
        if p is None: return None
        config = apply_move(config, sys_f, ms, n, p)
    return None

def check_hno_safe(movers, n):
    for q in range(n):
        if not any(m == q or m == (q-1)%n or m == (q+1)%n for m in movers):
            return False
    return True

def main():
    random.seed(777)

    no_jk0_examples = []

    for n, ms in [(5, [2,2,2,3,3]), (7, [2,2,2,3,3,3,3])]:
        for trial in range(200000):
            sys_f = {i: random_transition(ms[(i-1)%n], ms[i], ms[(i+1)%n]) for i in range(n)}
            cycle = find_good_cycle(sys_f, ms, n)
            if cycle is None:
                continue
            movers = [p for _, p in cycle]
            L = len(cycle)
            has_nosafe = check_hno_safe(movers, n)

            for t in range(n):
                lt, rt = (t-1)%n, (t+1)%n
                if ms[lt] != 2 or ms[rt] != 2:
                    continue

                fire_steps = [k for k in range(L) if movers[k] == t]
                F = len(fire_steps)
                if F < 2:
                    continue

                # Check all phases for J=K=0
                has_jk0 = False
                all_phases_mech = True
                phases_info = []
                for idx in range(F):
                    s = fire_steps[idx]
                    prev = fire_steps[(idx-1) % F]
                    if prev < s:
                        phase_movers = movers[prev+1:s]
                    else:
                        phase_movers = movers[prev+1:] + movers[:s]
                    J = sum(1 for m in phase_movers if m == lt)
                    K = sum(1 for m in phase_movers if m == rt)
                    if J == 0 and K == 0:
                        has_jk0 = True
                    both_even = (J%2==0) and (K%2==0)
                    toggle_l = J>=2 and K==0
                    toggle_r = J==0 and K>=2
                    mech = both_even or toggle_l or toggle_r
                    if not mech:
                        all_phases_mech = False
                    phases_info.append((J, K, len(phase_movers), mech))

                if not has_jk0 and len(no_jk0_examples) < 30:
                    no_jk0_examples.append({
                        'n': n, 'ms': ms, 't': t, 'F': F, 'L': L,
                        'hno_safe': has_nosafe,
                        'all_mech': all_phases_mech,
                        'phases': phases_info,
                        'distinct_movers': sorted(set(movers))
                    })

    print(f"Found {len(no_jk0_examples)} procs WITHOUT J=K=0 phase\n")
    for ex in no_jk0_examples[:20]:
        print(f"n={ex['n']} t={ex['t']} F={ex['F']} L={ex['L']} hno_safe={ex['hno_safe']} "
              f"all_mech={ex['all_mech']}")
        print(f"  movers: {ex['distinct_movers']}")
        print(f"  phases (J,K,len,mech): {ex['phases']}")
        print()

    # Key question: do ANY of the no-J=K=0 examples have hno_safe?
    with_nosafe = sum(1 for ex in no_jk0_examples if ex['hno_safe'])
    print(f"\nNo-J=K=0 examples WITH hno_safe: {with_nosafe}")
    print(f"No-J=K=0 examples WITHOUT hno_safe: {len(no_jk0_examples) - with_nosafe}")

    if with_nosafe == 0:
        print("\nCONFIRMED: hno_safe → ∃ phase with J=K=0!")
        print("Proof approach: derive ∃ phase with J=K=0 from hno_safe,")
        print("then use BothEven (phase_bothSilent_ec) on that phase.")

if __name__ == '__main__':
    main()
