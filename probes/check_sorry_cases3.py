#!/usr/bin/env python3
"""Check normal form with hno_safe filter, focused on n>=9."""
import random

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
    return privs[0] if len(privs) == 1 else None

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
            for c2 in cycle_configs:
                if find_unique_privileged(c2, sys_f, ms, n) is None:
                    return None
            return cycle_configs
        visited[config] = step
        p = find_unique_privileged(config, sys_f, ms, n)
        if p is None:
            return None
        config = apply_move(config, sys_f, ms, n, p)
    return None

def check_hno_safe(cycle_configs, sys_f, ms, n):
    """Check ¬hno_safe: no processor q such that mover never visits {q, left(q), right(q)}."""
    L = len(cycle_configs)
    movers = [find_unique_privileged(cycle_configs[k], sys_f, ms, n) for k in range(L)]
    for q in range(n):
        # Check if mover visits q's neighborhood
        visited = False
        for m in movers:
            if m == q or m == (q-1)%n or m == (q+1)%n:
                visited = True
                break
        if not visited:
            return False  # q is safe → hno_safe is True → ¬hno_safe is False
    return True  # No safe proc → ¬hno_safe holds

def check_normal_form(J, K):
    if J % 2 == 0 and K % 2 == 0:
        return False
    if J >= 2 and K == 0:
        return False
    if J == 0 and K >= 2:
        return False
    return True

def main():
    random.seed(123)

    configs_to_test = [
        (5, [2, 2, 2, 3, 3]),
        (5, [2, 2, 2, 3, 4]),
        (5, [2, 3, 2, 3, 3]),
        (7, [2, 2, 2, 3, 3, 3, 3]),
        (7, [2, 3, 2, 3, 3, 3, 3]),
        (9, [2, 2, 2, 3, 3, 3, 3, 3, 3]),
        (9, [2, 3, 2, 3, 3, 3, 3, 3, 3]),
        (9, [2, 3, 3, 2, 3, 3, 2, 3, 3]),
        (9, [2, 2, 3, 2, 3, 3, 3, 3, 3]),
        (11, [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3]),
        (11, [2, 3, 2, 3, 3, 3, 3, 3, 3, 3, 3]),
    ]

    for n, ms in configs_to_test:
        nf_total = 0
        nf_with_nosafe = 0
        cycles_found = 0
        cycles_with_nosafe = 0

        num_trials = 100000 if n <= 7 else 50000

        for trial in range(num_trials):
            sys_f = {}
            for i in range(n):
                sys_f[i] = random_transition(ms[(i-1)%n], ms[i], ms[(i+1)%n])

            cycle = find_good_cycle(sys_f, ms, n)
            if cycle is None:
                continue
            cycles_found += 1

            has_nosafe = check_hno_safe(cycle, sys_f, ms, n)
            if has_nosafe:
                cycles_with_nosafe += 1

            L = len(cycle)
            movers = [find_unique_privileged(cycle[k], sys_f, ms, n) for k in range(L)]

            for t in range(n):
                lt = (t - 1) % n
                rt = (t + 1) % n
                if ms[lt] != 2 or ms[rt] != 2:
                    continue

                fire_steps = [k for k in range(L) if movers[k] == t]
                if len(fire_steps) < 2:
                    continue

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
                                nf_total += 1
                                if has_nosafe:
                                    nf_with_nosafe += 1
                                    print(f"  NF+nosafe! n={n} ms={ms} t={t}(m={ms[t]}) "
                                          f"J={J} K={K} plen={s-a}")

        print(f"n={n} ms={ms}: {cycles_found} cycles ({cycles_with_nosafe} w/ nosafe), "
              f"NF: {nf_total} total, {nf_with_nosafe} with nosafe")

if __name__ == '__main__':
    main()
