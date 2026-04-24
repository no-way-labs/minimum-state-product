#!/usr/bin/env python3
"""Critical test: does one of {BothEven, ToggleFR-L, ToggleFR-R} ALWAYS fire
for phase_len >= 2? And are ALL normal-form phases at phase_len = 1?

If yes: palindromic_phase_ec only needs to handle phase_len=1.
For n >= 9 + hno_safe: if phase_len=1 can't happen, the sorry is vacuous.
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

def check_normal_form(J, K):
    if J % 2 == 0 and K % 2 == 0: return False  # BothEven
    if J >= 2 and K == 0: return False  # ToggleFR-L
    if J == 0 and K >= 2: return False  # ToggleFR-R
    return True

def main():
    random.seed(789)

    # Focus on finding ANY normal-form phase with phase_len >= 2
    nf_plen1 = 0
    nf_plen2plus = 0
    total_phases = 0

    configs = [
        (5, [2,2,2,3,3]),
        (5, [2,2,2,3,4]),
        (5, [2,3,2,3,3]),
        (7, [2,2,2,3,3,3,3]),
        (7, [2,3,2,3,3,3,3]),
        (9, [2,2,2,3,3,3,3,3,3]),
        (9, [2,3,2,3,3,3,3,3,3]),
    ]

    for n, ms in configs:
        local_nf1 = 0
        local_nf2 = 0
        local_total = 0
        cycles_found = 0

        for trial in range(200000 if n <= 7 else 100000):
            sys_f = {}
            for i in range(n):
                sys_f[i] = random_transition(ms[(i-1)%n], ms[i], ms[(i+1)%n])

            config = tuple(random.randint(0, ms[i]-1) for i in range(n))
            visited = {}
            for step in range(3000):
                if config in visited:
                    start = visited[config]
                    cycle = []
                    c = config
                    valid = True
                    for _ in range(step - start):
                        p = find_unique_privileged(c, sys_f, ms, n)
                        if p is None: valid = False; break
                        cycle.append(p)
                        c = apply_move(c, sys_f, ms, n, p)
                    if not valid or not cycle: break

                    cycles_found += 1
                    L = len(cycle)
                    movers = cycle

                    for t in range(n):
                        lt, rt = (t-1)%n, (t+1)%n
                        if ms[lt] != 2 or ms[rt] != 2: continue

                        fires = [k for k in range(L) if movers[k] == t]
                        if len(fires) < 2: continue

                        for idx in range(len(fires)):
                            s = fires[idx]
                            prev = fires[(idx-1) % len(fires)]
                            if prev < s:
                                a = prev + 1
                                if all(movers[k] != t for k in range(a, s)) and a < s:
                                    plen = s - a
                                    J = sum(1 for k in range(a, s) if movers[k] == lt)
                                    K = sum(1 for k in range(a, s) if movers[k] == rt)
                                    local_total += 1
                                    if check_normal_form(J, K):
                                        if plen == 1:
                                            local_nf1 += 1
                                        else:
                                            local_nf2 += 1
                                            print(f"  *** NF at plen={plen}! n={n} t={t}(m={ms[t]}) J={J} K={K}")
                    break
                visited[config] = step
                p = find_unique_privileged(config, sys_f, ms, n)
                if p is None: break
                config = apply_move(config, sys_f, ms, n, p)

        print(f"n={n} ms={ms}: {cycles_found} cycles, {local_total} phases, "
              f"NF@plen=1: {local_nf1}, NF@plen>=2: {local_nf2}")
        nf_plen1 += local_nf1
        nf_plen2plus += local_nf2
        total_phases += local_total

    print(f"\n=== TOTAL: {total_phases} phases, NF@plen=1: {nf_plen1}, NF@plen>=2: {nf_plen2plus} ===")
    if nf_plen2plus == 0:
        print("\nCONFIRMED: Normal form ONLY at phase_len=1!")
        print("Strategy: prove phase_len >= 2 under n>=9 hypotheses.")

if __name__ == '__main__':
    main()
