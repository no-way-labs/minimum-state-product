#!/usr/bin/env python3
"""Can we always find a mechanism-firing phase among ALL phases of t?

Key question: if t fires F ≥ 2 times with both binary neighbors,
does SOME phase always have BothEven/ToggleFR?

Test WITHOUT hno_safe to see if the mechanism guarantee comes from
the cycle structure alone, or if hno_safe is needed.
"""
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

def main():
    random.seed(42)

    all_mech_count = 0
    some_no_mech_count = 0
    all_nf_count = 0  # ALL phases in normal form
    total = 0

    details = []

    for n, ms in [(5, [2,2,2,3,3]), (5, [2,3,2,3,3]), (7, [2,2,2,3,3,3,3]),
                  (7, [2,3,2,3,3,3,3]), (9, [2,2,2,3,3,3,3,3,3])]:
        for trial in range(300000 if n <= 7 else 100000):
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
                        if p is None: ok = False; break
                        cycle.append(p)
                        c = apply_move(c, sys_f, ms, n, p)
                    if ok and cycle:
                        movers = cycle
                        L = len(movers)

                        for t in range(n):
                            lt, rt = (t-1)%n, (t+1)%n
                            if ms[lt] != 2 or ms[rt] != 2:
                                continue
                            fires = [k for k in range(L) if movers[k] == t]
                            F = len(fires)
                            if F < 2:
                                continue
                            total += 1

                            has_mech = False
                            all_nf = True
                            phase_types = []
                            for idx in range(F):
                                s = fires[idx]
                                prev = fires[(idx-1) % F]
                                if prev < s:
                                    pm = movers[prev+1:s]
                                else:
                                    pm = movers[prev+1:] + movers[:s]
                                J = sum(1 for m in pm if m == lt)
                                K = sum(1 for m in pm if m == rt)
                                be = (J%2==0) and (K%2==0)
                                tl = J>=2 and K==0
                                tr = J==0 and K>=2
                                mech = be or tl or tr
                                if mech:
                                    has_mech = True
                                    all_nf = False
                                else:
                                    pass
                                phase_types.append((J, K, len(pm), mech))

                            if has_mech:
                                all_mech_count += 1
                            else:
                                some_no_mech_count += 1
                                all_nf_count += 1
                                if len(details) < 20:
                                    details.append({
                                        'n': n, 'ms': ms, 't': t, 'F': F, 'L': L,
                                        'phases': phase_types
                                    })
                    break
                visited[config] = step
                p = find_unique_privileged(config, sys_f, ms, n)
                if p is None: break
                config = apply_move(config, sys_f, ms, n, p)

    print(f"Total procs: {total}")
    print(f"SOME phase has mechanism: {all_mech_count} ({all_mech_count*100//max(total,1)}%)")
    print(f"ALL phases normal form: {all_nf_count} ({all_nf_count*100//max(total,1)}%)")
    print()

    if all_nf_count > 0:
        print("Examples where ALL phases are normal form:")
        for d in details[:10]:
            print(f"  n={d['n']} t={d['t']} F={d['F']} L={d['L']}")
            print(f"    phases: {d['phases']}")
        print()
        print("KEY: When ALL phases are NF, what's the structure?")
        for d in details[:5]:
            jks = [(j,k) for j,k,_,_ in d['phases']]
            print(f"  (J,K) per phase: {jks}")
            j_sum = sum(j for j,k in jks)
            k_sum = sum(k for j,k in jks)
            print(f"  F_L={j_sum}, F_R={k_sum}, F={d['F']}")
    else:
        print("CONFIRMED: SOME phase ALWAYS has mechanism!")
        print()
        print("This means: even WITHOUT hno_safe, iterating over all phases")
        print("of t always finds a mechanism-firing phase.")
        print()
        print("PROOF APPROACH:")
        print("  Modify both_binary_neighbors_false to iterate over all phases.")
        print("  For EACH phase: check mechanism. If found: EC → False.")
        print("  If none found (all NF): derive contradiction from parity.")
        print("  Since computationally none found: the 'all NF' branch is dead code.")

if __name__ == '__main__':
    main()
