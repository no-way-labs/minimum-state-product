#!/usr/bin/env python3
"""For cycles WITH hno_safe: find the phase containing a non-neighbor mover.
Does the mechanism fire in THAT specific phase?"""
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

def main():
    random.seed(999)

    # Generate systems that DO have hno_safe
    # Use larger moduli to increase chance
    configs = [
        (5, [2,2,2,3,3]),
        (5, [2,2,2,3,4]),
        (5, [2,3,2,3,3]),
        (5, [3,2,3,2,3]),  # non-adjacent binary
        (7, [2,2,2,3,3,3,3]),
        (7, [2,3,3,2,3,3,3]),
    ]

    total_with_nosafe = 0
    mech_in_nn_phase = 0
    no_mech_in_nn_phase = 0

    for n, ms in configs:
        for trial in range(500000):
            sys_f = {i: random_transition(ms[(i-1)%n], ms[i], ms[(i+1)%n]) for i in range(n)}

            config = tuple(random.randint(0, ms[i]-1) for i in range(n))
            visited = {}
            cycle = None
            for step in range(3000):
                if config in visited:
                    start = visited[config]
                    cyc = []
                    c = config
                    ok = True
                    for _ in range(step - start):
                        p = find_unique_privileged(c, sys_f, ms, n)
                        if p is None: ok = False; break
                        cyc.append(p)
                        c = apply_move(c, sys_f, ms, n, p)
                    if ok and cyc:
                        cycle = cyc
                    break
                visited[config] = step
                p = find_unique_privileged(config, sys_f, ms, n)
                if p is None: break
                config = apply_move(config, sys_f, ms, n, p)

            if cycle is None:
                continue

            movers = cycle
            L = len(movers)

            # Check hno_safe
            safe = False
            for q in range(n):
                if not any(m == q or m == (q-1)%n or m == (q+1)%n for m in movers):
                    safe = True; break
            if safe:
                continue

            total_with_nosafe += 1

            # For each proc with both binary neighbors
            for t in range(n):
                lt, rt = (t-1)%n, (t+1)%n
                if ms[lt] != 2 or ms[rt] != 2:
                    continue

                fire_steps = [k for k in range(L) if movers[k] == t]
                F = len(fire_steps)
                if F < 2:
                    continue

                # Find non-neighbor step
                nn_steps = [k for k in range(L) if movers[k] != t and movers[k] != lt and movers[k] != rt]
                if not nn_steps:
                    continue

                # For each non-neighbor step: find its phase
                for nn_k in nn_steps:
                    # Find the phase containing nn_k
                    # Phase = gap between consecutive t-fires containing nn_k
                    # Find the t-fire BEFORE nn_k and AFTER nn_k
                    prev_t = max((s for s in fire_steps if s < nn_k), default=None)
                    next_t = min((s for s in fire_steps if s > nn_k), default=None)

                    if prev_t is None or next_t is None:
                        # Wrap-around case, skip for simplicity
                        continue

                    # Phase is (prev_t, next_t)
                    phase_movers = movers[prev_t+1:next_t]
                    J = sum(1 for m in phase_movers if m == lt)
                    K = sum(1 for m in phase_movers if m == rt)
                    plen = len(phase_movers)

                    both_even = (J%2==0) and (K%2==0)
                    toggle_l = J>=2 and K==0
                    toggle_r = J==0 and K>=2
                    mech = both_even or toggle_l or toggle_r

                    if mech:
                        mech_in_nn_phase += 1
                    else:
                        no_mech_in_nn_phase += 1
                        if no_mech_in_nn_phase <= 5:
                            print(f"  Non-neighbor phase WITHOUT mechanism!")
                            print(f"    n={n} t={t} J={J} K={K} plen={plen}")
                            print(f"    phase_movers={phase_movers}")
                            print(f"    nn_step={nn_k} mover={movers[nn_k]}")

                    break  # One non-neighbor per proc is enough

        print(f"n={n} ms={ms}: checked")

    print(f"\nTotal cycles with hno_safe: {total_with_nosafe}")
    print(f"Non-neighbor phases WITH mechanism: {mech_in_nn_phase}")
    print(f"Non-neighbor phases WITHOUT mechanism: {no_mech_in_nn_phase}")

    if no_mech_in_nn_phase == 0 and mech_in_nn_phase > 0:
        print("\nCONFIRMED: The phase containing a non-neighbor ALWAYS has mechanism!")
        print("This might be because the non-neighbor step forces J=K=0 or even J,K.")
    elif mech_in_nn_phase + no_mech_in_nn_phase == 0:
        print("\nNo cycles with hno_safe found. Need different test configs.")
    else:
        print(f"\n{no_mech_in_nn_phase} failures found. The approach needs refinement.")

if __name__ == '__main__':
    main()
