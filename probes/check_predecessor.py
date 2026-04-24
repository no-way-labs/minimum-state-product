#!/usr/bin/env python3
"""For cycles WITHOUT hno_safe (since we can't find any WITH):
How often is a t-fire preceded by a non-neighbor?
And: what's the structure when ALL predecessors are neighbors?"""
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
    random.seed(42)

    all_pred_neighbor = 0
    some_pred_nonneighbor = 0
    total = 0

    for n, ms in [(5, [2,2,2,3,3]), (5, [2,3,2,3,3]), (7, [2,2,2,3,3,3,3])]:
        for trial in range(200000):
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
                            if len(fires) < 2:
                                continue
                            total += 1

                            # Check predecessors
                            has_nn_pred = False
                            for s in fires:
                                prev = (s - 1) % L
                                if movers[prev] != lt and movers[prev] != rt and movers[prev] != t:
                                    has_nn_pred = True
                                    break

                            if has_nn_pred:
                                some_pred_nonneighbor += 1
                            else:
                                all_pred_neighbor += 1
                    break
                visited[config] = step
                p = find_unique_privileged(config, sys_f, ms, n)
                if p is None: break
                config = apply_move(config, sys_f, ms, n, p)

    print(f"Total procs analyzed: {total}")
    print(f"ALL predecessors are neighbors: {all_pred_neighbor} ({all_pred_neighbor*100//max(total,1)}%)")
    print(f"SOME predecessor is non-neighbor: {some_pred_nonneighbor} ({some_pred_nonneighbor*100//max(total,1)}%)")
    print()
    if all_pred_neighbor > 0:
        print("When ALL predecessors are neighbors:")
        print("  The cycle pattern is: ..., neighbor, t, neighbor, t, ...")
        print("  Only t and its neighbors fire.")
        print("  hno_safe would require non-neighbor movers elsewhere.")
        print("  But we're testing WITHOUT hno_safe, so this can happen.")
        print()
        print("With hno_safe: ALL-predecessor-neighbor implies only {t,lt,rt} fire")
        print("near t-fires. Non-neighbor fires are in phase INTERIORS, not at s-1.")
        print("This means the 'direct EC from non-neighbor predecessor' approach FAILS.")
        print()
        print("ALTERNATIVE: Instead of finding EC at t, find EC at the")
        print("NON-NEIGHBOR proc p. At step k where p fires: p is mover.")
        print("At some OTHER step where p doesn't fire: p is nonmover.")
        print("If context at p matches: EC at p!")

if __name__ == '__main__':
    main()
