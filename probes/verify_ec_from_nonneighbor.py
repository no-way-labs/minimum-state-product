#!/usr/bin/env python3
"""Verify: for every good cycle with both-binary-neighbor pivot t,
if SOME phase has a non-neighbor mover, does EC always exist?

The argument: non-neighbor mover at step k doesn't change t's context.
If J_rem (left fires between k and some t-fire) is even AND
K_rem (right fires between k and some t-fire) is even: EC at t.

We check: is there ALWAYS a (non-neighbor step k, t-fire step s) pair
with BothEven in the interval?"""

import random
from itertools import product as iterproduct

def make_system(ms, n):
    sys_f = {}
    for i in range(n):
        sys_f[i] = {}
        for L in range(ms[(i-1)%n]):
            for S in range(ms[i]):
                for R in range(ms[(i+1)%n]):
                    sys_f[i][(L,S,R)] = random.randint(0, ms[i]-1)
    return sys_f

def find_cycle(sys_f, ms, n, max_steps=5000):
    config = tuple(random.randint(0, ms[i]-1) for i in range(n))
    visited = {}
    for step in range(max_steps):
        if config in visited:
            start = visited[config]
            movers = []
            configs_list = []
            c = config
            for _ in range(step - start):
                privs = [i for i in range(n) if sys_f[i][(c[(i-1)%n], c[i], c[(i+1)%n])] != c[i]]
                if len(privs) != 1: return None, None
                movers.append(privs[0])
                configs_list.append(c)
                nc = list(c)
                p = privs[0]
                nc[p] = sys_f[p][(c[(p-1)%n], c[p], c[(p+1)%n])]
                c = tuple(nc)
            return configs_list, movers
        visited[config] = step
        privs = [i for i in range(n) if sys_f[i][(config[(i-1)%n], config[i], config[(i+1)%n])] != config[i]]
        if len(privs) != 1: return None, None
        p = privs[0]
        nc = list(config)
        nc[p] = sys_f[p][(config[(p-1)%n], config[p], config[(p+1)%n])]
        config = tuple(nc)
    return None, None

def context_at(configs, k, t, n):
    """Context at proc t at step k: (left_val, self_val, right_val)."""
    c = configs[k]
    return (c[(t-1)%n], c[t], c[(t+1)%n])

def main():
    random.seed(42)
    n = 9
    ms = [2,2,2,3,3,3,3,3,3]  # 3 consecutive binary

    found_ec = 0
    found_noec = 0
    total = 0

    for trial in range(500000):
        sys_f = make_system(ms, n)
        configs, movers = find_cycle(sys_f, ms, n)
        if configs is None: continue

        L = len(movers)

        # Find procs with both binary neighbors
        for t in range(n):
            lt = (t-1) % n
            rt = (t+1) % n
            if ms[lt] != 2 or ms[rt] != 2: continue

            # Check if t fires
            fc_t = sum(1 for m in movers if m == t)
            if fc_t < 2: continue

            # Find non-neighbor movers
            non_neighbor_steps = [k for k in range(L)
                                  if movers[k] != t and movers[k] != lt and movers[k] != rt]

            if not non_neighbor_steps: continue
            total += 1

            # For each non-neighbor step k, check EC with each t-fire step s
            has_ec = False
            t_fire_steps = [s for s in range(L) if movers[s] == t]

            for k in non_neighbor_steps:
                ctx_k = context_at(configs, k, t, n)
                for s in t_fire_steps:
                    ctx_s = context_at(configs, s, t, n)
                    if ctx_k == ctx_s:
                        has_ec = True
                        break
                if has_ec: break

            if has_ec:
                found_ec += 1
            else:
                found_noec += 1
                if found_noec <= 3:
                    print(f"NO EC! trial={trial} t={t} L={L} movers={movers}")
                    print(f"  non-neighbor steps: {non_neighbor_steps}")
                    print(f"  t-fire steps: {t_fire_steps}")
                    for k in non_neighbor_steps:
                        ctx_k = context_at(configs, k, t, n)
                        print(f"  ctx at step {k} (mover={movers[k]}): {ctx_k}")
                    for s in t_fire_steps:
                        ctx_s = context_at(configs, s, t, n)
                        print(f"  ctx at step {s} (t fires): {ctx_s}")

    print(f"\nTotal with non-neighbor movers: {total}")
    print(f"EC found: {found_ec}")
    print(f"No EC: {found_noec}")

main()
