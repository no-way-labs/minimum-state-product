#!/usr/bin/env python3
"""
Find the EXACT entry conflict witness for palindromic_phase_ec.

Setup: proc t with binary left and right neighbors.
Phase [a, s): t doesn't fire in [a,s), fires at s.
Normal form: J (left fires) and K (right fires) satisfy
  ¬(BothEven ∨ ToggleFR-L ∨ ToggleFR-R)

Find: proc p, steps k₁ (moverAt=p) and k₂ (moverAt≠p), with same (L,S,R) at p.

From the Python palindromic proof: the witness is at a proc ADJACENT to t,
specifically t+1 (= right(t)). The CW non-mover step (when t fires CW)
matches the CCW mover step (when right(t) fires CCW).

But wait — in the "normal form" case, t fires at step s. This is ONE fire.
The phase gives one fire. For the palindromic argument: need TWO fires of t
(CW and CCW). The phase only gives one.

So the witness might use DIFFERENT procs/steps. Let me search exhaustively.
"""

from itertools import product as cprod
import random

def left(i, n): return (i - 1) % n
def right(i, n): return (i + 1) % n

def find_all_ecs(cycle, priv, n):
    """Find ALL entry conflicts in the cycle."""
    ecs = []
    for p in range(n):
        lp, rp = left(p, n), right(p, n)
        mover_ctxs = {}  # ctx → list of steps
        nonmover_ctxs = {}
        for k, c in enumerate(cycle):
            ctx = (c[lp], c[p], c[rp])
            if priv[c] == p:
                mover_ctxs.setdefault(ctx, []).append(k)
            else:
                nonmover_ctxs.setdefault(ctx, []).append(k)
        for ctx in set(mover_ctxs) & set(nonmover_ctxs):
            ecs.append((p, ctx, mover_ctxs[ctx][0], nonmover_ctxs[ctx][0]))
    return ecs

def main():
    n = 9
    # Try various configurations with sandwiched ternary
    # t = 4 (ternary), left(4) = 3 (binary), right(4) = 5 (binary)
    # binary = {3, 5, ...}
    configs_tested = 0
    normal_phases = 0
    ecs_found = 0
    ec_procs = {}

    for binary_set in [[3, 5, 7], [0, 3, 6], [1, 3, 5], [0, 2, 5], [1, 4, 7]]:
        m = [3] * n
        for b in binary_set:
            m[b] = 2

        # Find sandwiched ternary
        sandwiched = []
        for t in range(n):
            if m[t] >= 3 and m[left(t, n)] == 2 and m[right(t, n)] == 2:
                sandwiched.append(t)

        if not sandwiched:
            continue

        for seed in range(5000):
            random.seed(seed + hash(tuple(binary_set)))
            f = {}
            for proc in range(n):
                f[proc] = {}
                for L in range(m[left(proc, n)]):
                    for S in range(m[proc]):
                        for R in range(m[right(proc, n)]):
                            f[proc][(L, S, R)] = random.randint(0, m[proc] - 1)

            all_configs = list(cprod(*[range(m[j]) for j in range(n)]))
            priv = {}
            for c in all_configs:
                privs = [j for j in range(n)
                         if f[j][(c[left(j, n)], c[j], c[right(j, n)])] != c[j]]
                if len(privs) == 1:
                    priv[c] = privs[0]

            visited = set()
            for start in priv:
                if start in visited:
                    continue
                path = [start]
                vis = {start}
                c = start
                found = False
                for _ in range(50000):
                    p = priv[c]
                    cl = list(c)
                    cl[p] = f[p][(c[left(p, n)], c[p], c[right(p, n)])]
                    cn = tuple(cl)
                    if cn == start:
                        found = True
                        break
                    if cn not in priv or cn in vis:
                        break
                    path.append(cn)
                    vis.add(cn)
                    c = cn

                if not found or len(path) < 6:
                    continue
                visited.update(path)
                configs_tested += 1

                L_cycle = len(path)

                for t in sandwiched:
                    # Find firing steps of t
                    fire_steps = [k for k in range(L_cycle) if priv[path[k]] == t]
                    if len(fire_steps) < 2:
                        continue

                    # For each consecutive pair of fires: check phase
                    for idx in range(len(fire_steps)):
                        s = fire_steps[idx]
                        a = (fire_steps[idx - 1] + 1) % L_cycle
                        if a >= s:  # wrap-around, skip for simplicity
                            continue

                        lt, rt = left(t, n), right(t, n)
                        J = sum(1 for k in range(a, s) if priv[path[k]] == lt)
                        K = sum(1 for k in range(a, s) if priv[path[k]] == rt)

                        # Check normal form
                        is_normal = True
                        if J % 2 == 0 and K % 2 == 0:
                            is_normal = False
                        if J >= 2 and K == 0:
                            is_normal = False
                        if J == 0 and K >= 2:
                            is_normal = False

                        if not is_normal:
                            continue
                        normal_phases += 1

                        # Find entry conflicts
                        ecs = find_all_ecs(path, priv, n)
                        if ecs:
                            ecs_found += 1
                            for p, ctx, k1, k2 in ecs[:1]:
                                # Which proc has the EC?
                                rel = "t" if p == t else \
                                      "left(t)" if p == lt else \
                                      "right(t)" if p == rt else \
                                      f"other({p})"
                                ec_procs[rel] = ec_procs.get(rel, 0) + 1
                        else:
                            print(f"NO EC! binary={binary_set} t={t} seed={seed}")
                            print(f"  Phase [{a},{s}): J={J} K={K}")
                            print(f"  Cycle len={L_cycle}")

    print(f"\nConfigs tested: {configs_tested}")
    print(f"Normal-form phases: {normal_phases}")
    print(f"EC found: {ecs_found}")
    print(f"EC procs: {ec_procs}")
    if normal_phases > 0 and ecs_found == normal_phases:
        print("→ EC ALWAYS found when normal-form phase exists!")
    print(f"No EC: {normal_phases - ecs_found}")

if __name__ == "__main__":
    main()
