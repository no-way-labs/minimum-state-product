#!/usr/bin/env python3
"""
For the "all normal form" case with 3 consecutive binary {0,1,2}:
- ri=1 fires exactly 2 times (binary, fc=2)
- Both phases have (J odd, K odd) where J=fires of i=0, K=fires of rri=2
- Isolated: between ri's fires, at least one other proc fires
- Outside mover: some step fires proc ∉ {0,1,2}

Find the entry conflict witness: which processor p has the same (L,S,R)
at both a mover step and a non-mover step?

From the analysis: after J₁ (odd) fires of i and K₁ (odd) fires of rri
in phase 1, the context at ri = (1-A, 1-B, 1-C) which matches the fire 2
context. If the step right before fire 2 fires an outside proc (not i, ri, rri):
the context at ri doesn't change → entry conflict!

If the step before fire 2 fires i or rri: context changes → no immediate EC.
But if there's an outside fire SOMEWHERE in the phase that happens AFTER all
i and rri fires: the context at ri is (1-A, 1-B, 1-C) and ri is non-mover.
EC with fire 2!

So: does the cycle structure guarantee an outside fire AFTER all i/rri fires
in at least one phase?
"""

from itertools import product as cprod
import random

def left(i, n): return (i - 1) % n
def right(i, n): return (i + 1) % n

def main():
    n = 9
    m = [2, 2, 2, 3, 3, 3, 3, 3, 3]
    ri = 1

    # Generate cycles and check the "all normal" case
    total = 0
    normal_count = 0
    ec_at_ri_via_outside = 0
    ec_other = 0
    no_ec = 0

    for seed in range(20000):
        random.seed(seed)
        f = {}
        for proc in range(n):
            f[proc] = {}
            for L in range(m[left(proc,n)]):
                for S in range(m[proc]):
                    for R in range(m[right(proc,n)]):
                        f[proc][(L,S,R)] = random.randint(0, m[proc]-1)

        all_configs = list(cprod(*[range(m[j]) for j in range(n)]))
        priv = {}
        for c in all_configs:
            privs = [j for j in range(n) if f[j][(c[left(j,n)], c[j], c[right(j,n)])] != c[j]]
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
                cl[p] = f[p][(c[left(p,n)], c[p], c[right(p,n)])]
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
            total += 1

            # Check fc(ri) = 2, isolated, outside mover
            fire_steps = [k for k in range(len(path)) if priv[path[k]] == ri]
            if len(fire_steps) != 2:
                continue
            # Isolated check
            L = len(path)
            isolated = all(priv[path[(fs+1)%L]] != ri for fs in fire_steps)
            if not isolated:
                continue
            # Outside check
            has_outside = any(priv[c] not in {0, 1, 2} for c in path)
            if not has_outside:
                continue

            # Check phases
            s1, s2 = fire_steps
            # Phase 1: steps s1+1, ..., s2-1 (between fire 1 and fire 2)
            phase1_steps = [(s1 + 1 + k) % L for k in range(((s2 - s1 - 1) % L))]
            J1 = sum(1 for k in phase1_steps if priv[path[k]] == 0)
            K1 = sum(1 for k in phase1_steps if priv[path[k]] == 2)

            # Both phases normal form?
            J2 = sum(1 for k in range(L) if priv[path[k]] == 0) - J1
            K2 = sum(1 for k in range(L) if priv[path[k]] == 2) - K1

            all_normal = True
            for J, K in [(J1, K1), (J2, K2)]:
                if J % 2 == 0 and K % 2 == 0:
                    all_normal = False
                if J >= 2 and K == 0:
                    all_normal = False
                if J == 0 and K >= 2:
                    all_normal = False

            if not all_normal:
                continue
            normal_count += 1

            # Check: is there an entry conflict?
            has_ec = False
            for p in range(n):
                lp, rp = left(p, n), right(p, n)
                mover_ctx = set()
                nonmover_ctx = set()
                for c in path:
                    ctx = (c[lp], c[p], c[rp])
                    if priv[c] == p:
                        mover_ctx.add(ctx)
                    else:
                        nonmover_ctx.add(ctx)
                if mover_ctx & nonmover_ctx:
                    has_ec = True
                    # Which proc?
                    if p == ri:
                        ec_at_ri_via_outside += 1
                    else:
                        ec_other += 1
                    break
            if not has_ec:
                no_ec += 1
                print(f"NO EC! seed={seed}")

    print(f"\nTotal cycles: {total}")
    print(f"All-normal with fc=2 + isolated + outside: {normal_count}")
    print(f"  EC at ri: {ec_at_ri_via_outside}")
    print(f"  EC other: {ec_other}")
    print(f"  No EC: {no_ec}")

if __name__ == "__main__":
    main()
