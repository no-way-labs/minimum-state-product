#!/usr/bin/env python3
"""
Check: in REAL good cycles with fc ≥ 2 for ALL processors,
does any sandwiched ternary have ALL phases in normal form?
"""
import sys
from itertools import product as cprod

def left(i, n): return (i - 1) % n
def right(i, n): return (i + 1) % n

def find_good_cycles_with_fc2(m, n, max_seeds=500):
    """Find good cycles where every processor fires ≥ 2 times."""
    import random
    results = []

    for seed in range(max_seeds):
        random.seed(seed + n * 10000)
        # Random transition table
        f = {}
        for i in range(n):
            f[i] = {}
            for L in range(m[left(i,n)]):
                for S in range(m[i]):
                    for R in range(m[right(i,n)]):
                        f[i][(L,S,R)] = random.randint(0, m[i]-1)

        # Find single-privileged configs
        all_configs = list(cprod(*[range(m[i]) for i in range(n)]))
        priv = {}
        for c in all_configs:
            privs = []
            for i in range(n):
                L, S, R = c[left(i,n)], c[i], c[right(i,n)]
                if f[i][(L,S,R)] != S:
                    privs.append(i)
            if len(privs) == 1:
                priv[c] = privs[0]

        # Find cycles
        visited_global = set()
        for start in priv:
            if start in visited_global:
                continue
            path = [start]
            visited = {start}
            c = start
            found = False
            for _ in range(10000):
                p = priv[c]
                c_list = list(c)
                c_list[p] = f[p][(c[left(p,n)], c[p], c[right(p,n)])]
                c_next = tuple(c_list)
                if c_next == start:
                    found = True
                    break
                if c_next not in priv or c_next in visited:
                    break
                path.append(c_next)
                visited.add(c_next)
                c = c_next

            if not found:
                continue
            visited_global.update(path)

            # Check fc ≥ 2 for all
            fc = [0] * n
            for c in path:
                fc[priv[c]] += 1
            if all(x >= 2 for x in fc):
                results.append((path, priv, fc, seed))

    return results


def check_phases(cycle, priv, t, n):
    """Check if all phases of sandwiched ternary t are normal form."""
    fire_steps = [k for k in range(len(cycle)) if priv[cycle[k]] == t]
    if len(fire_steps) < 2:
        return True, "fc<2", []

    lt, rt = left(t, n), right(t, n)
    L = len(cycle)
    phases = []
    for idx, s in enumerate(fire_steps):
        a = (fire_steps[idx-1] + 1) % L if idx > 0 else (fire_steps[-1] + 1) % L
        J, K = 0, 0
        k = a
        while k != s:
            mover = priv[cycle[k]]
            if mover == lt: J += 1
            if mover == rt: K += 1
            k = (k + 1) % L
        phases.append((J, K))

    for J, K in phases:
        if J % 2 == 0 and K % 2 == 0: return True, "BothEven", phases
        if J >= 2 and K == 0: return True, "ToggleFR-L", phases
        if J == 0 and K >= 2: return True, "ToggleFR-R", phases

    return False, "ALL_NORMAL", phases


def main():
    print("Real cycle check: all-normal with fc≥2 for all procs")
    print("=" * 60)

    for n in [5, 7, 9]:
        # Binary placements: ≥3, no 3 consecutive
        binary_placements = []
        for bits in range(1 << n):
            positions = [i for i in range(n) if bits & (1 << i)]
            if len(positions) < 3: continue
            has_3c = any((p+1)%n in positions and (p+2)%n in positions for p in positions)
            if has_3c: continue
            binary_placements.append(positions)

        total_cycles = 0
        total_checks = 0
        all_normal_count = 0

        for bp in binary_placements[:3]:
            m = [3]*n
            for p in bp: m[p] = 2

            # Find sandwiched ternary
            sandwiched = [t for t in range(n) if m[t]==3 and m[left(t,n)]==2 and m[right(t,n)]==2]
            if not sandwiched: continue

            cycles = find_good_cycles_with_fc2(m, n, max_seeds=1000)
            total_cycles += len(cycles)

            for cycle, priv, fc, seed in cycles:
                for t in sandwiched:
                    total_checks += 1
                    ok, reason, phases = check_phases(cycle, priv, t, n)
                    if not ok:
                        all_normal_count += 1
                        print(f"  ALL NORMAL: n={n} bp={bp} t={t} fc={fc} phases={phases} seed={seed}")

        print(f"n={n}: {total_cycles} fc≥2 cycles, {total_checks} checks, {all_normal_count} all-normal")

    print("\nDone.")

if __name__ == "__main__":
    main()
