#!/usr/bin/env python3
"""
Find entry conflict witnesses for the allNormalForm_false residue cases.

For n=9, ms=(2,2,2,3,3,3,3,3,3), pivot t=1 (binary neighbors at 0,2):
Enumerate ALL valid good cycles where:
- Every processor fires (full support)
- fireCount(t) >= 2
- All phases of t are normal form
Check: does every such cycle have entry conflict?
If yes: which processor and which steps?
"""

from itertools import product as cprod

def left(i, n): return (i - 1) % n
def right(i, n): return (i + 1) % n

def find_entry_conflict(path, priv, n):
    """Find entry conflict: same (L,S,R) at mover and non-mover step."""
    L = len(path)
    for p in range(n):
        lp, rp = left(p, n), right(p, n)
        mover_ctxs = {}  # ctx -> step
        for k in range(L):
            c = path[k]
            ctx = (c[lp], c[p], c[rp])
            if priv[c] == p:
                mover_ctxs[ctx] = k
        for k in range(L):
            c = path[k]
            ctx = (c[lp], c[p], c[rp])
            if priv[c] != p and ctx in mover_ctxs:
                return (p, mover_ctxs[ctx], k)
    return None

def main():
    n = 9
    m = [2, 2, 2, 3, 3, 3, 3, 3, 3]
    t = 1  # pivot: left(t)=0 (binary), right(t)=2 (binary)

    # Enumerate ALL transition functions for the 3 key processors
    # Actually, enumerate ALL valid good cycles by BFS from all configs
    all_configs = list(cprod(*[range(m[j]) for j in range(n)]))
    print(f"Total configs: {len(all_configs)}")

    # For each transition function assignment, find good cycles
    # This is too expensive for full enumeration. Instead:
    # enumerate by trying many random transition functions and checking thoroughly.
    import random

    total_cycles = 0
    normal_cycles = 0
    ec_count = 0
    no_ec_count = 0

    for seed in range(100000):
        random.seed(seed)
        f = {}
        for proc in range(n):
            f[proc] = {}
            for L in range(m[left(proc,n)]):
                for S in range(m[proc]):
                    for R in range(m[right(proc,n)]):
                        vals = list(range(m[proc]))
                        vals.remove(S)
                        f[proc][(L,S,R)] = random.choice(vals) if vals else S

        # Find privileged configs
        priv = {}
        for c in all_configs:
            privs = [j for j in range(n) if f[j][(c[left(j,n)], c[j], c[right(j,n)])] != c[j]]
            if len(privs) == 1:
                priv[c] = privs[0]

        # Find all good cycles by BFS
        visited_global = set()
        for start in priv:
            if start in visited_global:
                continue
            path = [start]
            vis = {start}
            c = start
            found = False
            for _ in range(200):
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

            if not found or len(path) < 4:
                continue
            visited_global.update(path)

            L = len(path)

            # Check full support
            fc = [0] * n
            for c in path:
                fc[priv[c]] += 1
            if any(fc[j] == 0 for j in range(n)):
                continue

            # Check fc(t) >= 2
            if fc[t] < 2:
                continue

            total_cycles += 1

            # Find t-firing steps
            t_fires = [k for k in range(L) if priv[path[k]] == t]

            # Check all phases normal form
            all_normal = True
            for idx in range(len(t_fires)):
                s = t_fires[idx]
                s_next = t_fires[(idx + 1) % len(t_fires)]
                # Phase: steps from s+1 to s_next (mod L)
                phase_steps = []
                k = (s + 1) % L
                while k != s_next:
                    phase_steps.append(k)
                    k = (k + 1) % L
                J = sum(1 for k in phase_steps if priv[path[k]] == left(t, n))
                K = sum(1 for k in phase_steps if priv[path[k]] == right(t, n))
                # Normal form: NOT mechanism-triggering
                if J % 2 == 0 and K % 2 == 0:
                    all_normal = False; break
                if J >= 2 and K == 0:
                    all_normal = False; break
                if J == 0 and K >= 2:
                    all_normal = False; break

            if not all_normal:
                continue

            normal_cycles += 1

            # Check for outside mover (mover not in {t-1, t, t+1})
            has_outside = any(priv[c] not in {left(t,n), t, right(t,n)} for c in path)
            if not has_outside:
                continue

            # Find entry conflict
            ec = find_entry_conflict(path, priv, n)
            if ec:
                ec_count += 1
            else:
                no_ec_count += 1
                # Print details for analysis
                print(f"\n=== NO EC at seed={seed} ===")
                print(f"Cycle length: {L}")
                print(f"Fire counts: {fc}")
                print(f"Mover word: {[priv[c] for c in path]}")
                print(f"t-fires at: {t_fires}")
                for idx in range(len(t_fires)):
                    s = t_fires[idx]
                    s_next = t_fires[(idx + 1) % len(t_fires)]
                    phase_steps = []
                    k = (s + 1) % L
                    while k != s_next:
                        phase_steps.append(k)
                        k = (k + 1) % L
                    J = sum(1 for k in phase_steps if priv[path[k]] == left(t,n))
                    K = sum(1 for k in phase_steps if priv[path[k]] == right(t,n))
                    print(f"  Phase {idx}: [{s}→{s_next}], J={J}, K={K}")

            if normal_cycles % 100 == 0 and normal_cycles > 0:
                print(f"  ... {normal_cycles} normal cycles checked, {no_ec_count} no-EC")

    print(f"\nTotal full-support fc≥2 cycles: {total_cycles}")
    print(f"All-normal + outside: {normal_cycles}")
    print(f"  With EC: {ec_count}")
    print(f"  No EC: {no_ec_count}")

if __name__ == "__main__":
    main()
