#!/usr/bin/env python3
"""
For sorry #3 (consecutive_binary_isolated_false_noSafe_outsideMover):
With 3 consecutive binary {i, ri, rri}, ri has isolated firings (fc≥2,
never fires twice in a row), mover goes outside the triple, no safe proc.

Does hasEntryConflict ALWAYS hold?

Entry conflict at proc p: same (L,S,R) at a mover step and non-mover step.

For binary ri: (L,S,R) ∈ {0,1}³ = 8 contexts.
At ri's mover steps: (L,S,R) is "privileged" → f(ri, L, S, R) ≠ S.
At ri's non-mover steps: (L,S,R) is "non-privileged" → f(ri, L, S, R) = S.

Entry conflict = some context is BOTH privileged and non-privileged.
This requires the SAME (L,S,R) to appear at both a mover and non-mover step.

With isolated firings: between consecutive fires of ri, at least one other
proc fires. This changes L (if i fires) or R (if rri fires) or neither
(if an outside proc fires).

KEY QUESTION: with isolated firings + outside mover, does the (L,S,R) context
at ri necessarily repeat across mover/non-mover steps?
"""

from itertools import product as cprod

def left(i, n): return (i - 1) % n
def right(i, n): return (i + 1) % n

def check_entry_conflict_at_proc(cycle, priv, p, n):
    """Check if proc p has an entry conflict in the cycle."""
    lp = left(p, n)
    rp = right(p, n)

    mover_contexts = set()
    nonmover_contexts = set()

    for k, c in enumerate(cycle):
        ctx = (c[lp], c[p], c[rp])
        if priv[c] == p:
            mover_contexts.add(ctx)
        else:
            nonmover_contexts.add(ctx)

    overlap = mover_contexts & nonmover_contexts
    return len(overlap) > 0, mover_contexts, nonmover_contexts

def check_isolated_property(cycle, priv, p, n):
    """Check if proc p's firings are isolated (never fires twice in a row)."""
    L = len(cycle)
    for k in range(L):
        if priv[cycle[k]] == p and priv[cycle[(k+1) % L]] == p:
            return False
    return True

def check_outside_mover(cycle, priv, i, n):
    """Check if some mover is outside {i, ri, rri}."""
    ri = right(i, n)
    rri = right(ri, n)
    triple = {i, ri, rri}
    for c in cycle:
        if priv[c] not in triple:
            return True
    return False

def main():
    import random
    print("Checking entry conflict for isolated binary with outside mover")
    print("=" * 60)

    n = 9
    # 3 consecutive binary at i=0: binary={0,1,2}, ternary={3,...,8}
    i_pos = 0
    ri = 1
    rri = 2
    m = [2, 2, 2, 3, 3, 3, 3, 3, 3]

    total_cycles = 0
    total_isolated_outside = 0
    total_ec = 0
    total_no_ec = 0

    for seed in range(5000):
        random.seed(seed)
        # Random transition table
        f = {}
        for proc in range(n):
            f[proc] = {}
            for L in range(m[left(proc, n)]):
                for S in range(m[proc]):
                    for R in range(m[right(proc, n)]):
                        f[proc][(L, S, R)] = random.randint(0, m[proc] - 1)

        # Find cycles
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

            if not found or len(path) < 4:
                continue
            visited.update(path)
            total_cycles += 1

            # Check: fc(ri) ≥ 2
            fc_ri = sum(1 for c in path if priv[c] == ri)
            if fc_ri < 2:
                continue

            # Check isolated
            if not check_isolated_property(path, priv, ri, n):
                continue

            # Check outside mover
            if not check_outside_mover(path, priv, i_pos, n):
                continue

            total_isolated_outside += 1

            # Check entry conflict at ANY proc
            has_ec = False
            for p in range(n):
                ec, _, _ = check_entry_conflict_at_proc(path, priv, p, n)
                if ec:
                    has_ec = True
                    break

            if has_ec:
                total_ec += 1
            else:
                total_no_ec += 1
                # Print details
                fc = [sum(1 for c in path if priv[c] == j) for j in range(n)]
                print(f"  NO EC! seed={seed} len={len(path)} fc={fc}")

    print(f"\nTotal: {total_cycles} cycles, {total_isolated_outside} with isolated+outside")
    print(f"  EC: {total_ec}, No EC: {total_no_ec}")
    if total_no_ec == 0 and total_isolated_outside > 0:
        print("  → EC ALWAYS holds! Theorem is correct.")
    elif total_no_ec > 0:
        print("  → Found cycles WITHOUT EC. Theorem might need stronger hypotheses.")

if __name__ == "__main__":
    main()
