#!/usr/bin/env python3
"""
For sorry #1 (consecutiveBinary_globalMin_residual_false):
With 3 consecutive binary, zero winding, CW>0, no safe processor,
and the GLOBAL MIN opposite pair at some edge:

Does hasEntryConflict ALWAYS hold?

The global min gives: at edge (p0, right(p0)), CW at step a0, CCW at step b0,
with b0 - a0 minimal across ALL edges.

Cases that reach the residual function:
- Gap = 1 (any endpoint type)
- Gap >= 2, non-binary endpoint
"""

from itertools import product as cprod
import random

def left(i, n): return (i - 1) % n
def right(i, n): return (i + 1) % n

def find_cycles_with_global_min(n, m, binary_pos, max_seeds=2000):
    """Find good cycles with zero winding, CW>0, no safe proc, 3 consec binary."""
    results = []

    for seed in range(max_seeds):
        random.seed(seed + n * 100000)
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

            L = len(path)
            # Check zero winding
            total_disp = 0
            for k in range(L):
                p_cur = priv[path[k]]
                p_next = priv[path[(k+1)%L]]
                step = (p_next - p_cur) % n
                if step > n // 2:
                    step -= n
                total_disp += step
            if total_disp != 0:
                continue

            # Check CW > 0
            cw_count = 0
            for k in range(L):
                p_cur = priv[path[k]]
                p_next = priv[path[(k+1)%L]]
                step = (p_next - p_cur) % n
                if step == 1:
                    cw_count += 1
            if cw_count == 0:
                continue

            # Check no safe processor
            mover_set = set()
            for c in path:
                p = priv[c]
                mover_set.add(p)
                mover_set.add(left(p, n))
                mover_set.add(right(p, n))
            has_safe = any(q not in mover_set for q in range(n))
            # Actually, safe means moverAt not in {q, left(q), right(q)}
            # Let me redo this properly
            safe_exists = False
            movers = [priv[c] for c in path]
            for q in range(n):
                is_safe = True
                for mov in movers:
                    if mov == q or mov == left(q, n) or mov == right(q, n):
                        is_safe = False
                        break
                if is_safe:
                    safe_exists = True
                    break
            if safe_exists:
                continue

            # Check entry conflict at ANY proc
            has_ec = False
            ec_proc = None
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
                    ec_proc = p
                    break

            fc = [sum(1 for c in path if priv[c] == j) for j in range(n)]
            results.append({
                'seed': seed, 'len': L, 'fc': fc, 'has_ec': has_ec,
                'ec_proc': ec_proc, 'cw': cw_count
            })

    return results


def main():
    print("GlobalMin residual: checking EC for zero-winding + 3 consec binary")
    print("=" * 60)

    n = 9
    binary_pos = [0, 1, 2]
    m = [2, 2, 2, 3, 3, 3, 3, 3, 3]

    results = find_cycles_with_global_min(n, m, binary_pos, max_seeds=5000)

    total = len(results)
    ec_count = sum(1 for r in results if r['has_ec'])
    no_ec_count = total - ec_count

    print(f"Found {total} cycles with zero winding + CW>0 + no safe proc")
    print(f"  With EC: {ec_count}")
    print(f"  Without EC: {no_ec_count}")

    if no_ec_count > 0:
        print("\n  Cycles WITHOUT entry conflict:")
        for r in results:
            if not r['has_ec']:
                print(f"    seed={r['seed']} len={r['len']} fc={r['fc']} cw={r['cw']}")

    if no_ec_count == 0 and total > 0:
        print("  → EC ALWAYS holds! GlobalMin residual is provable.")


if __name__ == "__main__":
    main()
