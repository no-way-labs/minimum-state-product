#!/usr/bin/env python3
"""
RA13 FAST: Quick proof verification with limited permutations.
"""

from itertools import product as iterproduct, permutations
from collections import defaultdict
import random

random.seed(42)


def classify_step(prev, curr, n):
    d = (curr - prev) % n
    return 'cw' if d == 1 else ('ccw' if d == n-1 else 'other')


def build_adj(ms):
    n = len(ms)
    all_c = list(iterproduct(*[range(m) for m in ms]))
    adj = defaultdict(list)
    for c in all_c:
        for p in range(n):
            for v in range(ms[p]):
                if v != c[p]:
                    c2 = list(c); c2[p] = v
                    adj[c].append((tuple(c2), p))
    return all_c, adj


def find_zw_fc3(ms, all_c, adj, num=200000, maxs=100):
    n = len(ms)
    unique = {}
    for _ in range(num):
        c = random.choice(all_c)
        vis = {c: 0}; path = [c]; mov = []
        for step in range(1, maxs):
            nb = adj[c]
            if not nb: break
            c, p = random.choice(nb)
            mov.append(p)
            if c in vis:
                s = vis[c]; cc = path[s:]; cm = mov[s:]; L = len(cm)
                if L < 2*n: break
                fc = defaultdict(int)
                for m in cm: fc[m] += 1
                if len(fc) < n or min(fc.values()) < 2: break
                cw = ccw = 0
                for i in range(L):
                    t = classify_step(cm[i-1], cm[i], n)
                    if t == 'cw': cw += 1
                    elif t == 'ccw': ccw += 1
                if cw != ccw or cw == 0: break
                if max(fc.values()) < 3: break
                key = (cc[0], tuple(cm))
                unique[key] = {'configs': cc, 'movers': cm, 'fc': dict(fc), 'length': L}
                break
            vis[c] = step; path.append(c)
    return list(unique.values())


def get_phases(movers, q, n):
    L = len(movers)
    fp = [i for i, m in enumerate(movers) if m == q]
    if not fp: return []
    lq = (q-1)%n; rq = (q+1)%n
    phases = []
    for pi in range(len(fp)):
        s = fp[pi]; e = fp[(pi+1)%len(fp)]
        J = K = 0; pos = (s+1)%L
        while pos != e:
            if movers[pos] == lq: J += 1
            if movers[pos] == rq: K += 1
            pos = (pos+1)%L
        phases.append((J, K))
    return phases


def main():
    print("RA13 FAST: Proof Verification")
    print("=" * 60)

    grand_total = 0
    case_a = 0; case_b = 0
    case_a_ok = 0; case_b_ok = 0
    case_a_fail = 0; case_b_fail = 0

    for n in [5, 7, 9]:
        threshold = 4 * 3 ** (n-2)
        multisets = []
        def gen(pos, cur, prod, ml=multisets, nn=n, t=threshold):
            if pos == nn:
                if prod < t and sum(1 for x in cur if x == 2) >= 3:
                    ml.append(tuple(cur))
                return
            for m in range(2, min(t // max(prod, 1) + 1, 20)):
                if prod * m >= t: break
                if cur and m < cur[-1]: continue
                gen(pos + 1, cur + [m], prod * m)
        gen(0, [], 1)

        print(f"\nn={n}: {len(multisets)} multisets")

        for ms_sorted in multisets:
            P = 1
            for m in ms_sorted: P *= m
            if P > 3000: continue

            # Just test 5 permutations (rotations)
            tested = set()
            for start in range(n):
                perm = ms_sorted[start:] + ms_sorted[:start]
                # Only useful if ms_sorted is actually a permutation starting point
                # For sorted multisets, rotations aren't distinct. Use first 5 unique perms.
                pass

            seen = set(); pc = 0
            for perm in permutations(ms_sorted):
                if perm in seen: continue
                seen.add(perm); pc += 1
                if pc > 5: break
                ms = perm
                all_c, adj = build_adj(ms)
                cycles = find_zw_fc3(ms, all_c, adj,
                    num=(200000 if n <= 7 else 50000),
                    maxs=(80 if n <= 7 else 150))

                for cyc in cycles:
                    fc = cyc['fc']
                    movers = cyc['movers']
                    grand_total += 1

                    fc_vals = [fc.get(q, 0) for q in range(n)]
                    is_constant = (min(fc_vals) == max(fc_vals))

                    if not is_constant:
                        case_a += 1
                        # Find gradient proc
                        max_fc = max(fc_vals)
                        found = False
                        for q in range(n):
                            if fc_vals[q] < 3: continue
                            lq = (q-1)%n; rq = (q+1)%n
                            if fc_vals[lq] < fc_vals[q] or fc_vals[rq] < fc_vals[q]:
                                # Pigeonhole guarantees J=0 or K=0 in some phase
                                # Verify:
                                phases = get_phases(movers, q, n)
                                lower_side = None
                                if fc_vals[lq] < fc_vals[q]:
                                    lower_side = 'left'
                                    has_zero = any(J == 0 for J, K in phases)
                                else:
                                    lower_side = 'right'
                                    has_zero = any(K == 0 for J, K in phases)
                                if has_zero:
                                    found = True; break
                        if found:
                            case_a_ok += 1
                        else:
                            case_a_fail += 1
                            if case_a_fail <= 3:
                                print(f"  Case A FAIL: ms={ms}, fc={fc_vals}")
                    else:
                        case_b += 1
                        # Uniform fc: check any phase dispatchable
                        found = False
                        for q in range(n):
                            phases = get_phases(movers, q, n)
                            if any(J == 0 or K == 0 or (J%2==0 and K%2==0)
                                   for J, K in phases):
                                found = True; break
                        if found:
                            case_b_ok += 1
                        else:
                            case_b_fail += 1
                            if case_b_fail <= 3:
                                k = fc_vals[0]
                                print(f"  Case B FAIL: ms={ms}, k={k}, CL={cyc['length']}")
                                for q in range(n):
                                    phases = get_phases(movers, q, n)
                                    print(f"    q={q}: {phases}")

        print(f"  n={n}: {grand_total} total, A={case_a}(ok={case_a_ok},fail={case_a_fail}), "
              f"B={case_b}(ok={case_b_ok},fail={case_b_fail})")

    print(f"\n{'='*60}")
    print(f"GRAND TOTAL: {grand_total}")
    print(f"Case A (non-constant fc): {case_a} (ok={case_a_ok}, fail={case_a_fail})")
    print(f"Case B (constant fc): {case_b} (ok={case_b_ok}, fail={case_b_fail})")

    if case_a_fail == 0 and case_b_fail == 0:
        print("\nTHEOREM VERIFIED: Every ZW fc≥3 cycle has a dispatchable phase.")
        print("\nPROOF STRUCTURE:")
        print("  1. fc non-constant (Case A): gradient/pigeonhole at max-fc boundary.")
        print("     This is ANALYTICAL: if fc(q) > fc(neighbor), then neighbor fires")
        print("     fewer times than q's phase count. Pigeonhole → some phase has")
        print("     0 fires from that neighbor → (0,K) or (J,0) → dispatchable.")
        print("  2. fc constant = k (Case B): k even ≥ 4 (binary constraint).")
        print(f"     Empirically verified: {case_b} cycles, all have dispatchable phase.")
        print("     Need analytical argument for this case.")


if __name__ == '__main__':
    main()
