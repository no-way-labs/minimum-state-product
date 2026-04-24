#!/usr/bin/env python3
"""
RA13: Analyze the S=all case (every proc fc≥3).

When every proc fires ≥3 times, the gradient argument doesn't apply.
But we still see 100% dispatchable. Why?

Hypothesis: Binary procs have fc ≥ 4 (even). With fc(b) = 4:
4 phases. Neighbor fires distributed over 4 phases.
If neighbor fires 3 times: 3 over 4 phases → some phase has 0 → dispatchable!

So: if any neighbor of a binary proc has fc = 3 (odd), pigeonhole at the binary proc.

When does this fail? When both neighbors of binary have fc ≥ 4.
Then: all surrounding procs fire ≥ 4. CL ≥ 4n.

But with fc(binary) = 4 and both neighbors fc = 4:
4 fires each over 4 phases. Could be (1,1,1,1) for both → all phases (1,1).
BUT: do ZW constraints force something else?

Let me check the S=all cases in detail.
"""

from itertools import product as iterproduct, permutations
from collections import defaultdict
import random

random.seed(42)


def classify_step(prev, curr, n):
    d = (curr - prev) % n
    if d == 1: return 'cw'
    elif d == n-1: return 'ccw'
    else: return 'other'


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


def find_zw_fc3_cycles(ms, all_c, adj, num=500000, maxs=80):
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


def main():
    print("=" * 70)
    print("RA13: S=all case analysis — WHY is it always dispatchable?")
    print("=" * 70)

    for n in [5, 7]:
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

        print(f"\nn={n}, threshold={threshold}")

        for ms_sorted in multisets:
            P = 1
            for m in ms_sorted: P *= m
            if P > 2000: continue

            seen = set(); pc = 0
            for perm in permutations(ms_sorted):
                if perm in seen: continue
                seen.add(perm); pc += 1
                if pc > 30: break
                ms = perm
                all_c, adj = build_adj(ms)
                cycles = find_zw_fc3_cycles(ms, all_c, adj, num=300000)

                for cyc in cycles:
                    fc = cyc['fc']
                    if not all(fc.get(q, 0) >= 3 for q in range(n)):
                        continue

                    # S = all procs case
                    movers = cyc['movers']; L = len(movers)

                    # For each proc, show fc and phases
                    print(f"\n  ms={ms}, CL={L}, fc=[{','.join(str(fc[q]) for q in range(n))}]")

                    # Key check: for each binary proc, does some neighbor have ODD fc?
                    for q in range(n):
                        if ms[q] != 2: continue
                        lq = (q-1)%n; rq = (q+1)%n
                        fl = fc.get(lq, 0); fr = fc.get(rq, 0)
                        # Binary fc is even (≥4). If neighbor fc is odd: pigeonhole.
                        # neighbor fires = odd, phases = even (fc_q). odd over even phases:
                        # Can't have all equal → some phase must differ → some phase has 0?
                        # No: odd over even can be (1,1,...,1,0,...,0) if total = even-1.
                        # Wait: fc(neighbor) = odd = 3, fc(q) = 4 phases.
                        # 3 over 4: at least 1 phase with 0 → dispatchable!
                        # This is just the standard pigeonhole: 3 < 4.

                        if fl < fc[q] or fr < fc[q]:
                            # Standard pigeonhole works
                            fire_pos = [i for i, m in enumerate(movers) if m == q]
                            phases = []
                            for pi in range(len(fire_pos)):
                                s = fire_pos[pi]; e = fire_pos[(pi+1)%len(fire_pos)]
                                J = K = 0; pos = (s+1)%L
                                while pos != e:
                                    if movers[pos] == lq: J += 1
                                    if movers[pos] == rq: K += 1
                                    pos = (pos+1)%L
                                phases.append((J, K))

                            has_zero = any(J == 0 or K == 0 for J, K in phases)
                            print(f"    q={q}(binary,fc={fc[q]}): L_fc={fl}, R_fc={fr}, "
                                  f"phases={phases}, has_zero={has_zero}")
                            if has_zero:
                                print(f"    -> DISPATCHABLE by pigeonhole")
                            break

                    # Also show: does some ternary proc have neighbor with lower fc?
                    for q in range(n):
                        if ms[q] == 2: continue
                        lq = (q-1)%n; rq = (q+1)%n
                        fl = fc.get(lq, 0); fr = fc.get(rq, 0)
                        if fl < fc[q] or fr < fc[q]:
                            fire_pos = [i for i, m in enumerate(movers) if m == q]
                            phases = []
                            for pi in range(len(fire_pos)):
                                s = fire_pos[pi]; e = fire_pos[(pi+1)%len(fire_pos)]
                                J = K = 0; pos = (s+1)%L
                                while pos != e:
                                    if movers[pos] == lq: J += 1
                                    if movers[pos] == rq: K += 1
                                    pos = (pos+1)%L
                                phases.append((J, K))
                            has_zero = any(J == 0 or K == 0 for J, K in phases)
                            if has_zero:
                                print(f"    q={q}(ternary,fc={fc[q]}): L_fc={fl}, R_fc={fr}, "
                                      f"phases={phases}")
                                print(f"    -> DISPATCHABLE by gradient")
                                break

    # COMPREHENSIVE: check if pigeonhole (fc(neighbor) < fc(q)) ALWAYS works
    # at SOME proc when S = all
    print("\n" + "=" * 60)
    print("COMPREHENSIVE: pigeonhole at SOME proc for S=all case")
    print("=" * 60)

    for n in [5, 7]:
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

        total_sall = 0
        pigeonhole_at_some = 0
        no_pigeonhole = 0  # ALL procs have fc(left) ≥ fc(q) AND fc(right) ≥ fc(q)
        no_pigeonhole_details = []

        for ms_sorted in multisets:
            P = 1
            for m in ms_sorted: P *= m
            if P > 2000: continue
            seen = set(); pc = 0
            for perm in permutations(ms_sorted):
                if perm in seen: continue
                seen.add(perm); pc += 1
                if pc > 30: break
                ms = perm
                all_c, adj = build_adj(ms)
                cycles = find_zw_fc3_cycles(ms, all_c, adj, num=300000)
                for cyc in cycles:
                    fc = cyc['fc']
                    if not all(fc.get(q, 0) >= 3 for q in range(n)):
                        continue
                    total_sall += 1

                    # Check: does SOME proc q have a neighbor with fc < fc(q)?
                    found = False
                    for q in range(n):
                        lq = (q-1)%n; rq = (q+1)%n
                        if fc.get(lq, 0) < fc[q] or fc.get(rq, 0) < fc[q]:
                            found = True; break
                    if found:
                        pigeonhole_at_some += 1
                    else:
                        no_pigeonhole += 1
                        if len(no_pigeonhole_details) < 5:
                            no_pigeonhole_details.append({
                                'ms': ms,
                                'fc': [fc[q] for q in range(n)],
                                'length': cyc['length'],
                            })

        print(f"\nn={n}: {total_sall} S=all cycles")
        print(f"  Pigeonhole at some proc: {pigeonhole_at_some}")
        print(f"  No pigeonhole (all fc equal?): {no_pigeonhole}")
        if no_pigeonhole_details:
            for d in no_pigeonhole_details:
                print(f"    ms={d['ms']}, fc={d['fc']}, CL={d['length']}")
        else:
            print(f"  -> Pigeonhole ALWAYS works at some proc!")


if __name__ == '__main__':
    main()
