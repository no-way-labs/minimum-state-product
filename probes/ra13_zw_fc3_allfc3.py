#!/usr/bin/env python3
"""
RA13: Check if S = all procs (every proc fc≥3) ever occurs in ZW cycles.
If not, the gradient/boundary argument closes everything.

Also: for the S ≠ all procs case, verify the gradient argument:
1. S has a boundary (since S is proper subset of {0,...,n-1})
2. At boundary: t ∈ S, u ∉ S, u is neighbor of t
3. fc(t) ≥ 3, fc(u) = 2 (since u ∉ S and fc(u) ≥ 2)
4. fc(u) = 2 < 3 ≤ fc(t): pigeonhole on phases of t
5. The u-side of t has at most 2 fires over ≥3 phases → some phase has 0
6. That phase is dispatchable (zero-sided)

For S = all procs: check computationally whether it occurs.
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


def find_zw_fc3_cycles(ms, all_c, adj, num=300000, maxs=80):
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
    print("RA13: Does S = all procs (every fc ≥ 3) occur in ZW cycles?")
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

        print(f"\nn={n}: {len(multisets)} multisets, threshold={threshold}")

        total_cycles = 0
        s_all_procs = 0  # Every proc fc ≥ 3
        s_proper = 0     # Some proc fc = 2
        s_proper_gradient_works = 0  # Gradient argument directly applies
        s_all_still_dispatchable = 0  # Even with all fc≥3, some proc has dispatchable phase

        for ms_sorted in multisets:
            P = 1
            for m in ms_sorted: P *= m
            if P > 2000: continue

            seen = set(); pc = 0
            for perm in permutations(ms_sorted):
                if perm in seen: continue
                seen.add(perm); pc += 1
                if pc > (30 if n == 5 else 15): break
                ms = perm
                all_c, adj = build_adj(ms)
                cycles = find_zw_fc3_cycles(ms, all_c, adj,
                    num=(300000 if n == 5 else 150000))

                for cyc in cycles:
                    fc = cyc['fc']
                    total_cycles += 1

                    all_ge3 = all(fc.get(q, 0) >= 3 for q in range(n))
                    if all_ge3:
                        s_all_procs += 1
                        # Check if still dispatchable
                        movers = cyc['movers']; L = len(movers)
                        found_disp = False
                        for q in range(n):
                            fire_pos = [i for i, m in enumerate(movers) if m == q]
                            lq = (q-1)%n; rq = (q+1)%n
                            for pi in range(len(fire_pos)):
                                s = fire_pos[pi]; e = fire_pos[(pi+1)%len(fire_pos)]
                                J = K = 0; pos = (s+1)%L
                                while pos != e:
                                    if movers[pos] == lq: J += 1
                                    if movers[pos] == rq: K += 1
                                    pos = (pos+1)%L
                                if J == 0 or K == 0 or (J%2==0 and K%2==0):
                                    found_disp = True; break
                            if found_disp: break
                        if found_disp:
                            s_all_still_dispatchable += 1
                    else:
                        s_proper += 1
                        # Gradient argument: find boundary of S
                        S = {q for q in range(n) if fc.get(q, 0) >= 3}
                        # Find t ∈ S with neighbor u ∉ S
                        found_boundary = False
                        for t in S:
                            for u in [(t-1)%n, (t+1)%n]:
                                if u not in S:
                                    # fc(t) ≥ 3, fc(u) = 2
                                    # fc(u) < fc(t): pigeonhole
                                    found_boundary = True
                                    break
                            if found_boundary: break
                        if found_boundary:
                            s_proper_gradient_works += 1

        print(f"  Total ZW fc≥3 cycles: {total_cycles}")
        print(f"  S = all procs (every fc≥3): {s_all_procs}")
        print(f"    Still dispatchable: {s_all_still_dispatchable}/{s_all_procs}")
        print(f"  S proper subset: {s_proper}")
        print(f"    Gradient works: {s_proper_gradient_works}/{s_proper}")

    # Check for large n=9 style multisets
    print("\n" + "=" * 60)
    print("LARGE n CHECK (random sampling)")
    print("=" * 60)

    for n in [9]:
        threshold = 4 * 3 ** (n-2)
        # Just test canonical multisets
        test_ms = [
            tuple([2]*3 + [3]*(n-3)),  # 3 binary, rest ternary
            tuple([2]*4 + [3]*(n-4)),  # 4 binary
            tuple([2]*5 + [3]*(n-5)),  # 5 binary
            tuple([2]*n),              # all binary
        ]

        for ms_sorted in test_ms:
            P = 1
            for m in ms_sorted: P *= m
            if P >= threshold or P > 5000:
                print(f"\n  ms={ms_sorted}: P={P} >= threshold or too large, skip")
                continue

            ms = ms_sorted  # Don't permute, just use sorted
            print(f"\n  ms={ms}, P={P}")
            all_c, adj = build_adj(ms)
            cycles = find_zw_fc3_cycles(ms, all_c, adj, num=500000, maxs=150)
            print(f"  ZW fc≥3 cycles found: {len(cycles)}")

            s_all = 0; s_proper = 0; disp = 0
            for cyc in cycles:
                fc = cyc['fc']
                all_ge3 = all(fc.get(q, 0) >= 3 for q in range(n))
                if all_ge3: s_all += 1
                else: s_proper += 1

                # Check dispatchable
                movers = cyc['movers']; L = len(movers)
                found = False
                for q in range(n):
                    if fc.get(q, 0) < 3: continue
                    fire_pos = [i for i, m in enumerate(movers) if m == q]
                    lq = (q-1)%n; rq = (q+1)%n
                    for pi in range(len(fire_pos)):
                        s = fire_pos[pi]; e = fire_pos[(pi+1)%len(fire_pos)]
                        J = K = 0; pos = (s+1)%L
                        while pos != e:
                            if movers[pos] == lq: J += 1
                            if movers[pos] == rq: K += 1
                            pos = (pos+1)%L
                        if J == 0 or K == 0 or (J%2==0 and K%2==0):
                            found = True; break
                    if found: break
                if found: disp += 1

            print(f"  S=all: {s_all}, S=proper: {s_proper}, dispatchable: {disp}/{len(cycles)}")


if __name__ == '__main__':
    main()
