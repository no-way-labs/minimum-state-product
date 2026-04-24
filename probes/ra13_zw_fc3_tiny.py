#!/usr/bin/env python3
"""
RA13 TINY: Test only the smallest multisets. Skip expensive config graph building.
Focus: does constant fc occur? Is Case A analytical proof valid?
"""

from itertools import product as iterproduct
from collections import defaultdict
import random

random.seed(42)


def test_ms(ms, num_samples=500000, maxs=80):
    """Test a single ms configuration."""
    n = len(ms)
    P = 1
    for m in ms: P *= m

    # Build config graph
    all_c = list(iterproduct(*[range(m) for m in ms]))
    adj = defaultdict(list)
    for c in all_c:
        for p in range(n):
            for v in range(ms[p]):
                if v != c[p]:
                    c2 = list(c); c2[p] = v
                    adj[c].append((tuple(c2), p))

    stats = {'total': 0, 'case_a': 0, 'case_a_ok': 0, 'case_a_fail': 0,
             'case_b': 0, 'case_b_ok': 0, 'case_b_fail': 0}
    unique = {}

    for _ in range(num_samples):
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
                # ZW check
                cw = ccw = 0
                for i in range(L):
                    d = (cm[i] - cm[i-1]) % n
                    if d == 1: cw += 1
                    elif d == n-1: ccw += 1
                if cw != ccw or cw == 0: break
                if max(fc.values()) < 3: break
                key = (cc[0], tuple(cm))
                if key in unique: break
                unique[key] = True
                stats['total'] += 1

                fc_vals = [fc.get(q, 0) for q in range(n)]
                is_const = (min(fc_vals) == max(fc_vals))

                if not is_const:
                    stats['case_a'] += 1
                    # Gradient: find fc≥3 proc with lower-fc neighbor
                    found = False
                    for q in range(n):
                        if fc_vals[q] < 3: continue
                        lq = (q-1)%n; rq = (q+1)%n
                        if fc_vals[lq] < fc_vals[q] or fc_vals[rq] < fc_vals[q]:
                            # Pigeonhole: lower-fc side has fewer fires than phases
                            # → some phase has 0 from that side → dispatchable
                            # Verify computationally:
                            fp = [i for i, m in enumerate(cm) if m == q]
                            lower_is_left = fc_vals[lq] < fc_vals[q]
                            target = lq if lower_is_left else rq
                            for pi in range(len(fp)):
                                s2 = fp[pi]; e2 = fp[(pi+1)%len(fp)]
                                cnt = 0; pos = (s2+1)%L
                                while pos != e2:
                                    if cm[pos] == target: cnt += 1
                                    pos = (pos+1)%L
                                if cnt == 0:
                                    found = True; break
                            if found: break
                    if found:
                        stats['case_a_ok'] += 1
                    else:
                        stats['case_a_fail'] += 1
                else:
                    stats['case_b'] += 1
                    # Check any phase dispatchable
                    found = False
                    for q in range(n):
                        fp = [i for i, m in enumerate(cm) if m == q]
                        lq = (q-1)%n; rq = (q+1)%n
                        for pi in range(len(fp)):
                            s2 = fp[pi]; e2 = fp[(pi+1)%len(fp)]
                            J = K = 0; pos = (s2+1)%L
                            while pos != e2:
                                if cm[pos] == lq: J += 1
                                if cm[pos] == rq: K += 1
                                pos = (pos+1)%L
                            if J == 0 or K == 0 or (J%2==0 and K%2==0):
                                found = True; break
                        if found: break
                    if found:
                        stats['case_b_ok'] += 1
                    else:
                        stats['case_b_fail'] += 1
                break
            vis[c] = step; path.append(c)

    return stats


def main():
    print("RA13 TINY: Smallest multisets only")
    print("=" * 60)

    test_cases = [
        # n=5
        (2,2,2,2,2), (2,2,2,2,3), (2,2,2,3,3), (2,2,2,3,4),
        # n=7
        (2,2,2,2,2,2,2), (2,2,2,2,2,2,3), (2,2,2,2,2,3,3),
        # n=9
        (2,2,2,2,2,2,2,2,2), (2,2,2,2,2,2,2,2,3),
    ]

    grand = {'total': 0, 'case_a': 0, 'case_a_ok': 0, 'case_a_fail': 0,
             'case_b': 0, 'case_b_ok': 0, 'case_b_fail': 0}

    for ms in test_cases:
        n = len(ms)
        P = 1
        for m in ms: P *= m
        threshold = 4 * 3**(n-2)
        if P >= threshold:
            print(f"ms={ms}: P={P} >= threshold={threshold}, skip")
            continue

        print(f"\nms={ms}, P={P}, n={n}...", end=' ', flush=True)
        s = test_ms(ms, num_samples=300000, maxs=min(80, P//2))
        print(f"total={s['total']}, A={s['case_a']}(ok={s['case_a_ok']},f={s['case_a_fail']}), "
              f"B={s['case_b']}(ok={s['case_b_ok']},f={s['case_b_fail']})")

        for k in grand:
            grand[k] += s[k]

    print(f"\n{'='*60}")
    print(f"GRAND: {grand['total']} cycles")
    print(f"  Case A: {grand['case_a']} (ok={grand['case_a_ok']}, fail={grand['case_a_fail']})")
    print(f"  Case B: {grand['case_b']} (ok={grand['case_b_ok']}, fail={grand['case_b_fail']})")

    if grand['case_a_fail'] == 0 and grand['case_b_fail'] == 0:
        print("\nALL VERIFIED.")
        print(f"  Case A (non-constant fc): {grand['case_a']} — all have gradient → pigeonhole → zero-sided phase")
        print(f"  Case B (constant fc): {grand['case_b']} — all have dispatchable phase (empirical)")


if __name__ == '__main__':
    main()
