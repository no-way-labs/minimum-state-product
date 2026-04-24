#!/usr/bin/env python3
"""
ra14_btb_pigeonhole.py — Prove EC at B-T-B processors via pigeonhole.

Key insight from anatomy: the ternary proc between two binary has space = 2*3*2 = 12.
CL = 3*2 + (n-3)*3 = 3n-3 for minimum fc.
For n>=5: CL = 3n-3 >= 12.

But pigeonhole needs: |mover residues| + |non-mover residues| > 12.
|mover residues| <= fc(p) = 3 (ternary).
|non-mover residues| <= CL - 3 = 3n - 6.
Total = CL = 3n - 3.
For n=5: total = 12 = space. Pigeonhole gives >= 1 overlap, but could be within one set!

Actually: pigeonhole between two sets. If A, B are subsets of S with |A| + |B| > |S|:
then |A ∩ B| >= 1. But here A = mover residue multiset, B = non-mover residue multiset.
We need: |image(A)| + |image(B)| > |S|, where image means distinct values.

But |image(A)| <= min(|A|, |S|) and |image(B)| <= min(|B|, |S|).
If |A| + |B| > |S|: NOT sufficient to conclude overlap of images.
E.g., A = {0,0,0}, B = {1,1,1,...}, |S|=3: |A|+|B| > 3 but images don't overlap.

Wait, but we're looking at residue triples. The MOVER residue values are the (pfc_L mod m_L, pfc_p mod m_p, pfc_R mod m_R) at mover steps. The NON-MOVER residue values are the same at non-mover steps.

For B-T-B: (pfc_L mod 2, pfc_p mod 3, pfc_R mod 2).

The question is: does SOME mover triple equal SOME non-mover triple?

Total steps = CL. Mover steps = fc(p) = ms[p]. Non-mover steps = CL - ms[p].
Each step maps to a point in {0,1} x {0,1,2} x {0,1} = 12 points.
By pigeonhole: if CL > 12, some two steps (of either type) share a residue triple.
But they could both be movers or both be non-movers.

We need a cross-type collision. This is NOT guaranteed by simple pigeonhole!

So what IS the argument? Let me look at what actually happens.
"""
import time
from itertools import combinations
from collections import defaultdict


def total_displacement(word, n):
    W = 0
    L = len(word)
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 0:
            pass
        elif diff <= n // 2:
            W += diff
        else:
            W -= (n - diff)
    return W


def step_directions(word, n):
    L = len(word)
    dirs = []
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 0:
            dirs.append(0)
        elif diff == 1:
            dirs.append(1)
        elif diff == n - 1:
            dirs.append(-1)
        else:
            dirs.append(diff if diff <= n // 2 else diff - n)
    return dirs


def gen_words(n, fc_target, max_results=500, timeout_s=15):
    target_cl = sum(fc_target)
    results = []
    t0 = time.time()
    def dfs(word, fc):
        if time.time() - t0 > timeout_s or len(results) >= max_results:
            return
        if len(word) == target_cl:
            if all(fc[p] == fc_target[p] for p in range(n)):
                results.append(tuple(word))
            return
        remaining = target_cl - len(word)
        needed = sum(max(0, fc_target[p] - fc[p]) for p in range(n))
        if needed > remaining:
            return
        last = word[-1]
        for nxt in [(last + 1) % n, (last - 1) % n]:
            if fc[nxt] < fc_target[nxt]:
                fc[nxt] += 1
                word.append(nxt)
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1
    for start in range(n):
        if time.time() - t0 > timeout_s or len(results) >= max_results:
            break
        fc = [0] * n
        fc[start] = 1
        if fc[start] <= fc_target[start]:
            dfs([start], fc)
    return results


def canonicalize(word):
    L = len(word)
    best = word
    for i in range(L):
        rot = word[i:] + word[:i]
        if rot < best:
            best = rot
    return best


def has_no_triple(ms, n):
    for i in range(n):
        if ms[i] == 2 and ms[(i+1) % n] == 2 and ms[(i+2) % n] == 2:
            return False
    return True


def analyze_btb_residues(word, n, ms):
    """For each B-T-B processor, analyze the mover/non-mover residue structure."""
    L = len(word)
    results = []

    for p in range(n):
        if ms[p] != 3:
            continue  # Only ternary
        lp = (p - 1) % n
        rp = (p + 1) % n
        if ms[lp] != 2 or ms[rp] != 2:
            continue  # Only B-T-B

        pfc_lp = [0] * (L + 1)
        pfc_p = [0] * (L + 1)
        pfc_rp = [0] * (L + 1)
        for t in range(L):
            pfc_lp[t + 1] = pfc_lp[t] + (1 if word[t] == lp else 0)
            pfc_p[t + 1] = pfc_p[t] + (1 if word[t] == p else 0)
            pfc_rp[t + 1] = pfc_rp[t] + (1 if word[t] == rp else 0)

        mover_triples = set()
        nonmover_triples = set()
        for t in range(L):
            triple = (pfc_lp[t] % 2, pfc_p[t] % 3, pfc_rp[t] % 2)
            if word[t] == p:
                mover_triples.add(triple)
            else:
                nonmover_triples.add(triple)

        overlap = mover_triples & nonmover_triples
        results.append({
            'p': p,
            'mover_count': sum(1 for t in range(L) if word[t] == p),
            'nonmover_count': sum(1 for t in range(L) if word[t] != p),
            'mover_distinct': len(mover_triples),
            'nonmover_distinct': len(nonmover_triples),
            'mover_triples': sorted(mover_triples),
            'nonmover_triples': sorted(nonmover_triples),
            'overlap': sorted(overlap),
            'has_ec': len(overlap) > 0,
        })
    return results


def main():
    print("RA14: B-T-B Pigeonhole Analysis")
    print("=" * 70)

    # Key question: for B-T-B procs, do mover and non-mover residue SETS always overlap?
    # Space = {0,1} x {0,1,2} x {0,1} = 12 points.
    # Mover has fc(p)=3 steps -> at most 3 distinct triples.
    # Non-mover has CL-3 steps -> at most min(CL-3, 12) distinct triples.

    # For n=5: CL=12, non-mover has 9 steps.
    # If non-mover covers >= 10 of 12 triples: mover can't avoid overlap (only 2 triples free).
    # But non-mover has 9 steps in 12 slots -> at least 9 distinct? NO: multiple steps can
    # hit the same triple.

    # Let's look at actual coverage.

    for n in [5, 7]:
        threshold = 4 * (3 ** (n - 2))
        print(f"\nn={n}, threshold={threshold}, CL={3*n-3}")
        print("-" * 50)

        total_btb = 0
        btb_with_ec = 0
        nonmover_coverage = []  # fraction of 12 triples covered by non-movers
        mover_coverage = []

        for bins in combinations(range(n), 3):
            bins_set = set(bins)
            ms = [2 if p in bins_set else 3 for p in range(n)]
            if not has_no_triple(ms, n):
                continue
            prod = 1
            for m in ms:
                prod *= m
            if prod >= threshold:
                continue

            fc_target = list(ms)
            words = gen_words(n, fc_target, max_results=300, timeout_s=8)
            unique = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique:
                    unique[c] = w

            for w in unique.values():
                wl = list(w)
                W = total_displacement(wl, n)
                if abs(W) != n:
                    continue
                dirs = step_directions(wl, n)
                ns = [d for d in dirs if d != 0]
                if not ns or all(d == ns[0] for d in ns):
                    continue

                btb_data = analyze_btb_residues(wl, n, ms)
                for bd in btb_data:
                    total_btb += 1
                    if bd['has_ec']:
                        btb_with_ec += 1
                    nonmover_coverage.append(bd['nonmover_distinct'])
                    mover_coverage.append(bd['mover_distinct'])

                    if not bd['has_ec'] and n <= 7:
                        print(f"  NO EC at B-T-B! ms={ms}, p={bd['p']}")
                        print(f"    Mover triples ({bd['mover_distinct']}): {bd['mover_triples']}")
                        print(f"    Non-mover triples ({bd['nonmover_distinct']}): {bd['nonmover_triples']}")

        print(f"\n  B-T-B processors analyzed: {total_btb}")
        print(f"  B-T-B with EC: {btb_with_ec} ({100*btb_with_ec/total_btb:.1f}%)")
        if nonmover_coverage:
            print(f"  Non-mover distinct triples: min={min(nonmover_coverage)}, max={max(nonmover_coverage)}, "
                  f"mean={sum(nonmover_coverage)/len(nonmover_coverage):.1f}")
            print(f"  Mover distinct triples: min={min(mover_coverage)}, max={max(mover_coverage)}, "
                  f"mean={sum(mover_coverage)/len(mover_coverage):.1f}")

    # Now let's understand WHY B-T-B always has EC.
    # The ternary proc p fires 3 times. Its left and right are binary (fire 2 times each).
    # The pfc at left changes: 0 -> 0 -> 1 -> 1 -> 2(=0 mod 2) across the cycle.
    # But the exact pattern depends on the word structure.

    # KEY INSIGHT: Look at the pfc_p values at mover steps.
    # At mover step for p: pfc_p takes values 0, 1, 2 (since p fires 3 times, pfc before
    # each fire is 0, 1, 2). After all fires: pfc_p = 3 = 0 mod 3.
    # So mover pfc_p values are {0, 1, 2} -- ALL THREE residues!
    # For non-mover steps: pfc_p ranges over 0,0,...,1,1,...,2,2,...,0 (mod 3).
    # Non-mover pfc_p also covers {0, 1, 2} (since there are non-mover steps between fires).

    # So the pfc_p component doesn't help distinguish. The discrimination must come from
    # (pfc_L mod 2, pfc_R mod 2).

    # At mover step 1 (pfc_p=0): (pfc_L mod 2, pfc_R mod 2) = some (a, b)
    # At mover step 2 (pfc_p=1): (a', b')
    # At mover step 3 (pfc_p=2): (a'', b'')
    # These 3 points in {0,1}^2 can't all be distinct (only 4 points in {0,1}^2).
    # But we need to match against non-movers at the SAME pfc_p residue.

    # For each r in {0,1,2}: find (pfc_L, pfc_R) mod (2,2) at mover step with pfc_p=r
    # and at all non-mover steps with pfc_p=r.
    # EC iff exists r where mover's (a,b) appears in non-mover's set at pfc_p=r.

    print(f"\n{'='*70}")
    print("PARITY LAYER ANALYSIS")
    print("For each B-T-B, decompose by pfc_p residue")
    print("=" * 70)

    for n in [5]:
        threshold = 4 * (3 ** (n - 2))
        for bins in combinations(range(n), 3):
            bins_set = set(bins)
            ms = [2 if p in bins_set else 3 for p in range(n)]
            if not has_no_triple(ms, n):
                continue
            prod = 1
            for m in ms:
                prod *= m
            if prod >= threshold:
                continue

            fc_target = list(ms)
            words = gen_words(n, fc_target, max_results=100, timeout_s=5)
            unique = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique:
                    unique[c] = w

            count = 0
            for w in list(unique.values())[:5]:
                wl = list(w)
                W = total_displacement(wl, n)
                if abs(W) != n:
                    continue
                dirs = step_directions(wl, n)
                ns_d = [d for d in dirs if d != 0]
                if not ns_d or all(d == ns_d[0] for d in ns_d):
                    continue
                count += 1
                if count > 3:
                    break

                L = len(wl)
                for p in range(n):
                    if ms[p] != 3:
                        continue
                    lp = (p - 1) % n
                    rp = (p + 1) % n
                    if ms[lp] != 2 or ms[rp] != 2:
                        continue

                    pfc_lp = [0] * (L + 1)
                    pfc_p = [0] * (L + 1)
                    pfc_rp = [0] * (L + 1)
                    for t in range(L):
                        pfc_lp[t + 1] = pfc_lp[t] + (1 if wl[t] == lp else 0)
                        pfc_p[t + 1] = pfc_p[t] + (1 if wl[t] == p else 0)
                        pfc_rp[t + 1] = pfc_rp[t] + (1 if wl[t] == rp else 0)

                    print(f"\n  ms={ms}, word={wl}, p={p} (B-T-B)")
                    for r in range(3):
                        mover_pts = []
                        nonmover_pts = []
                        for t in range(L):
                            if pfc_p[t] % 3 == r:
                                pt = (pfc_lp[t] % 2, pfc_rp[t] % 2)
                                if wl[t] == p:
                                    mover_pts.append((t, pt))
                                else:
                                    nonmover_pts.append((t, pt))
                        mover_set = set(pt for _, pt in mover_pts)
                        nonmover_set = set(pt for _, pt in nonmover_pts)
                        overlap = mover_set & nonmover_set
                        print(f"    pfc_p={r}: mover {mover_pts} | nonmover(pts) {[pt for _, pt in nonmover_pts]} | overlap={overlap}")


if __name__ == '__main__':
    main()
