#!/usr/bin/env python3
"""
ra14_ec_proof_n7.py — For n=7+ with valid walks (CL >= 21, non-minimum fc):
verify EC holds and analyze the pigeonhole structure.

KEY INSIGHT: At binary proc p (ms[p]=2, non-consecutive):
- Residue space = ms[L] * ms[p] * ms[R] = 3 * 2 * 3 = 18.
- fc[p] = 2*k for some k >= 1. MINIMUM fc[p] = 2 (since binary).
- Actually: in the non-minimum fc case, the binary might still have fc=2.
  Only ternaries get incremented (to change B parity).

Wait: the edge count analysis showed valid walks exist. But do they have ISOLATED
binary firings? (No two consecutive steps fire the same binary proc.)
The Lean proof gets to the sorry only when binary firings are isolated.

Also: the walk is NON-UNIFORM by construction (since edge counts have both CW and CCW).

Let me verify EC specifically for the valid walks at n=7.
"""
import time
from itertools import combinations


def solve_edge_counts(n, fc, winding=1):
    delta = winding
    f = [fc[p] - delta for p in range(n)]
    A = [0] * n
    S = [0] * n
    A[0] = 0
    S[0] = 1
    for k in range(1, n):
        A[k] = f[k] - A[k-1]
        S[k] = -S[k-1]
    coeff = S[n-1] + 1
    rhs = f[0] - A[n-1]
    if coeff == 0:
        if rhs != 0:
            return None
        import math
        lower = float('-inf')
        upper = float('inf')
        for k in range(n):
            if S[k] > 0:
                lower = max(lower, -A[k] / S[k])
            elif S[k] < 0:
                upper = min(upper, -A[k] / S[k])
            else:
                if A[k] < 0:
                    return None
        if lower > upper:
            return None
        c0 = max(int(lower) if lower == int(lower) else int(lower) + 1, 0)
        if c0 > upper:
            return None
        return [A[k] + S[k] * c0 for k in range(n)]
    else:
        if rhs % coeff != 0:
            return None
        c0 = rhs // coeff
        c = [A[k] + S[k] * c0 for k in range(n)]
        if any(cc < 0 for cc in c):
            return None
        return c


def has_no_triple(ms, n):
    for i in range(n):
        if ms[i] == 2 and ms[(i+1) % n] == 2 and ms[(i+2) % n] == 2:
            return False
    return True


def gen_words_cyclic(n, fc_target, max_results=500, timeout_s=30):
    target_cl = sum(fc_target)
    results = []
    t0 = time.time()
    def dfs(word, fc, start):
        if time.time() - t0 > timeout_s or len(results) >= max_results:
            return
        if len(word) == target_cl:
            if all(fc[p] == fc_target[p] for p in range(n)):
                diff = (start - word[-1]) % n
                if diff == 1 or diff == n - 1:
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
                dfs(word, fc, start)
                word.pop()
                fc[nxt] -= 1
    for start in range(n):
        if time.time() - t0 > timeout_s or len(results) >= max_results:
            break
        fc = [0] * n
        fc[start] = 1
        if fc[start] <= fc_target[start]:
            dfs([start], fc, start)
    return results


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


def canonicalize(word):
    L = len(word)
    best = word
    for i in range(L):
        rot = word[i:] + word[:i]
        if rot < best:
            best = rot
    return best


def check_structural_ec_detailed(word, n, ms):
    """Check EC and return details about where it occurs."""
    L = len(word)
    for p in range(n):
        lp = (p - 1) % n
        rp = (p + 1) % n
        pfc_lp = [0] * (L + 1)
        pfc_p = [0] * (L + 1)
        pfc_rp = [0] * (L + 1)
        for t in range(L):
            pfc_lp[t + 1] = pfc_lp[t] + (1 if word[t] == lp else 0)
            pfc_p[t + 1] = pfc_p[t] + (1 if word[t] == p else 0)
            pfc_rp[t + 1] = pfc_rp[t] + (1 if word[t] == rp else 0)
        mover_steps = [t for t in range(L) if word[t] == p]
        nonmover_steps = [t for t in range(L) if word[t] != p]

        mover_triples = set()
        nonmover_triples = set()
        for s in mover_steps:
            mover_triples.add((pfc_lp[s] % ms[lp], pfc_p[s] % ms[p], pfc_rp[s] % ms[rp]))
        for s in nonmover_steps:
            nonmover_triples.add((pfc_lp[s] % ms[lp], pfc_p[s] % ms[p], pfc_rp[s] % ms[rp]))

        overlap = mover_triples & nonmover_triples
        if overlap:
            return True, p, ms[p], len(mover_steps), len(nonmover_steps), len(mover_triples), len(nonmover_triples), ms[lp]*ms[p]*ms[rp]
    return False, -1, -1, -1, -1, -1, -1, -1


print("RA14: EC Verification for Valid Walks")
print("=" * 70)

for n in [7, 9]:
    threshold = 4 * (3 ** (n - 2))
    print(f"\nn={n}, threshold={threshold}")

    total_walks = 0
    walks_with_ec = 0
    walks_no_ec = 0

    # For EC analysis
    ec_at_binary = 0
    ec_at_ternary = 0
    pigeonhole_works = 0

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

        ternary_pos = [p for p in range(n) if ms[p] == 3]

        # Single-ternary increment
        for tp in ternary_pos[:3]:
            fc = list(ms)
            fc[tp] = 6
            cl = sum(fc)
            if (cl + n) % 2 != 0:
                continue

            # Check if walk exists via edge counts
            for w in [1, -1]:
                c = solve_edge_counts(n, fc, winding=w)
                if c is None:
                    continue

                # Generate actual walks
                words = gen_words_cyclic(n, fc, max_results=50, timeout_s=10)
                unique = {}
                for word in words:
                    can = canonicalize(word)
                    if can not in unique:
                        unique[can] = word

                for word in unique.values():
                    wl = list(word)
                    W = total_displacement(wl, n)
                    if abs(W) != n:
                        continue
                    # All valid walks are non-uniform (from edge count analysis)
                    total_walks += 1
                    has_ec, p, mp, m_count, nm_count, m_dist, nm_dist, space = check_structural_ec_detailed(wl, n, ms)
                    if has_ec:
                        walks_with_ec += 1
                        if mp == 2:
                            ec_at_binary += 1
                        else:
                            ec_at_ternary += 1
                        if m_count + nm_count > space:
                            pigeonhole_works += 1
                    else:
                        walks_no_ec += 1
                        print(f"  NO EC: ms={ms}, fc={fc}, word={wl[:15]}..., CL={len(wl)}")

    print(f"\n  Total valid walks: {total_walks}")
    print(f"  With EC: {walks_with_ec} (binary: {ec_at_binary}, ternary: {ec_at_ternary})")
    print(f"  Without EC: {walks_no_ec}")
    print(f"  Pigeonhole applicable (CL > space): {pigeonhole_works}")

# Now: the pigeonhole argument.
# At binary p (non-consecutive): space = 3*2*3 = 18.
# For n>=7, minimum CL with valid walk = 3n (one ternary doubled).
# 3n >= 21 > 18 for n >= 7.
# So total steps > space size.
# But we need CROSS-TYPE collision.

# KEY INSIGHT: The mover set has exactly fc[p] = 2 elements (for binary p with min fc).
# Actually fc[p] = ms[p] = 2 (binary wasn't incremented).
# Mover has 2 steps -> at most 2 distinct triples.
# Non-mover has CL - 2 = 3n - 2 >= 19 steps -> at most 18 distinct triples (space size).
# Since CL - 2 >= 19 > 18: by pigeonhole, at least 2 non-mover steps share a triple.
# Non-mover distinct triples <= 18.
# Mover distinct triples <= 2.
# Total distinct <= 18 (space).
# Steps assigned: 2 mover + (CL-2) non-mover = CL.

# For EC: need some mover triple = some non-mover triple.
# Mover covers 2 triples. Non-mover covers up to 18 triples.
# If non-mover covers >= 17 of the 18: only 1 triple uncovered.
# Mover has 2 triples; one of them must be in the 17+ covered ones.
# But non-mover might only cover 16 or fewer triples.

# With CL - 2 non-mover steps in 18 slots:
# By pigeonhole, distinct non-mover triples >= ... no, pigeonhole gives UPPER bound on distinct,
# not lower. Actually: distinct elements <= min(count, space) = min(CL-2, 18).
# For CL-2 >= 18: distinct could still be as low as 1 (all same triple).

# So pigeonhole alone doesn't give cross-type collision.
# We need to use the STRUCTURE of the walk.

print(f"\n{'='*70}")
print("ANALYSIS: Non-mover triple coverage at binary procs")
print("=" * 70)

for n in [7]:
    threshold = 4 * (3 ** (n - 2))
    for bins in list(combinations(range(n), 3))[:5]:
        bins_set = set(bins)
        ms = [2 if p in bins_set else 3 for p in range(n)]
        if not has_no_triple(ms, n):
            continue
        prod = 1
        for m in ms:
            prod *= m
        if prod >= threshold:
            continue

        ternary_pos = [p for p in range(n) if ms[p] == 3]
        fc = list(ms)
        fc[ternary_pos[0]] = 6
        cl = sum(fc)
        if (cl + n) % 2 != 0:
            continue

        words = gen_words_cyclic(n, fc, max_results=50, timeout_s=10)
        unique = {}
        for word in words:
            can = canonicalize(word)
            if can not in unique:
                unique[can] = word

        for word in list(unique.values())[:3]:
            wl = list(word)
            W = total_displacement(wl, n)
            if abs(W) != n:
                continue

            L = len(wl)
            print(f"\n  ms={ms}, fc={fc}, word={wl[:20]}..., CL={L}")
            for p in range(n):
                if ms[p] != 2:
                    continue
                lp = (p - 1) % n
                rp = (p + 1) % n

                pfc = {}
                for q in [lp, p, rp]:
                    pfc[q] = [0] * (L + 1)
                    for t in range(L):
                        pfc[q][t + 1] = pfc[q][t] + (1 if wl[t] == q else 0)

                mover_triples = set()
                nonmover_triples = set()
                for t in range(L):
                    triple = (pfc[lp][t] % ms[lp], pfc[p][t] % ms[p], pfc[rp][t] % ms[rp])
                    if wl[t] == p:
                        mover_triples.add(triple)
                    else:
                        nonmover_triples.add(triple)

                overlap = mover_triples & nonmover_triples
                print(f"    p={p}: mover_dist={len(mover_triples)}, nm_dist={len(nonmover_triples)}/18, "
                      f"overlap={len(overlap)}, EC={'YES' if overlap else 'NO'}")


if __name__ == '__main__':
    pass
