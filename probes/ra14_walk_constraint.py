#!/usr/bin/env python3
"""
ra14_walk_constraint.py — Exploit odd-winding + non-uniform structure for EC proof.

KEY INSIGHT to explore: the walk on the ring is a +-1 cyclic walk.
Odd winding means net displacement = +-n (one full loop).
Non-uniform means both CW and CCW steps.

The pfc at processor q changes by 1 each time the walk visits q.
Between consecutive visits to q, the walk goes to one neighbor, traverses some
path, and returns. This creates a specific pattern in the pfc values of q's neighbors.

For binary p with ternary neighbors L, R:
- p is visited exactly 2 times
- The walk arrives at p from L or R each time
- Between visits to p, the walk must go around and come back

Let me trace the EXACT pfc evolution at binary procs and their neighbors.

For minimum fc: binary fires 2, ternary fires 3.
Ring walk of length CL = 3*2 + (n-3)*3 = 3n-3.

Each step is +-1 on the ring. The word is a sequence of ring positions.
"""
import time
from itertools import combinations
from collections import Counter


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


def analyze_walk_pfc(word, n, ms):
    """
    Trace the walk and compute the cumulative PFC vector at each step.
    Also compute the 'direction sequence' at each processor.
    """
    L = len(word)

    # PFC vector at each step
    pfc = [[0]*n for _ in range(L+1)]
    for t in range(L):
        for q in range(n):
            pfc[t+1][q] = pfc[t][q] + (1 if word[t] == q else 0)

    # Direction at each step
    dirs = step_directions(word, n)

    # For each processor p, when it fires (word[t]=p), what direction did the walk come from?
    # If word[t]=p and word[t-1]=p-1: came from left (CW arrival)
    # If word[t]=p and word[t-1]=p+1: came from right (CCW arrival)
    for p in range(n):
        fires = [t for t in range(L) if word[t] == p]
        if ms[p] != 2:
            continue
        # For binary p, exactly 2 fires.
        lp = (p - 1) % n
        rp = (p + 1) % n
        arrivals = []
        for t in fires:
            prev = word[(t - 1) % L]
            if prev == lp:
                arrivals.append('from_L')  # came CW
            elif prev == rp:
                arrivals.append('from_R')  # came CCW
            else:
                arrivals.append(f'from_{prev}')  # shouldn't happen for +-1 walk
        yield p, fires, arrivals, pfc


def main():
    print("RA14: Walk Constraint Analysis")
    print("=" * 70)

    # Key idea: decompose the walk into "excursions" from each processor.
    # Between two visits to p, the walk does an excursion that visits each
    # neighbor a certain number of times.

    # For the FULL residue vector approach:
    # The walk visits CL positions. The residue vector r(t) = (pfc_0(t) mod m_0, ...).
    # r(0) = (0,...,0). r(CL) = (fc_0 mod m_0, ..., fc_{n-1} mod m_{n-1}).
    # Since fc_q = ms[q] for mult=1: r(CL) = r(0) = (0,...,0).
    # So the residue vector is PERIODIC with period CL.

    # Now, key property: in a +-1 walk on the ring, when position is at p,
    # the next step goes to p+1 or p-1. So the walk passes through p between
    # visiting p-1 and p+1.

    # The PFC increments for neighbors of p between consecutive p-visits:
    # Between fire 1 and fire 2 at p, the walk visits some of p's neighbors.
    # Specifically, left neighbor L gets visited some number of times,
    # right neighbor R gets visited some number of times.

    # For a +-1 walk: between two visits to p, the walk must leave p (to L or R)
    # and return to p. The excursion visits L and R specific numbers of times.

    # Let's compute: for binary p with fires at t1, t2:
    # delta_L = pfc[L][t2] - pfc[L][t1]: how many times L fired between p's two fires
    # delta_R = pfc[R][t2] - pfc[R][t1]: how many times R fired between p's two fires

    for n in [5]:
        threshold = 4 * (3 ** (n - 2))
        print(f"\nn={n}")

        delta_patterns = Counter()

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
                ns_d = [d for d in dirs if d != 0]
                if not ns_d or all(d == ns_d[0] for d in ns_d):
                    continue

                L_len = len(wl)
                pfc = [[0]*n for _ in range(L_len+1)]
                for t in range(L_len):
                    for q in range(n):
                        pfc[t+1][q] = pfc[t][q] + (1 if wl[t] == q else 0)

                for p in range(n):
                    if ms[p] != 2:
                        continue
                    lp = (p - 1) % n
                    rp = (p + 1) % n
                    fires = [t for t in range(L_len) if wl[t] == p]
                    t1, t2 = fires[0], fires[1]

                    # Delta between fires
                    delta_L = pfc[t2][lp] - pfc[t1][lp]
                    delta_R = pfc[t2][rp] - pfc[t1][rp]

                    # Arrival directions
                    prev1 = wl[(t1 - 1) % L_len]
                    prev2 = wl[(t2 - 1) % L_len]
                    arr1 = 'L' if prev1 == lp else ('R' if prev1 == rp else '?')
                    arr2 = 'L' if prev2 == lp else ('R' if prev2 == rp else '?')

                    pattern = (delta_L, delta_R, arr1, arr2)
                    delta_patterns[pattern] += 1

        print(f"\n  Delta patterns (dL, dR, arr1, arr2) -> count:")
        for pat, cnt in sorted(delta_patterns.items(), key=lambda x: -x[1]):
            print(f"    {pat}: {cnt}")

    # Now the KEY theoretical question:
    # For binary p with fc=2, the mover residue at the 1st fire has:
    #   (pfc_L mod 3, 0, pfc_R mod 3)
    # At the 2nd fire:
    #   ((pfc_L + dL) mod 3, 1, (pfc_R + dR) mod 3)
    #
    # Non-mover steps between the two fires have pfc_p = 1.
    # Non-mover steps outside have pfc_p = 0 (before fire 1 or after fire 2).
    #
    # For EC at pfc_p=0: the first mover's (pfc_L, pfc_R) mod (3,3)
    # must appear among non-mover steps with pfc_p=0.
    #
    # The non-mover steps with pfc_p=0 are those before the first fire
    # and those after the second fire. Their (pfc_L, pfc_R) values trace
    # a specific path in Z_3 x Z_3.

    print(f"\n{'='*70}")
    print("TRACE ANALYSIS: pfc_L, pfc_R at non-mover steps per parity")
    print("=" * 70)

    for n in [5]:
        threshold = 4 * (3 ** (n - 2))
        for bins in list(combinations(range(n), 3))[:2]:
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
            words = gen_words(n, fc_target, max_results=50, timeout_s=5)
            unique = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique:
                    unique[c] = w

            count = 0
            for w in list(unique.values()):
                wl = list(w)
                W = total_displacement(wl, n)
                if abs(W) != n:
                    continue
                dirs = step_directions(wl, n)
                ns_d = [d for d in dirs if d != 0]
                if not ns_d or all(d == ns_d[0] for d in ns_d):
                    continue
                count += 1
                if count > 2:
                    break

                L_len = len(wl)
                pfc_arr = [[0]*n for _ in range(L_len+1)]
                for t in range(L_len):
                    for q in range(n):
                        pfc_arr[t+1][q] = pfc_arr[t][q] + (1 if wl[t] == q else 0)

                print(f"\n  word={wl}, ms={ms}")
                for p in range(n):
                    if ms[p] != 2:
                        continue
                    lp = (p - 1) % n
                    rp = (p + 1) % n
                    fires = [t for t in range(L_len) if wl[t] == p]
                    print(f"    Binary p={p} (L={lp}, R={rp}), fires at t={fires}")

                    for t in range(L_len):
                        mover_flag = "MOVER" if wl[t] == p else ""
                        rL = pfc_arr[t][lp] % ms[lp]
                        rP = pfc_arr[t][p] % ms[p]
                        rR = pfc_arr[t][rp] % ms[rp]
                        print(f"      t={t:2d}: pos={wl[t]}, pfc_p%2={rP}, (rL,rR)=({rL},{rR}) {mover_flag}")


if __name__ == '__main__':
    main()
