#!/usr/bin/env python3
"""
Phase 0e: case-analysis probe for the Lemma A proof attempt.

The proof attempt for Lemma A (zw_provider_two_site_complementary_tail)
reduces to ruling out NEITHER: right-co-location fails AND left-co-location
fails simultaneously. Right-co-location fails iff Case (ii.a):

  rho_3 in (e, s)  AND  b_2 in (e, rho_3]

where rho_3 is the r_b fire immediately cyclically before rho_1 = s + 1.

Symmetric for left (swap b<->c, rho<->lambda, etc).

This probe reports, for every oscillatory B2B run:
- which co-location case it's in for right (A / i / ii.a / ii.b)
- which co-location case it's in for left  (A / I / II.a / II.b)
- whether word[s-1] = r_b (the "singleton sub-case" for right)
- whether word[e+1] = l_c (the "singleton sub-case" for left)
- joint histogram of (right case, left case)

If NEITHER is combinatorially impossible, the joint histogram will show
0 cases of (ii.a, II.a). Moreover, if the singleton sub-case co-occurrence
(word[s-1] = r_b AND word[e+1] = l_c) never happens, that is a sharper
local contradiction.
"""

import time
from collections import Counter


def L_(p, n): return (p - 1) % n
def R_(p, n): return (p + 1) % n


def enumerate_min_length_cycles(ms, n):
    L = sum(ms)
    start_cfg = tuple([0] * n)
    results = []

    def dfs(word, fc, config, visited):
        plen = len(word)
        if plen == L:
            first, last = word[0], word[-1]
            if first != R_(last, n) and first != L_(last, n) and first != last:
                return
            if config != start_cfg:
                return
            if not all(fc[p] == ms[p] for p in range(n)):
                return
            results.append(tuple(word))
            return
        remaining = L - plen
        needed = sum(ms[p] - fc[p] for p in range(n) if fc[p] < ms[p])
        if needed > remaining:
            return
        last = word[-1]
        for nxt in (R_(last, n), L_(last, n), last):
            if fc[nxt] >= ms[nxt]:
                continue
            nc = list(config)
            nc[nxt] = (nc[nxt] + 1) % ms[nxt]
            nc_t = tuple(nc)
            if nc_t in visited:
                if not (nc_t == start_cfg and plen == L - 1):
                    continue
            nf = list(fc)
            nf[nxt] += 1
            word.append(nxt)
            added = False
            if nc_t != start_cfg:
                visited.add(nc_t)
                added = True
            dfs(word, nf, nc_t, visited)
            if added:
                visited.discard(nc_t)
            word.pop()

    p_start = 0
    fc0 = [0] * n
    fc0[p_start] = 1
    cfg0 = [0] * n
    cfg0[p_start] = 1 % ms[p_start]
    visited = {tuple(cfg0)}
    dfs([p_start], fc0, tuple(cfg0), visited)
    return results


def is_zw_cwpos(word, n):
    L = len(word)
    cw = ccw = 0
    for k in range(L):
        nxt = word[(k + 1) % L]
        if nxt == R_(word[k], n):
            cw += 1
        elif nxt == L_(word[k], n):
            ccw += 1
    return cw == ccw and cw > 0


def canonical_rotation(word):
    L = len(word)
    return min(word[i:] + word[:i] for i in range(L))


def gap_interior_cw(b, c, n):
    out = []
    k = R_(b, n)
    while k != c:
        out.append(k)
        k = R_(k, n)
    return out


def binary_pairs(ms, n):
    bins = [p for p in range(n) if ms[p] == 2]
    pairs = []
    for idx, b in enumerate(bins):
        c = bins[(idx + 1) % len(bins)]
        interior = gap_interior_cw(b, c, n)
        if len(interior) >= 1:
            pairs.append((b, c, frozenset(interior)))
    return pairs


def find_gap_runs(word, b, c, interior):
    L = len(word)
    runs = []
    for s in range(L):
        if word[s] != b:
            continue
        k = (s + 1) % L
        if word[k] not in interior:
            continue
        steps = 0
        while word[k] in interior:
            k = (k + 1) % L
            steps += 1
            if steps > L:
                break
        if word[k] == c:
            runs.append((s, k))
    return runs


def is_oscillatory(word, s, e, n):
    L = len(word)
    has_cw = has_ccw = False
    k = s
    steps = 0
    while k != e and steps <= L:
        nxt = (k + 1) % L
        if word[nxt] == R_(word[k], n):
            has_cw = True
        elif word[nxt] == L_(word[k], n):
            has_ccw = True
        if has_cw and has_ccw:
            return True
        k = nxt
        steps += 1
    return has_cw and has_ccw


def in_open_cyclic(a1, a2, x, L):
    """x in open cyclic interval (a1, a2)."""
    return 0 < (x - a1) % L < (a2 - a1) % L


def classify_right(word, b, c, s, e, L, n):
    """Classify the right-co-location case for a run from b to c, starting
    at step s (b_1) and ending at step e (c_1)."""
    rb = R_(b, n)
    # Locate the other b-fire (b_2)
    b_fires = [k for k in range(L) if word[k] == b]
    if len(b_fires) != 2:
        return 'nonstandard'
    b1, b2_candidate = b_fires
    if b1 == s:
        b_2 = b2_candidate
    elif b2_candidate == s:
        b_2 = b1
    else:
        return 'nonstandard'
    rb_fires = sorted([k for k in range(L) if word[k] == rb])
    m_rb = len(rb_fires)
    if m_rb < 2:
        return 'nonstandard'
    # Find rho_1 = r_b fire at step s+1 (should exist by subclaim 1)
    rho_1 = (s + 1) % L
    if word[rho_1] != rb:
        return 'subclaim1_fails'
    # Find rho_3 = r_b fire immediately cyclically before rho_1
    idx = rb_fires.index(rho_1)
    rho_3 = rb_fires[(idx - 1) % m_rb]
    # Right co-location: b_2 in open cyclic (rho_3, rho_1)
    co_located = in_open_cyclic(rho_3, rho_1, b_2, L)
    # rho_3 position: is it inside the run (s, e) or in the complementary
    # arc (e, s)?
    in_run = in_open_cyclic(s, e, rho_3, L)
    if in_run or rho_3 == e:
        case = 'i'   # rho_3 in run or at e
    else:
        # rho_3 in complementary arc (e, s)
        if rho_3 == (s - 1) % L:
            case = 'ii_singleton'  # word[s-1] = r_b
        else:
            case = 'ii_other'
    return (case, co_located)


def classify_left(word, b, c, s, e, L, n):
    lc = L_(c, n)
    c_fires = [k for k in range(L) if word[k] == c]
    if len(c_fires) != 2:
        return 'nonstandard'
    c1_candidate, c2_candidate = c_fires
    if c1_candidate == e:
        c_2 = c2_candidate
    elif c2_candidate == e:
        c_2 = c1_candidate
    else:
        return 'nonstandard'
    lc_fires = sorted([k for k in range(L) if word[k] == lc])
    m_lc = len(lc_fires)
    if m_lc < 2:
        return 'nonstandard'
    # Subclaim 2: word[e-1] = l_c. lambda_prev = e-1.
    lam_prev = (e - 1) % L
    if word[lam_prev] != lc:
        return 'subclaim2_fails'
    idx = lc_fires.index(lam_prev)
    lam_next = lc_fires[(idx + 1) % m_lc]
    # Left co-location: c_1 = e in open (lam_prev, lam_next); c_2 also in
    # that interval
    co_located = in_open_cyclic(lam_prev, lam_next, c_2, L)
    # lam_next position: inside run or in complementary arc
    in_run = in_open_cyclic(s, e, lam_next, L)
    if in_run or lam_next == s:
        case = 'I'  # lam_next in run or at s
    else:
        # lam_next in (e, s)? Check: is lam_next in open (e, s)?
        in_comp = in_open_cyclic(e, s, lam_next, L)
        if in_comp:
            if lam_next == (e + 1) % L:
                case = 'II_singleton'  # word[e+1] = l_c
            else:
                case = 'II_other'
        else:
            # lam_next is not in run and not in comp — shouldn't happen
            case = 'anomalous'
    return (case, co_located)


def run_family(label, ms, n):
    L = sum(ms)
    print(f"\n=== {label}: n={n}, ms={tuple(ms)} ===", flush=True)

    t0 = time.time()
    raw = enumerate_min_length_cycles(list(ms), n)
    uniq = set(canonical_rotation(w) for w in raw)
    zw = [w for w in uniq if is_zw_cwpos(w, n)]
    t1 = time.time()
    print(f"  ZW cw>0 cycles: {len(zw)} (enum {t1 - t0:.1f}s)", flush=True)

    right_case_count = Counter()
    left_case_count = Counter()
    joint_case_count = Counter()
    joint_failure_count = Counter()  # (right_fail, left_fail) -> count
    singleton_cooccur = 0
    run_count = 0

    for w in zw:
        wlen = len(w)
        for b, c, interior in binary_pairs(list(ms), n):
            for (s, e) in find_gap_runs(w, b, c, interior):
                if not is_oscillatory(w, s, e, n):
                    continue
                run_count += 1
                r = classify_right(w, b, c, s, e, wlen, n)
                l = classify_left(w, b, c, s, e, wlen, n)
                if isinstance(r, tuple) and isinstance(l, tuple):
                    r_case, r_coloc = r
                    l_case, l_coloc = l
                    right_case_count[r_case] += 1
                    left_case_count[l_case] += 1
                    joint_case_count[(r_case, l_case)] += 1
                    joint_failure_count[(not r_coloc, not l_coloc)] += 1
                    if r_case == 'ii_singleton' and l_case == 'II_singleton':
                        singleton_cooccur += 1
                else:
                    right_case_count['ERR'] += 1
                    left_case_count['ERR'] += 1

    print(f"  Total oscillatory B2B runs: {run_count}", flush=True)
    print(f"  Right case histogram: {dict(right_case_count)}", flush=True)
    print(f"  Left  case histogram: {dict(left_case_count)}", flush=True)
    print(f"  Joint (right, left) case histogram:", flush=True)
    for k, v in sorted(joint_case_count.items(), key=lambda x: -x[1]):
        print(f"    {k}  x {v}", flush=True)
    print(f"  (right_fails, left_fails): {dict(joint_failure_count)}", flush=True)
    neither = joint_failure_count.get((True, True), 0)
    if neither > 0:
        print(f"  *** LEMMA A FAILS: {neither} NEITHER cases", flush=True)
    else:
        print(f"  Lemma A holds: 0 NEITHER cases", flush=True)
    print(f"  Singleton sub-case co-occurrence "
          f"(word[s-1]=r_b AND word[e+1]=l_c): {singleton_cooccur}", flush=True)


if __name__ == "__main__":
    families = [
        (9,  "n9  all-odd-gap",       [2, 3, 3, 2, 3, 3, 2, 3, 3]),
        (9,  "n9  3-consec-binary",   [2, 2, 2, 3, 3, 3, 3, 3, 3]),
        (9,  "n9  pivot alt",         [2, 3, 2, 3, 2, 3, 3, 3, 3]),
        (9,  "n9  3-all-spaced",      [2, 3, 3, 3, 2, 3, 3, 3, 2]),
        (9,  "n9  gap-(2,3,4)",       [2, 3, 2, 3, 3, 2, 3, 3, 3]),
        (9,  "n9  4-bin alternating", [2, 3, 2, 3, 2, 3, 2, 3, 3]),
        (11, "n11 all-odd-gap",       [2, 3, 3, 2, 3, 3, 2, 3, 3, 3, 3]),
        (11, "n11 3-consec-binary",   [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3]),
        (11, "n11 pivot 3bin",        [2, 3, 2, 3, 2, 3, 3, 3, 3, 3, 3]),
        (11, "n11 4-bin spaced",      [2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3]),
    ]
    for n, label, ms in families:
        run_family(label, ms, n)
