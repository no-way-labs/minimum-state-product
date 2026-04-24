#!/usr/bin/env python3
"""
Phase 0d: Direct verification probe for Lemma A (anchor co-location).

Lemma A claim (as stated in zw_provider_two_site_complementary_tail):

  For every oscillatory B2B run in gap (b, c), at least one of
    - right(b) has a consecutive-fire pair whose open interval contains
      both fires of b, OR
    - left(c) has a consecutive-fire pair whose open interval contains
      both fires of c.

This probe checks the claim at the RUN level (not at the winning-witness
level — the budget probe only saw co-location for *winning* witnesses,
which is circular if co-location is a prerequisite for winning).

The probe asks, for every oscillatory B2B run:
  A. does right(b) have a consec-fire pair with both b-fires? (boolean)
  B. does left(c) have a consec-fire pair with both c-fires? (boolean)

It reports three cases per run:
  - "both":        A and B
  - "r(b) only":   A but not B
  - "l(c) only":   B but not A
  - "neither":     not A and not B  <-- LEMMA A FAILS

If "neither" count is always 0 across all tested families, Lemma A holds
in its disjunction form. If always "both", the stronger conjunction form
holds.

This probe also records which direction-block pattern the co-location
interval takes, as a hint toward the Lemma B structural claim.
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


def interval_contains_both(word, site, anchor, n):
    """Return the consec-fire pair (a1, a2) of site whose open interval
    contains both of anchor's fires, or None if no such pair exists."""
    L = len(word)
    anchor_steps = [k for k in range(L) if word[k] == anchor]
    if len(anchor_steps) != 2:
        return None
    t0, t1 = anchor_steps
    site_steps = [k for k in range(L) if word[k] == site]
    m = len(site_steps)
    if m < 2:
        return None
    for idx in range(m):
        a1 = site_steps[idx]
        a2 = site_steps[(idx + 1) % m]
        if (a2 - a1) % L <= 1:
            continue
        # Is t0 in open (a1, a2)? And t1?
        def in_open(x):
            o = (x - a1) % L
            oa2 = (a2 - a1) % L
            return 0 < o < oa2
        if in_open(t0) and in_open(t1):
            return (a1, a2)
    return None


def classify_interval_entry(word, a1, a2, site, b, c, own_gap_interior):
    """Given a consec-fire pair (a1, a2) of site containing both anchor
    fires, classify the walk on the open interval:
      - 'pure-complementary': walk visits no own-gap-interior position
      - 'mixed':               walk visits some own-gap-interior positions
    """
    L = len(word)
    k = (a1 + 1) % L
    while k != a2:
        if word[k] in own_gap_interior and word[k] != site:
            return 'mixed'
        k = (k + 1) % L
    return 'pure-complementary'


def run_family(label, ms, n):
    L = sum(ms)
    bins = [p for p in range(n) if ms[p] == 2]
    print(f"\n=== {label}: n={n}, ms={tuple(ms)} ===", flush=True)
    print(f"  binaries at {bins}, min CL = {L}", flush=True)

    t0 = time.time()
    raw = enumerate_min_length_cycles(list(ms), n)
    uniq = set(canonical_rotation(w) for w in raw)
    zw = [w for w in uniq if is_zw_cwpos(w, n)]
    t1 = time.time()
    print(f"  ZW cw>0 cycles: {len(zw)} (enum {t1 - t0:.1f}s)", flush=True)

    total_runs = 0
    case_count = Counter()  # 'both' / 'rb-only' / 'lc-only' / 'NEITHER'
    rb_classify = Counter()
    lc_classify = Counter()
    neither_examples = []

    ms_list = list(ms)

    for w in zw:
        for b, c, interior in binary_pairs(ms_list, n):
            runs = find_gap_runs(w, b, c, interior)
            for (s, e) in runs:
                if not is_oscillatory(w, s, e, n):
                    continue
                total_runs += 1
                own_gap = set(interior)

                rb_pair = interval_contains_both(w, R_(b, n), b, n)
                lc_pair = interval_contains_both(w, L_(c, n), c, n)

                rb_has = rb_pair is not None
                lc_has = lc_pair is not None

                if rb_has and lc_has:
                    case_count['both'] += 1
                elif rb_has and not lc_has:
                    case_count['rb-only'] += 1
                elif lc_has and not rb_has:
                    case_count['lc-only'] += 1
                else:
                    case_count['NEITHER'] += 1
                    if len(neither_examples) < 3:
                        neither_examples.append((w, b, c, s, e))

                if rb_has:
                    cls = classify_interval_entry(
                        w, rb_pair[0], rb_pair[1], R_(b, n), b, c, own_gap)
                    rb_classify[cls] += 1
                if lc_has:
                    cls = classify_interval_entry(
                        w, lc_pair[0], lc_pair[1], L_(c, n), b, c, own_gap)
                    lc_classify[cls] += 1

    print(f"  Total oscillatory B2B runs: {total_runs}", flush=True)
    print(f"  Case counts:", flush=True)
    for case, cnt in sorted(case_count.items(), key=lambda x: -x[1]):
        print(f"    {case:<10s}  {cnt:>6d}  ({100*cnt/max(1,total_runs):5.1f}%)",
              flush=True)
    print(f"  right(b) co-location interval shape:", flush=True)
    for cls, cnt in sorted(rb_classify.items(), key=lambda x: -x[1]):
        print(f"    {cls:<22s}  {cnt:>6d}", flush=True)
    print(f"  left(c) co-location interval shape:", flush=True)
    for cls, cnt in sorted(lc_classify.items(), key=lambda x: -x[1]):
        print(f"    {cls:<22s}  {cnt:>6d}", flush=True)

    if case_count['NEITHER']:
        print(f"  *** LEMMA A FAILS — examples:", flush=True)
        for (w, b, c, s, e) in neither_examples:
            print(f"    word={w}", flush=True)
            print(f"    b={b}, c={c}, run=[s={s}, e={e}]", flush=True)
    else:
        print(f"  LEMMA A HOLDS (disjunction form) on this family", flush=True)
        if case_count['rb-only'] == 0 and case_count['lc-only'] == 0:
            print(f"  LEMMA A HOLDS (conjunction form) on this family", flush=True)


if __name__ == "__main__":
    families = [
        (9,  "n9  all-odd-gap",        [2, 3, 3, 2, 3, 3, 2, 3, 3]),
        (9,  "n9  3-consec-binary",    [2, 2, 2, 3, 3, 3, 3, 3, 3]),
        (9,  "n9  pivot alt",          [2, 3, 2, 3, 2, 3, 3, 3, 3]),
        (9,  "n9  3-all-spaced",       [2, 3, 3, 3, 2, 3, 3, 3, 2]),
        (9,  "n9  gap-(2,3,4)",        [2, 3, 2, 3, 3, 2, 3, 3, 3]),
        (9,  "n9  4-bin alternating",  [2, 3, 2, 3, 2, 3, 2, 3, 3]),
        (11, "n11 all-odd-gap",        [2, 3, 3, 2, 3, 3, 2, 3, 3, 3, 3]),
        (11, "n11 3-consec-binary",    [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3]),
        (11, "n11 pivot 3bin",         [2, 3, 2, 3, 2, 3, 3, 3, 3, 3, 3]),
        (11, "n11 4-bin spaced",       [2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3]),
    ]
    for n, label, ms in families:
        run_family(label, ms, n)
