#!/usr/bin/env python3
"""
Phase 0c: n=11 stress test for the two-site complementary-tail rule.

The n=9 probe (zw_boundary_pivot_mechanism.py) found a clean deterministic
rule across 2,785 runs in 6 families: every oscillatory B2B run is covered
by a broad provider at `right(b)` or `left(c)` whose tail lies entirely in
the complementary adjacent gap of that anchor binary. Every single winning
witness was complementary — zero own-gap or mixed tails.

This script stress-tests the same rule at n=11 on a few representative
sub-threshold >=3-binary families. If the rule holds, confidence jumps.
If it breaks, we learn the scope.

Runtime warning: n=11 min CL >= 30 and enumeration is order-of-magnitude
slower than n=9. This script is intended to run in the background.
"""

import time
from collections import Counter, defaultdict


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


def probe_stencil_at(word, ms, n, site_proc, own_gap_interior_set, b, c):
    L = len(word)
    i = site_proc
    li = L_(i, n)
    ri = R_(i, n)
    fire_steps = [k for k in range(L) if word[k] == i]
    m = len(fire_steps)
    if m < 2:
        return []
    successes = []
    own_closure = own_gap_interior_set | {b, c}
    for idx in range(m):
        a1 = fire_steps[idx]
        a2 = fire_steps[(idx + 1) % m]
        if (a2 - a1) % L <= 1:
            continue
        k2 = (a1 + 1) % L
        while k2 != a2:
            if word[k2] == i:
                k2 = (k2 + 1) % L
                continue
            tail_positions = []
            l_fires = r_fires = 0
            k = k2
            while k != a2:
                tail_positions.append(word[k])
                if word[k] == li:
                    l_fires += 1
                elif word[k] == ri:
                    r_fires += 1
                k = (k + 1) % L
            l_ok = (l_fires == 0) or (ms[li] == 2 and l_fires % 2 == 0)
            r_ok = (r_fires == 0) or (ms[ri] == 2 and r_fires % 2 == 0)
            if l_ok and r_ok:
                tail_set = set(tail_positions)
                hits_own_int = bool(tail_set & own_gap_interior_set)
                hits_complement = bool(tail_set - own_closure)
                if hits_own_int and hits_complement:
                    gap_kind = 'mixed'
                elif hits_own_int:
                    gap_kind = 'own'
                else:
                    gap_kind = 'complementary'
                successes.append({
                    'a1': a1, 'a2': a2, 'k2': k2,
                    'gap_kind': gap_kind,
                    'l_fires': l_fires, 'r_fires': r_fires,
                })
            k2 = (k2 + 1) % L
    return successes


def stencil_sites(b, c, n):
    return [
        ("b",        b),
        ("right(b)", R_(b, n)),
        ("left(c)",  L_(c, n)),
        ("c",        c),
    ]


def run_family(label, ms, n):
    L = sum(ms)
    prod = 1
    for m in ms:
        prod *= m
    thr = 4 * (3 ** (n - 2))
    bins = [p for p in range(n) if ms[p] == 2]
    print(f"\n=== {label}: n={n}, ms={tuple(ms)} ===", flush=True)
    print(f"  product={prod}, threshold={thr}, sub-threshold={prod < thr}", flush=True)
    print(f"  binaries at {bins}, min CL = {L}", flush=True)

    t0 = time.time()
    raw = enumerate_min_length_cycles(list(ms), n)
    t1 = time.time()
    uniq = set(canonical_rotation(w) for w in raw)
    zw = [w for w in uniq if is_zw_cwpos(w, n)]
    print(f"  raw={len(raw)}, unique={len(uniq)}, ZW cw>0={len(zw)} "
          f"(enum {t1 - t0:.1f}s)", flush=True)

    run_count = 0
    failures = 0
    site_bitmap_hist = Counter()
    combo_runs = defaultdict(set)
    tail_kind_total = Counter()
    two_site_covered = 0
    ms_list = list(ms)

    t2 = time.time()
    for w in zw:
        for b, c, interior in binary_pairs(ms_list, n):
            runs = find_gap_runs(w, b, c, interior)
            for (s, e) in runs:
                if not is_oscillatory(w, s, e, n):
                    continue
                own_gap = set(interior)
                run_idx = run_count
                run_count += 1

                per_site = {}
                for lbl, proc in stencil_sites(b, c, n):
                    per_site[lbl] = probe_stencil_at(
                        w, ms_list, n, proc, own_gap, b, c)

                winners = tuple(1 if per_site[lbl] else 0
                                for lbl, _ in stencil_sites(b, c, n))
                site_bitmap_hist[winners] += 1
                if sum(winners) == 0:
                    failures += 1

                if per_site["right(b)"] or per_site["left(c)"]:
                    two_site_covered += 1

                for lbl, _ in stencil_sites(b, c, n):
                    for wit in per_site[lbl]:
                        combo_runs[(lbl, wit['gap_kind'])].add(run_idx)
                        tail_kind_total[wit['gap_kind']] += 1
    t3 = time.time()

    print(f"  Total oscillatory B2B runs: {run_count}", flush=True)
    print(f"  Runs with EMPTY 4-site stencil: {failures}", flush=True)
    print(f"  Runs with >=1 hit at right(b) or left(c): "
          f"{two_site_covered} / {run_count}", flush=True)
    print(f"  Probe time: {t3 - t2:.1f}s", flush=True)
    print(f"  Tail-kind total witness count: {dict(tail_kind_total)}", flush=True)

    labels = [lbl for lbl, _ in stencil_sites(0, 0, n)]
    print(f"  Winning-site bitmap histogram (order: {labels}):", flush=True)
    for bm, cnt in sorted(site_bitmap_hist.items(), key=lambda x: (-x[1], x[0])):
        mask = ''.join('1' if b else '0' for b in bm)
        print(f"    {mask}  x {cnt}", flush=True)

    combo_coverage = [(combo, len(rs)) for combo, rs in combo_runs.items()]
    combo_coverage.sort(key=lambda x: -x[1])
    print(f"  Per-(site, gap_kind) run coverage (top 6):", flush=True)
    for (combo, cnt) in combo_coverage[:6]:
        pct = 100 * cnt / max(1, run_count)
        print(f"    {combo[0]:>10s}  {combo[1]:<13s}  "
              f"{cnt:>6d} / {run_count}  ({pct:5.1f}%)", flush=True)

    # Check the two-site complementary-tail rule:
    rb_comp = len(combo_runs.get(("right(b)", "complementary"), set()))
    lc_comp = len(combo_runs.get(("left(c)", "complementary"), set()))
    union_comp = len(combo_runs.get(("right(b)", "complementary"), set())
                     | combo_runs.get(("left(c)", "complementary"), set()))
    print(f"  TWO-SITE COMPLEMENTARY RULE:", flush=True)
    print(f"    right(b)+comp:                {rb_comp} / {run_count}", flush=True)
    print(f"    left(c)+comp:                 {lc_comp} / {run_count}", flush=True)
    print(f"    union covers:                 {union_comp} / {run_count}", flush=True)
    if union_comp == run_count:
        print(f"    RULE HOLDS: every run has >=1 witness from "
              f"{{right(b), left(c)}} with complementary tail", flush=True)
    else:
        print(f"    RULE FAILS: {run_count - union_comp} runs missed", flush=True)


if __name__ == "__main__":
    families = [
        (11, "n11 all-odd-gap 3bin",  [2, 3, 3, 2, 3, 3, 2, 3, 3, 3, 3]),
        (11, "n11 3-consec-binary",   [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3]),
        (11, "n11 pivot 3bin",        [2, 3, 2, 3, 2, 3, 3, 3, 3, 3, 3]),
        (11, "n11 4-bin spaced",      [2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3]),
    ]
    for n, label, ms in families:
        run_family(label, ms, n)
