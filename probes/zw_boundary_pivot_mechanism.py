#!/usr/bin/env python3
"""
Phase 0b: Boundary-pivot stencil mechanism probe.

Target: the live candidate theorem from
  docs/lean_docs/lb_campaign_2026-04-12/
    zw_provider_boundary_pivot_phase0_2026-04-12.md

The note claims:
  every oscillatory B2B gap run has >=1 stencil site in
  {b, right(b), left(c), c} that admits a broad provider interval.

Empirically 0 failures on 10,465 runs across 6 n=9 families. This probe
asks the *mechanism* question: is there a deterministic rule
(site, gap_kind) that always wins? Or is the winning witness scattered
across sites and adjacent gaps?

For each oscillatory run, we:
1. test all 4 stencil sites for a broad provider (no enclosing
   requirement — the theorem candidate is run-level, not interval-level);
2. for each successful (site, a1, a2, k2), classify the tail [k2, a2):
   - `own`           : tail stays inside own-gap closure {b, c} ∪ interior
   - `complementary` : tail does not touch own-gap interior at all
   - `mixed`         : tail straddles both (only possible when one end is
                        near b or c)
3. collect (site, gap_kind) combinations per run.

We then aggregate per family:
- which stencil sites win on each run (bitmap over 4 sites),
- which (site, gap_kind) combos win on each run,
- the minimum number of (site, gap_kind) combos needed to cover every run
  (deterministic if 1, near-deterministic if 2, scattered if >2).

Script is standalone (copies the enumerator and primitives from
zw_spoiler_phase0.py).
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
    """All successful (a1, a2, k2) witnesses for a broad provider at
    site_proc, each with gap_kind classification of the tail."""
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


def probe_run(word, ms, n, b, c):
    own_gap = set(gap_interior_cw(b, c, n))
    per_site = {}
    for label, proc in stencil_sites(b, c, n):
        per_site[label] = probe_stencil_at(word, ms, n, proc, own_gap, b, c)
    return per_site


def run_family(label, ms, n):
    L = sum(ms)
    prod = 1
    for m in ms:
        prod *= m
    thr = 4 * (3 ** (n - 2))
    print(f"\n=== {label}: n={n}, ms={tuple(ms)} ===")
    print(f"  product={prod}, threshold={thr}, sub-threshold={prod < thr}")
    print(f"  binaries at {[p for p in range(n) if ms[p] == 2]}, min CL = {L}")

    t0 = time.time()
    raw = enumerate_min_length_cycles(list(ms), n)
    uniq = set(canonical_rotation(w) for w in raw)
    t1 = time.time()
    zw = [w for w in uniq if is_zw_cwpos(w, n)]
    print(f"  ZW cw>0 unique cycles: {len(zw)} (enum {t1 - t0:.1f}s)")

    # Per-run aggregates
    run_count = 0
    failures = 0  # runs with empty stencil — should always be 0
    # Site-bitmap histogram (which subset of 4 sites won, regardless of gap)
    site_bitmap_hist = Counter()
    # (site, gap_kind) combo coverage per run — a run "contains" a combo if
    # any successful witness matched it
    combo_runs = defaultdict(set)  # combo -> set of run indices that contain it
    # Also: for each run, the set of combos it contains
    run_combos = []

    t2 = time.time()
    for w in zw:
        for b, c, interior in binary_pairs(list(ms), n):
            runs = find_gap_runs(w, b, c, interior)
            for (s, e) in runs:
                if not is_oscillatory(w, s, e, n):
                    continue
                per_site = probe_run(w, list(ms), n, b, c)
                run_idx = run_count
                run_count += 1

                # Build site bitmap
                winners = tuple(1 if per_site[lbl] else 0
                                for lbl, _ in stencil_sites(b, c, n))
                site_bitmap_hist[winners] += 1
                if sum(winners) == 0:
                    failures += 1

                # Collect (site, gap_kind) combos present in this run
                combos_here = set()
                for lbl, _ in stencil_sites(b, c, n):
                    for wit in per_site[lbl]:
                        combos_here.add((lbl, wit['gap_kind']))
                run_combos.append(combos_here)
                for combo in combos_here:
                    combo_runs[combo].add(run_idx)
    t3 = time.time()

    print(f"  Total oscillatory B2B runs: {run_count}")
    print(f"  Runs with EMPTY stencil (failures): {failures}")
    print(f"  Probe time: {t3 - t2:.1f}s")

    # Site-bitmap histogram (labelled)
    labels = [lbl for lbl, _ in stencil_sites(0, 0, n)]
    print(f"  Winning-site bitmap histogram (order: {labels}):")
    for bm, cnt in sorted(site_bitmap_hist.items(), key=lambda x: (-x[1], x[0])):
        mask = ''.join('1' if b else '0' for b in bm)
        print(f"    {mask}  x {cnt}")

    # Per-(site, gap_kind) coverage
    print(f"  Per-(site, gap_kind) run coverage (runs where >=1 witness of that kind exists):")
    combo_coverage = [(combo, len(rs)) for combo, rs in combo_runs.items()]
    combo_coverage.sort(key=lambda x: -x[1])
    for (combo, cnt) in combo_coverage:
        pct = 100 * cnt / max(1, run_count)
        print(f"    {combo[0]:>10s}  {combo[1]:<13s}  {cnt:>5d} / {run_count}  ({pct:5.1f}%)")

    # Deterministic rule check
    # Is there a single combo that covers 100% of runs?
    full = [c for (c, cnt) in combo_coverage if cnt == run_count]
    if full:
        print(f"  DETERMINISTIC: single combo covers all {run_count} runs: {full}")
    else:
        # Greedy set cover
        uncovered = set(range(run_count))
        chosen = []
        while uncovered and combo_coverage:
            best = max(combo_runs.items(), key=lambda kv: len(kv[1] & uncovered))
            if not (best[1] & uncovered):
                break
            chosen.append((best[0], len(best[1] & uncovered)))
            uncovered -= best[1]
            # Remove best from consideration
            del combo_runs[best[0]]
        print(f"  NOT single-combo deterministic. Greedy cover:")
        for combo, cnt in chosen:
            print(f"    {combo[0]:>10s}  {combo[1]:<13s}  covers {cnt} runs")
        if uncovered:
            print(f"  WARNING: {len(uncovered)} runs uncovered by any combo (bug?)")


if __name__ == "__main__":
    families = [
        (9, "all-odd-gap",        [2, 3, 3, 2, 3, 3, 2, 3, 3]),
        (9, "3-consec-binary",    [2, 2, 2, 3, 3, 3, 3, 3, 3]),
        (9, "pivot alt",          [2, 3, 2, 3, 2, 3, 3, 3, 3]),
        (9, "3-all-spaced",       [2, 3, 3, 3, 2, 3, 3, 3, 2]),
        (9, "gap-(2,3,4)",        [2, 3, 2, 3, 3, 2, 3, 3, 3]),
        (9, "4-bin alternating",  [2, 3, 2, 3, 2, 3, 2, 3, 3]),
    ]
    for n, label, ms in families:
        run_family(label, ms, n)
