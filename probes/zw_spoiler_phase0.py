#!/usr/bin/env python3
"""
Phase 0: Four-way spoiler search for the ZW provider bracketing theorem.

Targets the sharpest failure mode isolated in §6 of
  docs/lean_docs/lb_campaign_2026-04-12/
    zw_provider_gap_oscillation_pa_spec_2026-04-12.md

Candidate theorem (§1): for every oscillatory no-self-return boundary-to-
boundary gap run between ring-consecutive binaries b and c, there exists a
processor i in {left(b), right(b), left(c), right(c)} with a consecutive-
fire interval (a1, a2) cyclically containing the whole gap run, such that
after the last f-fire in (a1, a2) there are at least two d-fires before a2,
where d = the binary side of i (b or c) and f = the opposite neighbor of i.
That yields the exact 0/2 provider on [k2, a2).

A cycle is "four-way spoiled" iff it has an oscillatory no-self-return
boundary-to-boundary gap run for which NONE of the four candidates admits a
valid bracketing interval. Phase 0 is a positive signal for Phase 1 iff no
four-way-spoiled cycle is found.

Scope: minimum-length ZW cw>0 good cycles at n=9 across four representative
sub-threshold >=3-binary families (plus an n=5 sanity family). These are
the same multisets sampled in the spec's §Purpose.
"""

import time
from collections import Counter


def L_(p, n): return (p - 1) % n
def R_(p, n): return (p + 1) % n


def enumerate_min_length_cycles(ms, n):
    """All cyclic mover words of length L = sum(ms) that form good cycles:
      - each proc fires exactly m_p times
      - each transition (including wrap) is L / stay / R
      - starts/ends at config (0,...,0) with all L intermediate configs distinct
    Canonicalised by word[0] = 0 (each rotation-class produces fc[0] raw hits,
    deduplicated downstream via canonical_rotation)."""
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
            # Config distinctness: only reject re-entry to a non-start config.
            # Re-entry to start_cfg is only valid on the final step (plen == L - 1).
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
    """Zero net winding with at least one cw step. Stay transitions
    (word[k+1]==word[k]) count as neither cw nor ccw. ZW means
    cw_count == ccw_count."""
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


def gap_interior(b, c, n):
    out = []
    k = R_(b, n)
    steps = 0
    while k != c and steps < n:
        out.append(k)
        k = R_(k, n)
        steps += 1
    return out


def binary_pairs(ms, n):
    bins = [p for p in range(n) if ms[p] == 2]
    pairs = []
    for idx, b in enumerate(bins):
        c = bins[(idx + 1) % len(bins)]
        interior = gap_interior(b, c, n)
        if len(interior) >= 1:
            pairs.append((b, c, frozenset(interior)))
    return pairs


def find_gap_runs(word, b, c, interior):
    """Maximal gap runs from b to c: word[s]=b, word[e]=c, all steps strictly
    between in gap_interior. Self-return runs (those that return to b before
    reaching c) are automatically excluded by the interior-only condition."""
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
    """True iff the gap run walk from step s to step e has both a cw and a
    ccw transition. Stay transitions (word[k+1]==word[k]) are ignored."""
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
        # stay: ignore
        if has_cw and has_ccw:
            return True
        k = nxt
        steps += 1
    return has_cw and has_ccw


def interval_strictly_contains(a1, a2, s, e, L):
    """Open cyclic interval (a1, a2) strictly contains segment [s, e] (cw)."""
    oa2 = (a2 - a1) % L
    if oa2 == 0:
        return False
    os_ = (s - a1) % L
    oe = (e - a1) % L
    return 0 < os_ < oa2 and 0 < oe < oa2 and os_ <= oe


def candidate_bracketing_ok(word, i, d, f, s_run, e_run):
    """A consecutive-fire pair (a1, a2) of i strictly contains the gap run
    and admits k2 ∈ (a1, a2) with f-count=0 and d-count=2 on [k2, a2)."""
    L = len(word)
    fire_steps = [k for k in range(L) if word[k] == i]
    m = len(fire_steps)
    if m < 2:
        return False
    for idx in range(m):
        a1 = fire_steps[idx]
        a2 = fire_steps[(idx + 1) % m]
        if not interval_strictly_contains(a1, a2, s_run, e_run, L):
            continue
        d_fires = []
        f_fires = []
        k = (a1 + 1) % L
        while k != a2:
            if word[k] == d:
                d_fires.append(k)
            elif word[k] == f:
                f_fires.append(k)
            k = (k + 1) % L
        if len(d_fires) < 2:
            continue
        if not f_fires:
            return True
        last_f = f_fires[-1]
        def off(x): return (x - (a1 + 1)) % L
        last_f_off = off(last_f)
        d_after = sum(1 for x in d_fires if off(x) > last_f_off)
        if d_after >= 2:
            return True
    return False


def broad_provider_exists_anywhere(word, ms, n):
    """Matches the check in zw_provider_ec_final.py: does ANY proc i have
    a consec-fire pair (a1, a2) and k2 in (a1, a2) with word[k2] != i such
    that on [k2, a2), the left/right neighbours each have 0 fires OR
    (ms==2 and fire count even)? This is the broad theorem boundary for
    provider_interval_exists_zw. Returns (ok, i, a1, a2, k2)."""
    L = len(word)
    for i in range(n):
        li = L_(i, n)
        ri = R_(i, n)
        fire_steps = [k for k in range(L) if word[k] == i]
        m = len(fire_steps)
        if m < 2:
            continue
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
                l_fires = r_fires = 0
                k = k2
                while k != a2:
                    if word[k] == li:
                        l_fires += 1
                    elif word[k] == ri:
                        r_fires += 1
                    k = (k + 1) % L
                l_ok = (l_fires == 0) or (ms[li] == 2 and l_fires % 2 == 0)
                r_ok = (r_fires == 0) or (ms[ri] == 2 and r_fires % 2 == 0)
                if l_ok and r_ok:
                    return True, i, a1, a2, k2
                k2 = (k2 + 1) % L
    return False, -1, -1, -1, -1


def broad_provider_exists_enclosing(word, ms, n, s_run, e_run):
    """Same as broad_provider_exists_anywhere but additionally requires
    the consec-fire interval (a1, a2) to strictly enclose [s_run, e_run].
    This is the strictly-refined condition from the gap-oscillation spec
    §1 but WITHOUT restricting i to the four boundary-adjacent sites."""
    L = len(word)
    for i in range(n):
        li = L_(i, n)
        ri = R_(i, n)
        fire_steps = [k for k in range(L) if word[k] == i]
        m = len(fire_steps)
        if m < 2:
            continue
        for idx in range(m):
            a1 = fire_steps[idx]
            a2 = fire_steps[(idx + 1) % m]
            if not interval_strictly_contains(a1, a2, s_run, e_run, L):
                continue
            k2 = (a1 + 1) % L
            while k2 != a2:
                if word[k2] == i:
                    k2 = (k2 + 1) % L
                    continue
                l_fires = r_fires = 0
                k = k2
                while k != a2:
                    if word[k] == li:
                        l_fires += 1
                    elif word[k] == ri:
                        r_fires += 1
                    k = (k + 1) % L
                l_ok = (l_fires == 0) or (ms[li] == 2 and l_fires % 2 == 0)
                r_ok = (r_fires == 0) or (ms[ri] == 2 and r_fires % 2 == 0)
                if l_ok and r_ok:
                    return True, i
                k2 = (k2 + 1) % L
    return False, -1


def check_cycle(word, ms, n, do_broad=False):
    """Return [(b, c, s, e, good_candidates, spoiled_candidates, broad_ok, broad_i), ...]
    over all oscillatory no-self-return boundary-to-boundary gap runs."""
    records = []
    for b, c, interior in binary_pairs(ms, n):
        for (s, e) in find_gap_runs(word, b, c, interior):
            if not is_oscillatory(word, s, e, n):
                continue
            cand = [
                (L_(b, n), b, L_(L_(b, n), n)),
                (R_(b, n), b, R_(R_(b, n), n)),
                (L_(c, n), c, L_(L_(c, n), n)),
                (R_(c, n), c, R_(R_(c, n), n)),
            ]
            good, spoiled = [], []
            for (i, d, f) in cand:
                if candidate_bracketing_ok(word, i, d, f, s, e):
                    good.append(i)
                else:
                    spoiled.append(i)
            broad_ok, broad_i = (False, -1)
            if do_broad and len(good) == 0:
                broad_ok, broad_i = broad_provider_exists_enclosing(word, ms, n, s, e)
            records.append((b, c, s, e, tuple(good), tuple(spoiled), broad_ok, broad_i))
    return records


def run_family(label, ms, n):
    L = sum(ms)
    prod = 1
    for m in ms:
        prod *= m
    thr = 4 * (3 ** (n - 2))
    bins = [p for p in range(n) if ms[p] == 2]
    print(f"\n=== {label}: n={n}, ms={tuple(ms)} ===")
    print(f"  product={prod}, threshold={thr}, sub-threshold={prod < thr}")
    print(f"  binaries at {bins}, min CL = {L}")

    t0 = time.time()
    raw = enumerate_min_length_cycles(list(ms), n)
    t1 = time.time()

    uniq = set(canonical_rotation(w) for w in raw)
    print(f"  Enumerated {len(raw)} raw / {len(uniq)} unique cycles in {t1 - t0:.1f}s")

    zw = [w for w in uniq if is_zw_cwpos(w, n)]
    print(f"  ZW cw>0 cycles: {len(zw)}")

    # Cycle-level broad provider health (matches zw_provider_ec_final.py):
    # does ANY processor anywhere admit a provider interval with preserved
    # context on the tail? This is the baseline for provider_interval_exists_zw.
    t_b = time.time()
    cycles_with_broad_provider = 0
    cycles_without_broad_provider = 0
    broad_failures = []
    for w in zw:
        ok, *_ = broad_provider_exists_anywhere(w, list(ms), n)
        if ok:
            cycles_with_broad_provider += 1
        else:
            cycles_without_broad_provider += 1
            broad_failures.append(w)
    print(f"  Cycle-level broad provider (any i, any interval): "
          f"{cycles_with_broad_provider}/{len(zw)} cover, "
          f"{cycles_without_broad_provider} fail "
          f"({time.time() - t_b:.1f}s)")
    if broad_failures:
        print(f"  === CYCLE-LEVEL BROAD-PROVIDER FAILURES ({len(broad_failures)}) ===")
        for w in broad_failures:
            fc_list = [sum(1 for k in range(len(w)) if w[k] == p) for p in range(n)]
            print(f"    word={w}")
            print(f"    fc={fc_list}")

    osc_total = 0
    cycles_with_osc = 0
    four_way_spoil_runs = 0
    cycles_with_spoil = 0
    broad_ok_spoiled_runs = 0
    broad_fail_runs = 0
    good_hist = Counter()
    examples = []
    broad_fail_examples = []

    t2 = time.time()
    for w in zw:
        recs = check_cycle(w, list(ms), n, do_broad=True)
        if recs:
            cycles_with_osc += 1
        has_spoil = False
        for (b, c, s, e, good, spoiled, broad_ok, broad_i) in recs:
            osc_total += 1
            good_hist[len(good)] += 1
            if len(good) == 0:
                four_way_spoil_runs += 1
                has_spoil = True
                if broad_ok:
                    broad_ok_spoiled_runs += 1
                else:
                    broad_fail_runs += 1
                    if len(broad_fail_examples) < 3:
                        broad_fail_examples.append((w, b, c, s, e))
                if len(examples) < 3:
                    examples.append((w, b, c, s, e, broad_ok, broad_i))
        if has_spoil:
            cycles_with_spoil += 1
    t3 = time.time()

    print(f"  Cycles with >=1 oscillatory B2B gap run: {cycles_with_osc}")
    print(f"  Total oscillatory B2B gap runs: {osc_total}")
    print(f"  Good-candidate histogram (# good per run): {dict(sorted(good_hist.items()))}")
    print(f"  Four-way spoiled runs: {four_way_spoil_runs}")
    print(f"    of which broad provider (any i) exists: {broad_ok_spoiled_runs}")
    print(f"    of which broad provider also fails:      {broad_fail_runs}")
    print(f"  Cycles with a four-way spoiled run: {cycles_with_spoil}")
    print(f"  Spoiler scan: {t3 - t2:.1f}s")
    if examples:
        print(f"  === 4-SITE SPOILER EXAMPLES ===")
        for (w, b, c, s, e, broad_ok, broad_i) in examples:
            tag = f"broad OK at i={broad_i}" if broad_ok else "BROAD PROVIDER ALSO FAILS"
            print(f"    word={w}")
            print(f"    b={b}, c={c}, run=[s={s}, e={e}] -> {tag}")
    if broad_fail_examples:
        print(f"  === BROAD PROVIDER FAILS (serious) ===")
        for (w, b, c, s, e) in broad_fail_examples:
            print(f"    word={w}  b={b}, c={c}, run=[s={s}, e={e}]")
    if four_way_spoil_runs == 0:
        print(f"  === no four-way spoiler found ===")


if __name__ == "__main__":
    families = [
        (5, "n5 sanity (2,2,3,2,3)",    [2, 2, 3, 2, 3]),
        (9, "all-odd-gap",              [2, 3, 3, 2, 3, 3, 2, 3, 3]),
        (9, "3-consec-binary",          [2, 2, 2, 3, 3, 3, 3, 3, 3]),
        (9, "pivot alt",                [2, 3, 2, 3, 2, 3, 3, 3, 3]),
        (9, "3-all-spaced",             [2, 3, 3, 3, 2, 3, 3, 3, 2]),
    ]
    for n, label, ms in families:
        run_family(label, ms, n)
