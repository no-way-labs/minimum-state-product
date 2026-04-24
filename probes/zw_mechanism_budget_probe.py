#!/usr/bin/env python3
"""
Phase 0c: Mechanism budget probe for the two-site complementary-tail rule.

The previous mechanism probe established that every oscillatory B2B run in
the tested n=9 and n=11 families has a broad provider witness at
`right(b)` or `left(c)` with tail entirely in the complementary adjacent
gap. This probe asks *why*:

- what is the structural shape of each winning witness tail?
- does the tail use the "binary-even" escape (`l_fires = 2`, both b-fires
  in the tail) or the "both-silent" escape (`l_fires = r_fires = 0`)?
- does the full consec-fire interval `(a1, a2)` contain `b`? if so, how
  many times?
- is the winning interval a "complementary excursion" through `b`, or a
  "pure own-gap loop" that trims to a silent tail?
- is there a single structural signature that every winning witness
  satisfies?

If a strict per-witness invariant falls out, that is the proof hook for
the two-site complementary-tail theorem.
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


def count_in_arc(word, start_exclusive, end_exclusive, proc, L):
    """Count occurrences of `proc` on cyclic open interval
    (start_exclusive, end_exclusive)."""
    n_hits = 0
    k = (start_exclusive + 1) % L
    while k != end_exclusive:
        if word[k] == proc:
            n_hits += 1
        k = (k + 1) % L
    return n_hits


def interval_length_open(a1, a2, L):
    """Length of the cyclic open interval (a1, a2)."""
    return (a2 - a1) % L - 1


def probe_winning_witnesses_at(word, ms, n, site_proc, own_gap_interior_set,
                                b, c, site_label):
    """Return list of witness dicts for this site with complementary-tail.
    Each dict records structural shape details."""
    L = len(word)
    i = site_proc
    li = L_(i, n)
    ri = R_(i, n)
    fire_steps = [k for k in range(L) if word[k] == i]
    m = len(fire_steps)
    if m < 2:
        return []

    own_closure = own_gap_interior_set | {b, c}
    results = []
    for idx in range(m):
        a1 = fire_steps[idx]
        a2 = fire_steps[(idx + 1) % m]
        ilen = (a2 - a1) % L
        if ilen <= 1:
            continue
        # Full interval shape
        full_positions = []
        k = (a1 + 1) % L
        while k != a2:
            full_positions.append(word[k])
            k = (k + 1) % L
        full_set = set(full_positions)
        full_b_fires = sum(1 for p in full_positions if p == b)
        full_c_fires = sum(1 for p in full_positions if p == c)
        full_hits_own = bool(full_set & own_gap_interior_set)
        full_hits_comp = bool(full_set - own_closure)
        if full_hits_own and full_hits_comp:
            full_shape = 'mixed'
        elif full_hits_own:
            full_shape = 'own'
        elif full_hits_comp:
            full_shape = 'complementary'
        else:
            # Only {b, c} — degenerate
            full_shape = 'boundary-only'

        # Slide k2 to find winning tails with complementary classification
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
                    tail_kind = 'mixed'
                elif hits_own_int:
                    tail_kind = 'own'
                else:
                    tail_kind = 'complementary'
                if tail_kind == 'complementary':
                    results.append({
                        'site': site_label,
                        'a1': a1, 'a2': a2, 'k2': k2,
                        'interval_len': ilen,
                        'tail_len': len(tail_positions),
                        'l_fires': l_fires,   # fires of li on tail
                        'r_fires': r_fires,   # fires of ri on tail
                        'li': li, 'ri': ri,
                        'li_is_binary': ms[li] == 2,
                        'ri_is_binary': ms[ri] == 2,
                        'full_shape': full_shape,
                        'full_b_fires': full_b_fires,
                        'full_c_fires': full_c_fires,
                    })
            k2 = (k2 + 1) % L
    return results


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

    # Per-witness shape tallies (only winning right(b) / left(c) + complementary)
    shape_counts = Counter()          # (l_fires, r_fires) tallies
    full_shape_counts = Counter()     # full interval shape
    escape_mode_counts = Counter()    # "binary-even" vs "both-silent" vs "mixed-silent"
    tail_len_hist = Counter()
    interval_len_hist = Counter()
    full_contains_b_hist = Counter()  # fires of b in FULL interval (a1, a2)
    ri_is_binary_among_witnesses = Counter()

    total_runs = 0
    per_site_any_witness = Counter()
    ms_list = list(ms)

    for w in zw:
        for b, c, interior in binary_pairs(ms_list, n):
            runs = find_gap_runs(w, b, c, interior)
            for (s, e) in runs:
                if not is_oscillatory(w, s, e, n):
                    continue
                total_runs += 1
                own_gap = set(interior)
                rb_wits = probe_winning_witnesses_at(
                    w, ms_list, n, R_(b, n), own_gap, b, c, "right(b)")
                lc_wits = probe_winning_witnesses_at(
                    w, ms_list, n, L_(c, n), own_gap, b, c, "left(c)")
                for wit in rb_wits + lc_wits:
                    shape_counts[(wit['l_fires'], wit['r_fires'])] += 1
                    full_shape_counts[wit['full_shape']] += 1
                    tail_len_hist[wit['tail_len']] += 1
                    interval_len_hist[wit['interval_len']] += 1
                    # Classify escape mode
                    if wit['l_fires'] > 0 and wit['r_fires'] == 0:
                        mode = 'binary-even-l'
                    elif wit['r_fires'] > 0 and wit['l_fires'] == 0:
                        mode = 'binary-even-r'
                    elif wit['l_fires'] == 0 and wit['r_fires'] == 0:
                        mode = 'both-silent'
                    else:
                        mode = 'both-binary-even'
                    escape_mode_counts[mode] += 1
                    # For right(b) witnesses: b is left(i); for left(c): c is right(i).
                    if wit['site'] == "right(b)":
                        full_contains_b_hist[wit['full_b_fires']] += 1
                    else:  # left(c)
                        full_contains_b_hist[wit['full_c_fires']] += 1
                if rb_wits:
                    per_site_any_witness["right(b)"] += 1
                if lc_wits:
                    per_site_any_witness["left(c)"] += 1

    print(f"  Total oscillatory B2B runs: {total_runs}", flush=True)
    print(f"  Runs with >=1 right(b)+comp witness: "
          f"{per_site_any_witness['right(b)']}", flush=True)
    print(f"  Runs with >=1 left(c)+comp witness:  "
          f"{per_site_any_witness['left(c)']}", flush=True)

    print(f"  (l_fires, r_fires) distribution across winning witnesses:")
    for shape, cnt in sorted(shape_counts.items(), key=lambda x: -x[1]):
        print(f"    {shape}  x {cnt}", flush=True)

    print(f"  Escape mode distribution:", flush=True)
    for mode, cnt in sorted(escape_mode_counts.items(), key=lambda x: -x[1]):
        print(f"    {mode}  x {cnt}", flush=True)

    print(f"  Full-interval shape (a1, a2) distribution:", flush=True)
    for sh, cnt in sorted(full_shape_counts.items(), key=lambda x: -x[1]):
        print(f"    {sh}  x {cnt}", flush=True)

    print(f"  Full interval b-fires (for right(b)) / c-fires (for left(c)):",
          flush=True)
    for bc_fires, cnt in sorted(full_contains_b_hist.items()):
        print(f"    boundary-binary fires in full (a1, a2) = {bc_fires}  x {cnt}",
              flush=True)

    print(f"  Tail-length histogram (top 8): "
          f"{dict(tail_len_hist.most_common(8))}", flush=True)
    print(f"  Interval-length histogram (top 8): "
          f"{dict(interval_len_hist.most_common(8))}", flush=True)


if __name__ == "__main__":
    families = [
        (9,  "n9  all-odd-gap",        [2, 3, 3, 2, 3, 3, 2, 3, 3]),
        (9,  "n9  3-consec-binary",    [2, 2, 2, 3, 3, 3, 3, 3, 3]),
        (9,  "n9  pivot alt",          [2, 3, 2, 3, 2, 3, 3, 3, 3]),
        (9,  "n9  3-all-spaced",       [2, 3, 3, 3, 2, 3, 3, 3, 2]),
        (11, "n11 all-odd-gap",        [2, 3, 3, 2, 3, 3, 2, 3, 3, 3, 3]),
        (11, "n11 3-consec-binary",    [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3]),
        (11, "n11 pivot 3bin",         [2, 3, 2, 3, 2, 3, 3, 3, 3, 3, 3]),
    ]
    for n, label, ms in families:
        run_family(label, ms, n)
