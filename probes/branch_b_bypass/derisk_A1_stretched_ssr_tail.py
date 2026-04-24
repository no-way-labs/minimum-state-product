#!/usr/bin/env python3
"""
Candidate A1 derisking probe.

Question:
  Does every stretched self-return (two consecutive monotone B2B traversals of
  the same binary gap sharing a boundary endpoint) admit a `right(b)` or
  `left(c)` consecutive-fire interval with complementary exact tail `(2, 0)` or
  `(0, 2)`?

Search boundary:
  - same min-CL cycle population used by the earlier complementary-tail probes
  - representative n=9 / n=11 sub-threshold >=3-binary families

This is search guidance only.
"""

import time


def L_(p, n):
    return (p - 1) % n


def R_(p, n):
    return (p + 1) % n


def enumerate_min_length_cycles(ms, n):
    length = sum(ms)
    start_cfg = tuple([0] * n)
    results = []

    def dfs(word, fc, config, visited):
        plen = len(word)
        if plen == length:
            first, last = word[0], word[-1]
            if first != R_(last, n) and first != L_(last, n) and first != last:
                return
            if config != start_cfg:
                return
            if not all(fc[p] == ms[p] for p in range(n)):
                return
            results.append(tuple(word))
            return
        remaining = length - plen
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
                if not (nc_t == start_cfg and plen == length - 1):
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
    cw = ccw = 0
    for k in range(len(word)):
        nxt = word[(k + 1) % len(word)]
        if nxt == R_(word[k], n):
            cw += 1
        elif nxt == L_(word[k], n):
            ccw += 1
    return cw == ccw and cw > 0


def canonical_rotation(word):
    return min(word[i:] + word[:i] for i in range(len(word)))


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
            pairs.append((b, c, tuple(interior)))
    return pairs


def is_monotone_subrun(word, s, e, n, direction):
    k = s
    saw_move = False
    steps = 0
    while k != e and steps <= len(word):
        nxt = (k + 1) % len(word)
        if word[nxt] == word[k]:
            pass
        elif direction == "cw" and word[nxt] == R_(word[k], n):
            saw_move = True
        elif direction == "ccw" and word[nxt] == L_(word[k], n):
            saw_move = True
        else:
            return False
        k = nxt
        steps += 1
    return saw_move


def find_monotone_gap_runs(word, b, c, interior, n):
    interior_set = set(interior)
    runs = []
    length = len(word)
    for start, end, direction in ((b, c, "cw"), (c, b, "ccw")):
        for s in range(length):
            if word[s] != start:
                continue
            k = (s + 1) % length
            if word[k] not in interior_set:
                continue
            steps = 0
            while word[k] in interior_set:
                k = (k + 1) % length
                steps += 1
                if steps > length:
                    break
            if steps > length or word[k] != end:
                continue
            if is_monotone_subrun(word, s, k, n, direction):
                runs.append(
                    {
                        "s": s,
                        "e": k,
                        "start": start,
                        "end": end,
                        "direction": direction,
                    }
                )
    return runs


def find_stretched_ssr_pairs(word, b, c, interior, n):
    interior_set = set(interior)
    runs = find_monotone_gap_runs(word, b, c, interior, n)
    pairs = []
    seen = set()
    length = len(word)

    for run in runs:
        shared = run["end"]
        expected_end = run["start"]
        opposite_dir = "ccw" if run["direction"] == "cw" else "cw"

        t = (run["e"] + 1) % length
        steps = 0
        while steps < length and word[t] == shared:
            t = (t + 1) % length
            steps += 1
        if steps >= length:
            continue
        if word[t] not in interior_set:
            continue

        s2 = (t - 1) % length
        k = t
        inner_steps = 0
        while word[k] in interior_set:
            k = (k + 1) % length
            inner_steps += 1
            if inner_steps > length:
                break
        if inner_steps > length or word[k] != expected_end:
            continue
        if not is_monotone_subrun(word, s2, k, n, opposite_dir):
            continue

        key = (run["s"], run["e"], s2, k, b, c)
        if key in seen:
            continue
        seen.add(key)
        pairs.append(
            {
                "first": run,
                "second": {
                    "s": s2,
                    "e": k,
                    "start": shared,
                    "end": expected_end,
                    "direction": opposite_dir,
                },
                "shared": shared,
            }
        )
    return pairs


def find_exact_complementary_tail(word, ms, n, site, b, c, interior, expected_shape):
    own_gap = set(interior)
    own_closure = own_gap | {b, c}
    li = L_(site, n)
    ri = R_(site, n)
    fire_steps = [k for k in range(len(word)) if word[k] == site]
    if len(fire_steps) < 2:
        return None

    for idx in range(len(fire_steps)):
        a1 = fire_steps[idx]
        a2 = fire_steps[(idx + 1) % len(fire_steps)]
        if (a2 - a1) % len(word) <= 1:
            continue
        k2 = (a1 + 1) % len(word)
        while k2 != a2:
            if word[k2] == site:
                k2 = (k2 + 1) % len(word)
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
                k = (k + 1) % len(word)

            tail_set = set(tail_positions)
            complementary = not bool(tail_set & own_gap)
            if complementary and (l_fires, r_fires) == expected_shape:
                return {
                    "site": site,
                    "a1": a1,
                    "a2": a2,
                    "k2": k2,
                    "shape": (l_fires, r_fires),
                    "touches_outside_gap": bool(tail_set - own_closure),
                }
            k2 = (k2 + 1) % len(word)
    return None


def find_two_site_provider(word, ms, n, b, c, interior):
    rb = R_(b, n)
    lc = L_(c, n)
    rb_wit = find_exact_complementary_tail(word, ms, n, rb, b, c, interior, (2, 0))
    if rb_wit is not None:
        return rb_wit
    lc_wit = find_exact_complementary_tail(word, ms, n, lc, b, c, interior, (0, 2))
    return lc_wit


def run_family(n, label, ms):
    t0 = time.time()
    raw = enumerate_min_length_cycles(list(ms), n)
    uniq = set(canonical_rotation(w) for w in raw)
    zw = [w for w in uniq if is_zw_cwpos(w, n)]
    elapsed = time.time() - t0

    total_pairs = 0
    covered_pairs = 0
    failures = []
    for word in zw:
        for b, c, interior in binary_pairs(ms, n):
            pairs = find_stretched_ssr_pairs(word, b, c, interior, n)
            for pair in pairs:
                total_pairs += 1
                witness = find_two_site_provider(word, ms, n, b, c, interior)
                if witness is not None:
                    covered_pairs += 1
                elif len(failures) < 3:
                    failures.append(
                        {
                            "word": word,
                            "b": b,
                            "c": c,
                            "first": pair["first"],
                            "second": pair["second"],
                            "shared": pair["shared"],
                        }
                    )

    return {
        "label": label,
        "ms": tuple(ms),
        "raw_cycles": len(raw),
        "unique_cycles": len(uniq),
        "zw_cycles": len(zw),
        "elapsed": elapsed,
        "stretched_ssr_count": total_pairs,
        "covered_count": covered_pairs,
        "failures": failures,
    }


def main():
    families = [
        (9, "n9 all-odd-gap", [2, 3, 3, 2, 3, 3, 2, 3, 3]),
        (9, "n9 3-consec-binary", [2, 2, 2, 3, 3, 3, 3, 3, 3]),
        (9, "n9 pivot alt", [2, 3, 2, 3, 2, 3, 3, 3, 3]),
        (9, "n9 3-all-spaced", [2, 3, 3, 3, 2, 3, 3, 3, 2]),
        (11, "n11 all-odd-gap", [2, 3, 3, 2, 3, 3, 2, 3, 3, 3, 3]),
        (11, "n11 3-consec-binary", [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3]),
        (11, "n11 pivot 3bin", [2, 3, 2, 3, 2, 3, 3, 3, 3, 3, 3]),
    ]

    grand_total = 0
    grand_covered = 0
    failed_families = []

    for n, label, ms in families:
        result = run_family(n, label, ms)
        grand_total += result["stretched_ssr_count"]
        grand_covered += result["covered_count"]
        if result["stretched_ssr_count"] != result["covered_count"]:
            failed_families.append(result["label"])

        print(f"\n=== {result['label']} ===", flush=True)
        print(f"ms={result['ms']}", flush=True)
        print(
            f"raw={result['raw_cycles']} unique={result['unique_cycles']} "
            f"ZW cw>0={result['zw_cycles']} enum={result['elapsed']:.1f}s",
            flush=True,
        )
        print(
            f"stretched_ssr={result['stretched_ssr_count']} "
            f"covered={result['covered_count']}",
            flush=True,
        )
        if result["failures"]:
            print("counterexamples:", flush=True)
            for fail in result["failures"]:
                print(f"  word={fail['word']}", flush=True)
                print(
                    f"  gap=({fail['b']},{fail['c']}) shared={fail['shared']} "
                    f"first={fail['first']} second={fail['second']}",
                    flush=True,
                )

    rate = 1.0 if grand_total == 0 else grand_covered / grand_total
    print("\n=== SUMMARY ===", flush=True)
    print(f"tested_families={[label for _, label, _ in families]}", flush=True)
    print(f"stretched_ssr_count={grand_total}", flush=True)
    print(f"covered_count={grand_covered}", flush=True)
    print(f"coverage_rate={rate:.6f}", flush=True)
    print(f"failed_families={failed_families}", flush=True)


if __name__ == "__main__":
    main()
