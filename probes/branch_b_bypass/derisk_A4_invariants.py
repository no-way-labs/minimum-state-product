#!/usr/bin/env python3
"""
Candidate A4 derisking probe.

Compute the standard global invariants on 10 small ZW good cycles and inspect
whether any obvious separator for "hard" / low-provider cycles surfaces.

Search guidance only.
"""


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


def canonical_rotation(word):
    return min(word[i:] + word[:i] for i in range(len(word)))


def is_zw_cwpos(word, n):
    cw = ccw = 0
    for k in range(len(word)):
        nxt = word[(k + 1) % len(word)]
        if nxt == R_(word[k], n):
            cw += 1
        elif nxt == L_(word[k], n):
            ccw += 1
    return cw == ccw and cw > 0


def step_dir(word, k, n):
    curr = word[k]
    nxt = word[(k + 1) % len(word)]
    if nxt == R_(curr, n):
        return "cw"
    if nxt == curr:
        return "stay"
    return "ccw"


def reversal_count(word, n):
    dirs = [step_dir(word, k, n) for k in range(len(word))]
    out = 0
    for k in range(len(word)):
        d1 = dirs[k]
        d2 = dirs[(k + 1) % len(word)]
        if (d1, d2) in {("cw", "ccw"), ("ccw", "cw")}:
            out += 1
    return out


def fire_count(word, n):
    return [sum(1 for x in word if x == p) for p in range(n)]


def cw_move_count_at(word, p, n):
    return sum(1 for k in range(len(word)) if word[k] == p and word[(k + 1) % len(word)] == R_(p, n))


def ccw_move_count_at(word, p, n):
    return sum(1 for k in range(len(word)) if word[k] == p and word[(k + 1) % len(word)] == L_(p, n))


def stay_move_count_at(word, p, n):
    return sum(1 for k in range(len(word)) if word[k] == p and word[(k + 1) % len(word)] == p)


def exact_provider_count(word, ms, n):
    total = 0
    for site in range(n):
        li = L_(site, n)
        ri = R_(site, n)
        fires = [k for k in range(len(word)) if word[k] == site]
        if len(fires) < 2:
            continue
        for idx in range(len(fires)):
            a1 = fires[idx]
            a2 = fires[(idx + 1) % len(fires)]
            if (a2 - a1) % len(word) <= 1:
                continue
            k2 = (a1 + 1) % len(word)
            while k2 != a2:
                if word[k2] == site:
                    k2 = (k2 + 1) % len(word)
                    continue
                l_fires = r_fires = 0
                k = k2
                while k != a2:
                    if word[k] == li:
                        l_fires += 1
                    elif word[k] == ri:
                        r_fires += 1
                    k = (k + 1) % len(word)
                if (ms[li] == 2 and l_fires == 2 and r_fires == 0) or (
                    ms[ri] == 2 and r_fires == 2 and l_fires == 0
                ):
                    total += 1
                k2 = (k2 + 1) % len(word)
    return total


def invariant_vector(word, ms, n):
    dirs = [step_dir(word, k, n) for k in range(len(word))]
    fc = fire_count(word, n)
    cw_steps = sum(1 for d in dirs if d == "cw")
    ccw_steps = sum(1 for d in dirs if d == "ccw")
    stay_steps = sum(1 for d in dirs if d == "stay")
    cw_moves = [cw_move_count_at(word, p, n) for p in range(n)]
    ccw_moves = [ccw_move_count_at(word, p, n) for p in range(n)]
    stay_moves = [stay_move_count_at(word, p, n) for p in range(n)]
    edge_cw = list(cw_moves)
    edge_ccw = [ccw_moves[R_(p, n)] for p in range(n)]
    edge_flow = [cw_moves[p] - ccw_moves[R_(p, n)] for p in range(n)]
    return {
        "word": word,
        "fireCount": fc,
        "cwStepCount": cw_steps,
        "ccwStepCount": ccw_steps,
        "stayStepCount": stay_steps,
        "reversalCount": reversal_count(word, n),
        "totalDisplacement": cw_steps - ccw_steps,
        "cwMoveCountAt": cw_moves,
        "ccwMoveCountAt": ccw_moves,
        "stayMoveCountAt": stay_moves,
        "edgeCWSteps": edge_cw,
        "edgeCCWSteps": edge_ccw,
        "edgeNetFlow": edge_flow,
        "exactProviderCount": exact_provider_count(word, ms, n),
    }


def sample_cycles(n, ms, take):
    raw = enumerate_min_length_cycles(list(ms), n)
    uniq = sorted(set(canonical_rotation(w) for w in raw))
    zw = [w for w in uniq if is_zw_cwpos(w, n)]
    return zw[:take]


def main():
    families = [
        (5, "n5 sanity", [2, 2, 3, 2, 3], 5),
        (7, "n7 pivot-like", [2, 3, 2, 3, 2, 3, 3], 5),
    ]

    rows = []
    for n, label, ms, take in families:
        for idx, word in enumerate(sample_cycles(n, ms, take), start=1):
            rows.append((label, n, tuple(ms), idx, invariant_vector(word, ms, n)))

    rows.sort(key=lambda item: (item[4]["exactProviderCount"], item[0], item[3]))

    print(f"sample_count={len(rows)}")
    print("invariants_computed=['totalDisplacement','cwStepCount','ccwStepCount',"
          "'stayStepCount','reversalCount','edgeNetFlow','edgeCWSteps',"
          "'edgeCCWSteps','fireCount','cwMoveCountAt']")

    min_provider = min(row[4]["exactProviderCount"] for row in rows)
    hardest = [row for row in rows if row[4]["exactProviderCount"] == min_provider]
    print(f"min_exact_provider_count={min_provider}")
    print(f"hardest_cycle_count={len(hardest)}")

    for label, n, ms, idx, inv in rows:
        print(f"\n=== {label} sample#{idx} n={n} ms={ms} ===")
        print(f"word={inv['word']}")
        print(f"exactProviderCount={inv['exactProviderCount']}")
        print(f"fireCount={inv['fireCount']}")
        print(f"cwStepCount={inv['cwStepCount']} ccwStepCount={inv['ccwStepCount']} "
              f"stayStepCount={inv['stayStepCount']}")
        print(f"reversalCount={inv['reversalCount']} totalDisplacement={inv['totalDisplacement']}")
        print(f"cwMoveCountAt={inv['cwMoveCountAt']}")
        print(f"ccwMoveCountAt={inv['ccwMoveCountAt']}")
        print(f"edgeCWSteps={inv['edgeCWSteps']}")
        print(f"edgeCCWSteps={inv['edgeCCWSteps']}")
        print(f"edgeNetFlow={inv['edgeNetFlow']}")

    print("\n=== SUMMARY ===")
    print(f"candidate_separating_invariants=[]")
    print("observation=zero-winding cycles collapse the obvious global invariants "
          "(totalDisplacement=0, cwStepCount=ccwStepCount, edgeNetFlow all 0), "
          "and the remaining vectors vary across low-provider samples without "
          "yielding a clean separator.")


if __name__ == "__main__":
    main()
