#!/usr/bin/env python3
"""
RA4 Script 1: Phase-level classification of good cycles.

For good cycles with sub-threshold product, ternary pivot t with binary neighbors:
- Extract t-phases (intervals between consecutive t-fires)
- Classify each phase by (J, K)
- Check mixed phases, adjacent-chain structure, EC properties

We start at n=5,6 with various binary placements, then try n=7.
The key question: are mixed phases (J>=1, K>=1) ever found in EC-free cycles?
"""
from collections import Counter


def enumerate_good_cycles_exhaustive(ms, n, max_length=None):
    """Exhaustively enumerate good cycles via DFS on mover words."""
    if max_length is None:
        max_length = 4 * sum(ms)
    ring_adj = {p: [(p - 1) % n, (p + 1) % n] for p in range(n)}
    seen = set()
    results = []

    start = tuple(0 for _ in range(n))

    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= 2 * n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                w = tuple(word)
                best = w
                for i in range(len(w)):
                    rot = w[i:] + w[:i]
                    if rot < best:
                        best = rot
                if best not in seen:
                    seen.add(best)
                    results.append(list(best))
                return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n)
                     if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            nc = list(config)
            nc[nxt] = (nc[nxt] + 1) % ms[nxt]
            nf = list(fc)
            nf[nxt] += 1
            word.append(nxt)
            dfs(word, nf, tuple(nc))
            word.pop()

    for p in range(n):
        first_config = list(start)
        first_config[p] = (first_config[p] + 1) % ms[p]
        dfs([p], [1 if i == p else 0 for i in range(n)], tuple(first_config))

    return results


def build_configs(ms, n, word):
    ell = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    return configs[:ell]


def has_entry_conflict(configs, movers, n):
    ell = len(movers)
    for p in range(n):
        L, R = (p - 1) % n, (p + 1) % n
        mover_triples = set()
        nonmover_triples = set()
        for i in range(ell):
            triple = (configs[i][L], configs[i][p], configs[i][R])
            if movers[i] == p:
                mover_triples.add(triple)
            else:
                nonmover_triples.add(triple)
        if mover_triples & nonmover_triples:
            return True
    return False


def extract_phases(movers, t, ell):
    t_steps = [i for i in range(ell) if movers[i] == t]
    if len(t_steps) < 2:
        return []
    phases = []
    for idx in range(len(t_steps)):
        a = t_steps[idx]
        s = t_steps[(idx + 1) % len(t_steps)]
        if s <= a:
            s += ell
        phases.append((a, s))
    return phases


def ring_dist(a, b, n):
    return min((a - b) % n, (b - a) % n)


def analyze_config(n, ms, label=""):
    binary_pos = [i for i in range(n) if ms[i] == 2]
    if len(binary_pos) < 3:
        return

    prod = 1
    for m in ms:
        prod *= m
    threshold = 4 * 3 ** (n - 2)

    # Check non-consecutive on ring
    is_nonconsec = all(ring_dist(binary_pos[i], binary_pos[j], n) > 1
                       for i in range(len(binary_pos))
                       for j in range(i + 1, len(binary_pos)))

    print(f"\n{'='*70}")
    print(f"n={n}, ms={ms}, product={prod}, threshold={threshold}")
    print(f"Binary at {binary_pos}, non-consecutive={is_nonconsec}")
    if label:
        print(f"({label})")

    pivots = []
    for t in range(n):
        L, R = (t - 1) % n, (t + 1) % n
        if ms[t] >= 3 and ms[L] == 2 and ms[R] == 2:
            pivots.append(t)
    print(f"Pivots: {pivots}")
    if not pivots:
        print("No pivots -- skipping")
        return

    max_len = max(3 * n, 2 * sum(ms))
    if n >= 7:
        max_len = min(max_len, 3 * n)
    print(f"Enumerating (max len {max_len})...")
    words = enumerate_good_cycles_exhaustive(ms, n, max_length=max_len)
    print(f"Found {len(words)} distinct good cycles")
    if not words:
        return

    phase_counts = Counter()
    mixed_count = 0
    mixed_with_ec = 0
    mixed_without_ec = 0
    adj_chain = Counter()  # (has_adjL, has_adjR) -> count
    no_ec_mixed_details = []

    all_sparse_count = 0
    all_sparse_ec = 0
    all_sparse_noec = 0

    for word in words:
        movers = word
        ell = len(movers)
        configs = build_configs(ms, n, word)
        has_ec = has_entry_conflict(configs, movers, n)

        all_sparse = True
        for t in pivots:
            phases = extract_phases(movers, t, ell)
            for a, s in phases:
                L_proc = (t - 1) % n
                R_proc = (t + 1) % n
                LL = (t - 2) % n
                RR = (t + 2) % n
                J = sum(1 for i in range(a + 1, s) if movers[i % ell] == L_proc)
                K = sum(1 for i in range(a + 1, s) if movers[i % ell] == R_proc)

                if J + K > 1:
                    all_sparse = False

                if J == 0 and K == 0:
                    ptype = "empty"
                elif K == 0:
                    ptype = "L-only"
                elif J == 0:
                    ptype = "R-only"
                else:
                    ptype = "mixed"

                phase_counts[(ptype, J, K)] += 1

                if J >= 1 and K >= 1:
                    mixed_count += 1
                    if has_ec:
                        mixed_with_ec += 1
                    else:
                        mixed_without_ec += 1

                    # Check adjacent chain
                    fL = fR = None
                    for i in range(a + 1, s):
                        idx = i % ell
                        if movers[idx] == L_proc and fL is None:
                            fL = i
                        if movers[idx] == R_proc and fR is None:
                            fR = i

                    has_adjL = has_adjR = False
                    if fL is not None and fL > a + 1:
                        has_adjL = movers[(fL - 1) % ell] == LL
                    if fR is not None and fR > a + 1:
                        has_adjR = movers[(fR - 1) % ell] == RR

                    adj_chain[(has_adjL, has_adjR)] += 1

                    if not has_ec and len(no_ec_mixed_details) < 10:
                        no_ec_mixed_details.append({
                            't': t, 'a': a, 's': s, 'J': J, 'K': K,
                            'movers': [movers[i % ell] for i in range(a, s)],
                            'adjL': has_adjL, 'adjR': has_adjR,
                        })

        if all_sparse:
            all_sparse_count += 1
            if has_ec:
                all_sparse_ec += 1
            else:
                all_sparse_noec += 1

    print(f"\nPhase (type, J, K) distribution:")
    for (ptype, j, k), cnt in sorted(phase_counts.items(), key=lambda x: -x[1]):
        print(f"  {ptype} J={j} K={k}: {cnt}")

    print(f"\nMixed phases: {mixed_count}")
    print(f"  with EC: {mixed_with_ec}, without EC: {mixed_without_ec}")
    print(f"\n  Adjacent-chain structure:")
    for (aL, aR), cnt in sorted(adj_chain.items()):
        print(f"    adjL={aL}, adjR={aR}: {cnt}")

    if no_ec_mixed_details:
        print(f"\n  EC-free mixed phase examples (first {min(5, len(no_ec_mixed_details))}):")
        for d in no_ec_mixed_details[:5]:
            print(f"    t={d['t']}, J={d['J']}, K={d['K']}, "
                  f"adjL={d['adjL']}, adjR={d['adjR']}")
            print(f"      movers: {d['movers']}")

    print(f"\nAll-sparse (J+K<=1 at all pivots): {all_sparse_count}")
    print(f"  EC: {all_sparse_ec}, no EC: {all_sparse_noec}")
    if all_sparse_noec == 0 and all_sparse_count > 0:
        print(f"  ** ALL all-sparse cycles have EC **")
    elif all_sparse_noec > 0:
        print(f"  *** {all_sparse_noec} EC-free all-sparse cycles ***")


def main():
    # n=5: binary at 0,2,4 -- but 0 and 4 are adjacent on 5-ring (dist=1).
    # So actually all 3-binary placements on 5-ring have at least 2 consecutive.
    # For n=5 with 3 binary: impossible to have all non-consecutive.
    # Need n>=6 for 3 non-consecutive binary.
    print("="*70)
    print("NOTE: On a ring of size n, 3 non-adjacent binary positions require n>=7")
    print("(for n=5,6: 3 binary on ring of 5 or 6 always has an adjacent pair)")
    print("Testing anyway with various configs...")
    print("="*70)

    # n=5: consecutive binary (Case 3a) -- for reference
    analyze_config(5, [2, 2, 2, 3, 3], "3 consecutive binary")
    analyze_config(5, [2, 3, 2, 3, 2], "alternating -- binary at 0,2,4 (0-4 adjacent)")

    # n=6: binary at 0,2,4
    analyze_config(6, [2, 3, 2, 3, 2, 3], "binary at 0,2,4 -- 0-4 dist=2 OK, 4-0 dist=2 OK on 6-ring")

    # n=7: first opportunity for 3 truly non-adjacent binary
    analyze_config(7, [2, 3, 2, 3, 2, 3, 3],
                   "binary at 0,2,4 -- dist(0,4)=3, dist(4,0)=3 on 7-ring")
    analyze_config(7, [2, 3, 3, 2, 3, 3, 2],
                   "binary at 0,3,6 -- dist(0,3)=3, dist(3,6)=3, dist(0,6)=1 ADJACENT!")
    analyze_config(7, [3, 2, 3, 2, 3, 2, 3],
                   "binary at 1,3,5 -- dist(1,3)=2, dist(3,5)=2, dist(1,5)=3")


if __name__ == '__main__':
    main()
