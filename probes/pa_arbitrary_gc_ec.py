#!/usr/bin/env python3
"""PA: Does EC hold at boundary ternary procs for ARBITRARY good cycles
when >=3 non-consecutive binary exist at sub-threshold product?

We check: for every good cycle on every valid ring placement with
>=3 non-consecutive binary and product < 4*3^(n-2), does some
boundary ternary proc t (adjacent to a binary proc) have entry conflict?

Entry conflict at proc t: exists (L,S,R) appearing at both a mover step
(word[s] == t) and a nonmover step (word[s] != t).

We enumerate:
- All valid state vectors ms with >=3 binary, non-consecutive, product < threshold
- All mover words (ring walks returning to start with fc[p] % m_p == 0)
- Build the unique cycle (incrementing transitions)
- Check EC at boundary ternary procs

Key: we check ARBITRARY good cycles, not just fc=2 wavefronts.
"""
import itertools
from collections import Counter, defaultdict
import time
import math


def enumerate_mover_words(ms, n, max_length):
    """Enumerate all valid mover words on the ring."""
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    min_len = sum(ms)  # minimum: each proc fires exactly m_p times

    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= min_len and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
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
        first = list(start)
        first[p] = (first[p] + 1) % ms[p]
        dfs([p], [1 if i == p else 0 for i in range(n)], tuple(first))
    return results


def build_cycle(ms, n, word):
    """Build config sequence from mover word (incrementing transitions)."""
    ell = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:ell])) != ell:
        return None
    return configs[:ell]


def has_ec_at_boundary(word, cycle, ms, n, boundary_ternary):
    """Check if any boundary ternary proc has entry conflict."""
    ell = len(word)
    for t in boundary_ternary:
        bL = (t - 1) % n
        bR = (t + 1) % n
        mover_ctxs = set()
        nonmover_ctxs = set()
        for s in range(ell):
            ctx = (cycle[s][bL], cycle[s][t], cycle[s][bR])
            if word[s] == t:
                mover_ctxs.add(ctx)
            else:
                nonmover_ctxs.add(ctx)
        if mover_ctxs & nonmover_ctxs:
            return True
    return False


def has_ec_at_any_ternary(word, cycle, ms, n):
    """Check if ANY ternary proc adjacent to a binary has EC."""
    ell = len(word)
    for t in range(n):
        if ms[t] <= 2:
            continue
        # Check if t is adjacent to any binary
        bL = (t - 1) % n
        bR = (t + 1) % n
        if ms[bL] != 2 and ms[bR] != 2:
            continue
        mover_ctxs = set()
        nonmover_ctxs = set()
        for s in range(ell):
            ctx = (cycle[s][bL], cycle[s][t], cycle[s][bR])
            if word[s] == t:
                mover_ctxs.add(ctx)
            else:
                nonmover_ctxs.add(ctx)
        if mover_ctxs & nonmover_ctxs:
            return True
    return False


def has_ec_anywhere(word, cycle, ms, n):
    """Check if ANY proc has EC."""
    ell = len(word)
    for t in range(n):
        bL = (t - 1) % n
        bR = (t + 1) % n
        mover_ctxs = set()
        nonmover_ctxs = set()
        for s in range(ell):
            ctx = (cycle[s][bL], cycle[s][t], cycle[s][bR])
            if word[s] == t:
                mover_ctxs.add(ctx)
            else:
                nonmover_ctxs.add(ctx)
        if mover_ctxs & nonmover_ctxs:
            return True
    return False


def get_nonconsec_binary_placements(n):
    """Generate all state vectors with >=3 non-consecutive binary,
    remaining ternary, product < 4*3^(n-2)."""
    threshold = 4 * (3 ** (n - 2))
    placements = []

    # Binary positions: choose >=3 from {0,...,n-1}, no two adjacent
    for num_bin in range(3, n // 2 + 2):  # at most n//2 non-adjacent
        for binary_pos in itertools.combinations(range(n), num_bin):
            # Check non-consecutive (on ring)
            ok = True
            for i in range(len(binary_pos)):
                for j in range(i + 1, len(binary_pos)):
                    if abs(binary_pos[i] - binary_pos[j]) % n <= 1 or \
                       abs(binary_pos[i] - binary_pos[j]) % n >= n - 1:
                        if binary_pos[i] != binary_pos[j]:
                            ok = False
                            break
                if not ok:
                    break
            if not ok:
                continue

            ms = [3] * n
            for p in binary_pos:
                ms[p] = 2
            prod = 1
            for m in ms:
                prod *= m
            if prod < threshold:
                placements.append(tuple(ms))

    # Deduplicate by rotation
    seen = set()
    unique = []
    for ms in placements:
        canon = min(tuple(ms[i:] + ms[:i]) for i in range(n))
        if canon not in seen:
            seen.add(canon)
            unique.append(ms)
    return unique


def analyze_phases(word, cycle, ms, n, t):
    """Extract phase data for ternary proc t."""
    ell = len(word)
    fc_t = sum(1 for s in range(ell) if word[s] == t)
    M_per_phase = fc_t // ms[t]  # firings per phase

    bL = (t - 1) % n
    bR = (t + 1) % n

    phases = []
    # Find t-firing steps
    t_steps = [s for s in range(ell) if word[s] == t]

    for phase_idx in range(ms[t]):
        # Steps in this phase: from after t_steps[phase_idx*M] firing
        # to just before t_steps[(phase_idx+1)*M] firing
        start_fire = phase_idx * M_per_phase
        end_fire = (phase_idx + 1) * M_per_phase

        # Collect all steps between t_steps[start_fire] and t_steps[end_fire-1]
        # (inclusive of the t-firing steps)
        if start_fire < len(t_steps) and end_fire <= len(t_steps):
            first = t_steps[start_fire]
            if end_fire < len(t_steps):
                last = t_steps[end_fire]
            else:
                last = t_steps[0]  # wrap

            # Count J (bL firings) and K (bR firings) in this phase
            J, K = 0, 0
            s = first
            while True:
                if word[s] == bL:
                    J += 1
                elif word[s] == bR:
                    K += 1
                if s == (last - 1) % ell:
                    break
                s = (s + 1) % ell
                if s == first and J + K > ell:  # safety
                    break

            phases.append((J, K, M_per_phase))

    return phases


# ======================================================================
# MAIN COMPUTATION
# ======================================================================

print("=" * 70)
print("PA: ARBITRARY GOOD CYCLE EC CHECK")
print("Does every good cycle have EC at some boundary ternary?")
print("=" * 70)

for n in [5, 7]:
    threshold = 4 * (3 ** (n - 2))
    placements = get_nonconsec_binary_placements(n)
    print(f"\nn={n}, threshold={threshold}")
    print(f"  Non-consecutive binary placements: {len(placements)}")

    max_len_map = {5: 16, 7: 28, 9: 40}
    max_len = max_len_map.get(n, 2 * n + 10)

    for ms in placements:
        ms_list = list(ms)
        prod = 1
        for m in ms_list:
            prod *= m

        binary_pos = [p for p in range(n) if ms_list[p] == 2]
        # Boundary ternary: ternary proc adjacent to some binary
        boundary_t = []
        for t in range(n):
            if ms_list[t] > 2:
                bL = (t - 1) % n
                bR = (t + 1) % n
                if ms_list[bL] == 2 or ms_list[bR] == 2:
                    boundary_t.append(t)

        # "Sandwiched" = ternary between two binary
        sandwiched = [t for t in range(n) if ms_list[t] == 3
                      and ms_list[(t-1)%n] == 2 and ms_list[(t+1)%n] == 2]

        t0 = time.time()
        words = enumerate_mover_words(ms_list, n, max_len)
        t1 = time.time()

        total = 0
        ec_boundary = 0
        ec_any_adj = 0
        ec_anywhere = 0
        no_ec = []
        fc_dist = Counter()

        for word in words:
            cycle = build_cycle(ms_list, n, word)
            if cycle is None:
                continue
            total += 1

            fc = Counter(word)
            fc_key = tuple(fc[p] // ms_list[p] for p in range(n))
            fc_dist[fc_key] += 1

            # Check EC at sandwiched ternary (between two binary)
            if sandwiched:
                has_sand = has_ec_at_boundary(word, cycle, ms_list, n, sandwiched)
            else:
                has_sand = False

            # Check EC at any ternary adjacent to binary
            has_adj = has_ec_at_any_ternary(word, cycle, ms_list, n)

            # Check EC anywhere
            has_any = has_ec_anywhere(word, cycle, ms_list, n)

            if has_sand:
                ec_boundary += 1
            if has_adj:
                ec_any_adj += 1
            if has_any:
                ec_anywhere += 1
            if not has_any:
                no_ec.append((word, fc_key))

        t2 = time.time()

        if total == 0:
            print(f"  ms={ms_list} prod={prod}: 0 cycles (enum {t1-t0:.1f}s)")
            continue

        print(f"\n  ms={ms_list} prod={prod} bin={binary_pos}")
        print(f"    binary_pos={binary_pos} boundary_t={boundary_t} sandwiched={sandwiched}")
        print(f"    {total} cycles enumerated in {t1-t0:.1f}s, checked in {t2-t1:.1f}s")
        print(f"    EC at sandwiched:    {ec_boundary}/{total} ({100*ec_boundary/total:.1f}%)")
        print(f"    EC at adj-to-binary: {ec_any_adj}/{total} ({100*ec_any_adj/total:.1f}%)")
        print(f"    EC anywhere:         {ec_anywhere}/{total} ({100*ec_anywhere/total:.1f}%)")

        if no_ec:
            print(f"    *** WARNING: {len(no_ec)} cycles with NO EC ANYWHERE ***")
            for w, fk in no_ec[:3]:
                print(f"      word={w} fc_mult={fk}")

        # Show fire count distribution
        if len(fc_dist) <= 10:
            print(f"    FC multiplicity dist: {dict(fc_dist)}")
        else:
            print(f"    FC multiplicity dist: {len(fc_dist)} distinct patterns")
            # Show top 5
            for fk, cnt in fc_dist.most_common(5):
                print(f"      {fk}: {cnt}")

        if ec_boundary == total:
            print(f"    *** 100% EC AT SANDWICHED TERNARY ***")
        elif ec_any_adj == total:
            print(f"    *** 100% EC AT BOUNDARY TERNARY ***")
        elif ec_anywhere == total:
            print(f"    *** 100% EC SOMEWHERE (not always at boundary) ***")
