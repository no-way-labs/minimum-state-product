#!/usr/bin/env python3
"""
RA10c: For sweep words that DO exist with non-adjacent binary,
check if they always have entry conflicts.

Key finding from ra10b: sweep words exist at n=9 for some non-adjacent
binary placements like [0,3,6]. We need to check:
1. Do they form valid good cycles?
2. If so, do they ALL have entry conflicts?
3. What mechanism produces the EC?
"""
from collections import defaultdict
from itertools import combinations
import time


def total_displacement(word, n):
    disp = 0
    L = len(word)
    for i in range(L):
        nxt = word[(i + 1) % L]
        cur = word[i]
        diff = (nxt - cur) % n
        if diff == 1:
            disp += 1
        elif diff == n - 1:
            disp -= 1
        else:
            return None
    return disp


def enumerate_words_dfs(n, ms, max_results=5000, timeout=60):
    target_cl = sum(ms)
    results = []
    t0 = time.time()

    def dfs(word, fc):
        if time.time() - t0 > timeout:
            return
        if len(results) >= max_results:
            return
        if len(word) == target_cl:
            if all(fc[p] == ms[p] for p in range(n)):
                diff = (word[0] - word[-1]) % n
                if diff in (1, n - 1):
                    results.append(tuple(word))
            return
        remaining = target_cl - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n))
        if needed > remaining:
            return
        last = word[-1]
        for nxt in [(last + 1) % n, (last - 1) % n]:
            if fc[nxt] < ms[nxt]:
                fc[nxt] += 1
                word.append(nxt)
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1

    for start in range(n):
        if time.time() - t0 > timeout or len(results) >= max_results:
            break
        fc = [0] * n
        fc[start] = 1
        if fc[start] <= ms[start]:
            dfs([start], fc)

    return results


def canonicalize(word):
    L = len(word)
    best = word
    for i in range(L):
        rot = word[i:] + word[:i]
        if rot < best:
            best = rot
    return best


def check_good_cycle_multi(word, ms, n):
    """Check good cycle validity with ALL transition combos (inc/dec at ternary)."""
    L = len(word)
    wl = list(word)
    bins = {p for p in range(n) if ms[p] == 2}
    ternary = [p for p in range(n) if ms[p] == 3]
    n_tern = len(ternary)

    results = []
    for trans_bits in range(1 << n_tern):
        # Build transition direction for each proc
        trans_dir = {}
        for p in bins:
            trans_dir[p] = 1  # inc
        for idx, p in enumerate(ternary):
            trans_dir[p] = 1 if not ((trans_bits >> idx) & 1) else -1  # 1=inc, -1=dec

        configs = [[0] * n]
        for t in range(L):
            c = list(configs[-1])
            p = wl[t]
            c[p] = (c[p] + trans_dir[p]) % ms[p]
            configs.append(c)

        if configs[-1] != configs[0]:
            continue
        config_set = set(tuple(c) for c in configs[:L])
        if len(config_set) != L:
            continue

        results.append((trans_dir.copy(), configs[:L]))

    return results


def find_entry_conflicts(word, ms, n, configs):
    """Find all entry conflicts."""
    L = len(word)
    wl = list(word)
    conflicts = []
    for j in range(n):
        mt = set()
        nmt = set()
        for t in range(L):
            c = tuple(configs[t])
            triple = (c[(j - 1) % n], c[j], c[(j + 1) % n])
            if wl[t] == j:
                mt.add(triple)
            else:
                nmt.add(triple)
        overlap = mt & nmt
        if overlap:
            conflicts.append((j, overlap))
    return conflicts


def min_firing_gap(word, p):
    positions = [i for i, x in enumerate(word) if x == p]
    if len(positions) < 2:
        return float('inf')
    L = len(word)
    min_gap = L
    for i in range(len(positions)):
        j = (i + 1) % len(positions)
        if j == 0:
            gap = (positions[j] + L - positions[i]) - 1
        else:
            gap = positions[j] - positions[i] - 1
        min_gap = min(min_gap, gap)
    return min_gap


def main():
    print("RA10c: Sweep EC Check for Non-Adjacent Binary")
    print("=" * 70)

    # Cases where sweep words exist with 3 binary, no triple
    # From ra10b output at n=9:
    # [0,3,6] nonadj, [1,4,7] nonadj, [2,5,8] nonadj have sweeps!
    # Plus many adjacent-pair cases.

    # Focus on the truly non-adjacent cases first
    n = 9
    threshold = 4 * (3 ** (n - 2))

    nonadj_cases = []
    adj_cases = []

    for bin_combo in combinations(range(n), 3):
        bins_set = set(bin_combo)
        has_triple = False
        for i in range(n):
            if i in bins_set and (i+1)%n in bins_set and (i+2)%n in bins_set:
                has_triple = True
                break
        if has_triple:
            continue

        has_pair = False
        for i in range(n):
            if i in bins_set and (i+1)%n in bins_set:
                has_pair = True
                break

        ms = [2 if p in bins_set else 3 for p in range(n)]
        product = 1
        for m in ms:
            product *= m
        if product >= threshold:
            continue

        words = enumerate_words_dfs(n, ms, max_results=2000, timeout=15)
        unique = {}
        for w in words:
            c = canonicalize(w)
            if c not in unique:
                unique[c] = w

        sweep_words = []
        for w in unique.values():
            d = total_displacement(list(w), n)
            if d is not None and abs(d) >= 2 * n:
                sweep_words.append(w)

        if sweep_words:
            if has_pair:
                adj_cases.append((list(bin_combo), ms, sweep_words))
            else:
                nonadj_cases.append((list(bin_combo), ms, sweep_words))

    print(f"\nn=9: {len(nonadj_cases)} non-adjacent cases, {len(adj_cases)} adjacent-pair cases with sweeps")

    # Analyze non-adjacent cases in detail
    print(f"\n{'='*70}")
    print("NON-ADJACENT BINARY SWEEP ANALYSIS")
    print("=" * 70)

    for bins, ms, sweep_words in nonadj_cases:
        print(f"\nbins={bins}, ms={ms}")
        print(f"  {len(sweep_words)} sweep words")

        total_valid = 0
        total_ec = 0
        no_ec_examples = []

        for w in sweep_words:
            disp = total_displacement(list(w), n)
            # Try ALL transition combos
            valid_cycles = check_good_cycle_multi(w, ms, n)
            for trans_dir, configs in valid_cycles:
                total_valid += 1
                ecs = find_entry_conflicts(list(w), ms, n, configs)
                if ecs:
                    total_ec += 1
                else:
                    no_ec_examples.append((w, disp, trans_dir))

        print(f"  Valid good cycles (all trans): {total_valid}")
        print(f"  With EC: {total_ec}/{total_valid}")
        if no_ec_examples:
            print(f"  *** {len(no_ec_examples)} WITHOUT EC ***")
            for w, disp, td in no_ec_examples[:3]:
                print(f"    word={list(w)[:15]}... disp={disp}")
                print(f"    trans_dir={td}")
        else:
            print(f"  >>> ALL have EC <<<")

    # Also check adjacent-pair cases
    print(f"\n{'='*70}")
    print("ADJACENT-PAIR BINARY SWEEP ANALYSIS (sample)")
    print("=" * 70)

    for bins, ms, sweep_words in adj_cases[:5]:
        print(f"\nbins={bins}, ms={ms}")
        print(f"  {len(sweep_words)} sweep words")

        total_valid = 0
        total_ec = 0

        for w in sweep_words:
            valid_cycles = check_good_cycle_multi(w, ms, n)
            for trans_dir, configs in valid_cycles:
                total_valid += 1
                ecs = find_entry_conflicts(list(w), ms, n, configs)
                if ecs:
                    total_ec += 1

        print(f"  Valid good cycles (all trans): {total_valid}")
        print(f"  With EC: {total_ec}/{total_valid}")
        if total_ec < total_valid:
            print(f"  *** {total_valid - total_ec} WITHOUT EC ***")
        else:
            print(f"  >>> ALL have EC <<<")

    # NOW: check whether sweep words with non-adjacent binary have
    # isolated binary firings, or whether all firings are "concentrated"
    print(f"\n{'='*70}")
    print("FIRING GAP ANALYSIS for sweep words")
    print("=" * 70)

    for bins, ms, sweep_words in nonadj_cases + adj_cases[:5]:
        bins_set = set(bins)
        gap_info = []
        for w in sweep_words[:10]:
            for p in sorted(bins_set):
                gap = min_firing_gap(list(w), p)
                fc = sum(1 for x in w if x == p)
                gap_info.append((bins, p, fc, gap))

        if gap_info:
            print(f"\nbins={bins}:")
            seen = set()
            for b, p, fc, gap in gap_info:
                key = (p, fc, gap)
                if key not in seen:
                    seen.add(key)
                    iso = "ISOLATED" if gap >= 2 else "consecutive"
                    print(f"  proc {p}: fc={fc}, min_gap={gap} [{iso}]")

    # KEY QUESTION: For the sweep case in CaseObstructions.lean,
    # we only reach isolated firings after ruling out EC and permanent_mover.
    # But the data shows ALL sweep good cycles have EC.
    # So the isolated firings case is VACUOUSLY TRUE for sweeps!
    #
    # But wait - we need to check: does the LEAN proof's trichotomy
    # (binary_isolated_firings_or_ec) always produce EC for sweeps?
    # Or does it sometimes give permanent_mover or isolated_firings?
    # The issue is that even if ALL sweep good cycles have EC,
    # binary_isolated_firings_or_ec might not always DETECT it.
    #
    # The right approach: prove that sweep + non-consecutive binary → EC directly,
    # without going through the trichotomy at all.

    print(f"\n{'='*70}")
    print("DIRECT EC MECHANISM FOR SWEEPS")
    print("=" * 70)
    print("""
For sweep cycles (|disp| ≥ 2n), the walk wraps ≥2 times.
Every processor fires ≥ 2 times.

For a binary proc p (fc=2 in a sweep with |disp|=2n):
The walk passes through p's edge twice in each direction? No.
With disp=2n (say CW), the walk is CW 2n+r times, CCW r times.
Each edge is crossed (CW - CCW) = 2 times net.

At each edge (p, p+1): edgeNetFlow = 2.
edgeTraversalCount = CW crossings + CCW crossings.
CW - CCW = 2. CW + CCW = total crossings ≥ 2.

For the edge (p-1, p) and (p, p+1):
fireCount(p) = (left_crossings + right_crossings + stay) / 2 ... wait.
Actually fireCount(p) = CW crossings of (p-1,p) + CCW crossings of (p,p+1)
  + stayMoves at p.
No: fireCount(p) = # steps where mover is at p.

For sweep (all CW): fireCount(p) = CW crossings entering from left
  = crossings of edge (p-1, p) going CW.
And each crossing of (p-1,p) CW means mover was at p-1, moves to p.
So fireCount(p) = CW crossings of (p, p+1) (mover at p, goes CW to p+1).

Wait, let me think about this differently.

For UNIFORM sweep (all steps CW, disp = CL):
- Every step is CW: mover goes from word[t] to word[t]+1 mod n.
- fireCount(p) = # times p appears in word = ms[p].
- For binary: fc(p) = 2.
- The walk is: start, start+1, start+2, ..., visiting each proc ms[p] times.
- This is exactly a UNIFORM SWEEP as defined in the codebase.

But wait, for binary p with fc=2: the walk visits p twice, and all visits
are with CW moves. At each visit, the mover enters from p-1 and leaves to p+1.
The mover triple (c[p-1], c[p], c[p+1]) at first visit is T1.
After firing: c[p] flips. Various other procs fire between visits.
At second visit: triple is T2 with c[p] = 1-T1[1] (since p fires once between).

Now: between the two visits to p, the walk wraps around the ring once.
Every processor fires at least once. In particular, p-1 fires its full count
(or count-1 if it also fires before p's first visit).

The EC would require T1 or T2 to appear as a non-mover triple at p.
Non-mover triples at p occur at ALL steps when the mover is NOT p.
That's CL - 2 steps. The triple at p changes as p-1 and p+1 fire.

Between p's two firings (a full wrap): p-1 fires ms[p-1] or ms[p-1]-1 times,
cycling through its full range. p+1 similarly. So the triple at p takes many
values during non-mover steps.

If ms[p-1]=3 and ms[p+1]=3: the triple has 2*3*3 = 18 possible values,
but only 2 mover triples. The 18 non-mover triples span most of the space.
With CL-2 = 22 non-mover steps and only 18 possible triples: by pigeonhole,
repeats occur. But we need to check if the 2 mover triples are among the ~18.
""")

    # Check: for each sweep good cycle, at WHICH proc does EC occur?
    print("EC location analysis:")
    for bins, ms, sweep_words in nonadj_cases:
        bins_set = set(bins)
        print(f"\nbins={bins}:")
        ec_loc_counts = defaultdict(int)
        for w in sweep_words:
            valid_cycles = check_good_cycle_multi(w, ms, n)
            for td, configs in valid_cycles:
                ecs = find_entry_conflicts(list(w), ms, n, configs)
                for proc, _ in ecs:
                    role = "binary" if proc in bins_set else "ternary"
                    ec_loc_counts[(proc, role)] += 1

        for (proc, role), count in sorted(ec_loc_counts.items()):
            print(f"  EC at proc {proc} ({role}): {count} times")

    # Check at n=7 too
    print(f"\n{'='*70}")
    print("n=7 sweep analysis")
    print("=" * 70)

    n = 7
    threshold = 4 * (3 ** (n - 2))

    for bin_combo in combinations(range(n), 3):
        bins_set = set(bin_combo)
        has_triple = any(i in bins_set and (i+1)%n in bins_set and (i+2)%n in bins_set for i in range(n))
        if has_triple:
            continue

        ms = [2 if p in bins_set else 3 for p in range(n)]
        product = 1
        for m in ms:
            product *= m
        if product >= threshold:
            continue

        words = enumerate_words_dfs(n, ms, max_results=2000, timeout=10)
        unique = {}
        for w in words:
            c = canonicalize(w)
            if c not in unique:
                unique[c] = w

        sweep_words = [w for w in unique.values()
                       if total_displacement(list(w), n) is not None
                       and abs(total_displacement(list(w), n)) >= 2 * n]

        if not sweep_words:
            continue

        has_pair = any(i in bins_set and (i+1)%n in bins_set for i in range(n))
        adj_label = "adj" if has_pair else "nonadj"

        total_valid = 0
        total_ec = 0
        for w in sweep_words:
            valid_cycles = check_good_cycle_multi(w, ms, n)
            for td, configs in valid_cycles:
                total_valid += 1
                ecs = find_entry_conflicts(list(w), ms, n, configs)
                if ecs:
                    total_ec += 1

        print(f"  bins={list(bin_combo)} [{adj_label}]: "
              f"{len(sweep_words)} sweep words, {total_valid} valid, {total_ec} EC")
        if total_ec < total_valid:
            print(f"    *** {total_valid - total_ec} WITHOUT EC ***")


if __name__ == '__main__':
    main()
