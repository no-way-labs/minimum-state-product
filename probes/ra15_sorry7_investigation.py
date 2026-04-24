#!/usr/bin/env python3
"""RA15: Sorry 7 investigation — CL bounds, pigeonhole, cycle-type hypothesis.

Sorry 7: odd-winding + non-consecutive binary + non-uniform direction + isolated firings → EC

FOUR PARTS:
1. Verify CL ≥ 3n+4 for odd-winding non-uniform non-consecutive cycles
2. Pigeonhole argument precision
3. Does EC actually need cycle-type hypothesis? Or just non-WaterfallCycle?
4. Edge flow → CL bound derivation
"""
from collections import Counter, defaultdict
from itertools import product as iprod
import time

# ============================================================
# Core cycle infrastructure (from binscc)
# ============================================================

def enumerate_mover_words(ms, n, max_length):
    """Enumerate all valid mover words (cycle-forming) up to max_length."""
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= 2*n and config == start:
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
    """Build config sequence from mover word."""
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


def has_actual_ec(word, cycle, ms, n):
    """Check if cycle has entry conflict at ANY processor."""
    ell = len(word)
    for p in range(n):
        mover_ctx = set()
        nonmover_ctx = set()
        for s in range(ell):
            L = cycle[s][(p-1) % n]
            S = cycle[s][p]
            R = cycle[s][(p+1) % n]
            ctx = (L, S, R)
            if word[s] == p:
                mover_ctx.add(ctx)
            else:
                nonmover_ctx.add(ctx)
        if mover_ctx & nonmover_ctx:
            return True
    return False


def has_ec_at_binary(word, cycle, ms, n, binary_procs):
    """Check if cycle has EC specifically at a binary processor."""
    ell = len(word)
    for p in binary_procs:
        mover_ctx = set()
        nonmover_ctx = set()
        for s in range(ell):
            L = cycle[s][(p-1) % n]
            S = cycle[s][p]
            R = cycle[s][(p+1) % n]
            ctx = (L, S, R)
            if word[s] == p:
                mover_ctx.add(ctx)
            else:
                nonmover_ctx.add(ctx)
        if mover_ctx & nonmover_ctx:
            return True
    return False


# ============================================================
# Cycle classification
# ============================================================

def classify_cycle(word, n):
    """Classify a mover word by winding, direction uniformity, etc."""
    ell = len(word)

    # Per-step displacement: +1 CW, -1 CCW
    displacements = []
    for i in range(ell):
        curr = word[i]
        nxt = word[(i+1) % ell]
        d = (nxt - curr) % n
        if d == 1:
            displacements.append(+1)
        elif d == n - 1:
            displacements.append(-1)
        else:
            # Adjacent but wrapping (same as above covers it for ring)
            # Actually for ring, diff can only be +1 or -1 mod n
            displacements.append(0)  # shouldn't happen for valid ring walks

    total_disp = sum(displacements)
    winding = total_disp // n if total_disp % n == 0 else None

    cw_count = sum(1 for d in displacements if d == 1)
    ccw_count = sum(1 for d in displacements if d == -1)
    uniform = (cw_count == 0 or ccw_count == 0)

    return {
        'total_disp': total_disp,
        'winding': winding,
        'winding_odd': winding is not None and winding % 2 != 0,
        'uniform': uniform,
        'cw': cw_count,
        'ccw': ccw_count,
    }


def is_waterfall_cycle(word, n, ms):
    """Check if this is a uniform-sweep (waterfall) cycle.
    A waterfall cycle visits processors in a single direction sweep."""
    ell = len(word)
    fc = Counter(word)
    # All uniform direction
    info = classify_cycle(word, n)
    if not info['uniform']:
        return False
    # Check if it's a pure sweep (each proc visited in order)
    return True  # Simplified: uniform direction = waterfall-type


def is_non_consecutive_binary(ms, n):
    """Check if binary processors are non-consecutive."""
    binary = [i for i in range(n) if ms[i] == 2]
    if len(binary) < 3:
        return False
    for b in binary:
        if ms[(b+1) % n] == 2:
            return False
    return True


def binary_procs(ms, n):
    return [i for i in range(n) if ms[i] == 2]


def ternary_procs(ms, n):
    return [i for i in range(n) if ms[i] == 3]


# ============================================================
# Generate non-consecutive binary multisets for given n
# ============================================================

def gen_nonconsec_binary_multisets(n, min_binary=3):
    """Generate state vectors with ≥3 non-consecutive binary, rest ternary,
    product < 4*3^(n-2)."""
    threshold = 4 * 3**(n-2)
    # For simplicity: ms entries are 2 or 3
    # Need ≥3 binary, non-consecutive, product < threshold
    results = []
    for mask in range(1 << n):
        bs = [i for i in range(n) if mask & (1 << i)]
        if len(bs) < min_binary:
            continue
        # Check non-consecutive
        consec = False
        for b in bs:
            if (b+1) % n in bs:
                consec = True
                break
        if consec:
            continue
        ms = [2 if i in bs else 3 for i in range(n)]
        prod = 1
        for m in ms:
            prod *= m
        if prod < threshold:
            results.append(ms)
    return results


# ============================================================
# PART 1: CL bounds for odd-winding non-uniform non-consecutive
# ============================================================

def part1_cl_bounds():
    print("=" * 70)
    print("PART 1: Cycle Length Bounds")
    print("=" * 70)

    for n in [5, 7]:
        multisets = gen_nonconsec_binary_multisets(n)
        if not multisets:
            print(f"\n  n={n}: No valid multisets")
            continue

        max_len = 4 * n + 10  # generous upper bound for enumeration
        threshold_cl = 3*n + 4

        for ms in multisets[:3]:  # sample first 3
            t0 = time.time()
            words = enumerate_mover_words(ms, n, max_len)

            # Classify all valid cycles
            cl_by_type = defaultdict(list)
            for word in words:
                cycle = build_cycle(ms, n, word)
                if cycle is None:
                    continue
                info = classify_cycle(word, n)
                ell = len(word)
                key = (info['winding_odd'], info['uniform'])
                cl_by_type[key].append(ell)

            print(f"\n  n={n}, ms={ms}, product={eval('*'.join(str(m) for m in ms))}")
            print(f"  Enumerated in {time.time()-t0:.1f}s")

            for (odd_w, unif), cls in sorted(cl_by_type.items()):
                tag = f"{'odd' if odd_w else 'even'}-wind, {'uniform' if unif else 'non-uniform'}"
                cl_counter = Counter(cls)
                min_cl = min(cls)
                max_cl = max(cls)
                total = len(cls)
                above = sum(1 for c in cls if c >= threshold_cl)
                print(f"    {tag}: {total} cycles, CL range [{min_cl}, {max_cl}], "
                      f"CL≥{threshold_cl}: {above}/{total}")
                # Show distribution
                for cl_val in sorted(cl_counter.keys()):
                    print(f"      CL={cl_val}: {cl_counter[cl_val]}")


# ============================================================
# PART 2: Pigeonhole argument precision
# ============================================================

def part2_pigeonhole():
    print("\n" + "=" * 70)
    print("PART 2: Pigeonhole Argument Precision")
    print("=" * 70)

    print("""
  Setup: Binary proc b with ternary neighbors (L, R ∈ Z₃, S ∈ {0,1}).
  Context space: Z₃ × {0,1} × Z₃ = 18 triples.
  For fixed S=s: 9 possible (L,R) pairs.

  In a cycle of length CL:
    - b fires fc(b) times (mover steps)
    - b doesn't fire CL - fc(b) times (non-mover steps)

  For entry conflict: need some (L, s, R) in both mover and non-mover sets.

  Pigeonhole: if non-mover appearances ≥ 10 for some fixed S=s,
  then all 9 (L,R) pairs covered → any mover with that S matches.
    """)

    # Computational check at small n
    for n in [5, 7]:
        multisets = gen_nonconsec_binary_multisets(n)
        max_len = 4 * n + 10

        for ms in multisets[:2]:
            words = enumerate_mover_words(ms, n, max_len)
            bp = binary_procs(ms, n)

            # For each cycle, track non-mover (L,R) coverage at each binary proc
            coverage_stats = []

            for word in words:
                cycle = build_cycle(ms, n, word)
                if cycle is None:
                    continue
                ell = len(word)
                fc = Counter(word)
                info = classify_cycle(word, n)

                for b in bp:
                    L_idx = (b-1) % n
                    R_idx = (b+1) % n
                    # Only consider if neighbors are ternary
                    if ms[L_idx] != 3 or ms[R_idx] != 3:
                        continue

                    # Count non-mover contexts by S value
                    nonmover_by_s = {0: set(), 1: set()}
                    mover_by_s = {0: set(), 1: set()}

                    for s in range(ell):
                        L = cycle[s][L_idx]
                        S = cycle[s][b]
                        R = cycle[s][R_idx]
                        if word[s] == b:
                            mover_by_s[S].add((L, R))
                        else:
                            nonmover_by_s[S].add((L, R))

                    for s_val in [0, 1]:
                        nm_count = len(nonmover_by_s[s_val])
                        m_count = len(mover_by_s[s_val])
                        overlap = len(nonmover_by_s[s_val] & mover_by_s[s_val])
                        coverage_stats.append({
                            'word': word, 'b': b, 's': s_val,
                            'nm_pairs': nm_count, 'm_pairs': m_count,
                            'overlap': overlap, 'ell': ell,
                            'fc_b': fc[b],
                            'nm_total': ell - fc[b],
                            'winding_odd': info['winding_odd'],
                            'uniform': info['uniform'],
                        })

            # Analyze
            print(f"\n  n={n}, ms={ms}")
            print(f"  Binary procs with ternary neighbors: {[b for b in bp if ms[(b-1)%n]==3 and ms[(b+1)%n]==3]}")

            # For cycles with no EC via pigeonhole: what's the max non-mover coverage?
            no_ec_cycles = set()
            for stat in coverage_stats:
                if stat['overlap'] > 0:
                    continue  # has EC
                # This binary-s combo has no overlap

            # Group by cycle type
            by_type = defaultdict(list)
            for stat in coverage_stats:
                key = (stat['winding_odd'], stat['uniform'])
                by_type[key].append(stat)

            for (odd_w, unif), stats in sorted(by_type.items()):
                tag = f"{'odd' if odd_w else 'even'}-wind, {'uniform' if unif else 'non-uniform'}"
                max_nm_pairs = max(s['nm_pairs'] for s in stats)
                min_nm_pairs = min(s['nm_pairs'] for s in stats)
                any_full_coverage = any(s['nm_pairs'] == 9 for s in stats)
                overlaps = [s['overlap'] for s in stats]
                ec_rate = sum(1 for o in overlaps if o > 0) / len(overlaps) if overlaps else 0
                print(f"    {tag}: {len(stats)} proc-s combos")
                print(f"      Non-mover (L,R) pairs: [{min_nm_pairs}, {max_nm_pairs}], full-9: {any_full_coverage}")
                print(f"      EC rate: {ec_rate:.1%}")


# ============================================================
# PART 3: Does EC need cycle-type hypothesis?
# ============================================================

def part3_hypothesis_test():
    print("\n" + "=" * 70)
    print("PART 3: Does EC Need Cycle-Type Hypothesis?")
    print("=" * 70)
    print("  Test: ALL non-waterfall sub-threshold cycles with ≥3 non-consec binary")
    print("  Do they ALL have entry conflict?")

    for n in [5, 7]:
        multisets = gen_nonconsec_binary_multisets(n)
        max_len = 4 * n + 10

        for ms in multisets[:3]:
            words = enumerate_mover_words(ms, n, max_len)

            total_cycles = 0
            waterfall = 0
            non_waterfall = 0
            non_waterfall_ec = 0
            non_waterfall_no_ec = 0
            waterfall_ec = 0
            waterfall_no_ec = 0

            # Break down by type
            ec_by_type = defaultdict(lambda: [0, 0])  # [has_ec, no_ec]

            for word in words:
                cycle = build_cycle(ms, n, word)
                if cycle is None:
                    continue
                total_cycles += 1

                info = classify_cycle(word, n)
                is_wf = info['uniform']
                has_ec = has_actual_ec(word, cycle, ms, n)

                type_key = f"wind={info['winding']},{'uniform' if info['uniform'] else 'non-uniform'}"
                if has_ec:
                    ec_by_type[type_key][0] += 1
                else:
                    ec_by_type[type_key][1] += 1

                if is_wf:
                    waterfall += 1
                    if has_ec:
                        waterfall_ec += 1
                    else:
                        waterfall_no_ec += 1
                else:
                    non_waterfall += 1
                    if has_ec:
                        non_waterfall_ec += 1
                    else:
                        non_waterfall_no_ec += 1

            print(f"\n  n={n}, ms={ms}, product={eval('*'.join(str(m) for m in ms))}")
            print(f"  Total cycles: {total_cycles}")
            print(f"  Waterfall (uniform): {waterfall} (EC: {waterfall_ec}, no-EC: {waterfall_no_ec})")
            print(f"  Non-waterfall: {non_waterfall} (EC: {non_waterfall_ec}, NO-EC: {non_waterfall_no_ec})")

            if non_waterfall_no_ec > 0:
                print(f"  *** COUNTEREXAMPLE: {non_waterfall_no_ec} non-waterfall cycles WITHOUT EC ***")
            else:
                print(f"  CONFIRMED: ALL non-waterfall cycles have EC")

            print(f"\n  By type:")
            for tk in sorted(ec_by_type.keys()):
                ec, no_ec = ec_by_type[tk]
                print(f"    {tk}: EC={ec}, no-EC={no_ec}")


# ============================================================
# PART 4: Edge flow → CL bound
# ============================================================

def part4_edge_flow():
    print("\n" + "=" * 70)
    print("PART 4: Edge Flow → CL Bound Derivation")
    print("=" * 70)

    print("""
  DEFINITIONS:
    - Mover word w = (w_0, w_1, ..., w_{CL-1}) where w_i ∈ {0,...,n-1}
    - Step displacement d_i = w_{i+1} - w_i (mod n), mapped to +1 (CW) or -1 (CCW)
    - Total displacement D = Σ d_i
    - Winding number W = D / n (must be integer for valid cycle)
    - CW steps: C = #{i : d_i = +1}
    - CCW steps: K = #{i : d_i = -1}
    - CL = C + K (every step moves exactly 1 position on ring)
    - D = C - K, so C = (CL + D)/2, K = (CL - D)/2

  CONSTRAINTS:
    - Each proc p fires fc(p) times, fc(p) = k·m_p for some k ≥ 1
    - CL = Σ fc(p)
    - For sub-threshold: ≥3 binary procs, so fc(b) ≥ 2 for each binary b
    - Total fc ≥ 3·2 + (n-3)·3 = 3n - 3 (minimum)

  Q: Does odd winding + non-uniform force CL ≥ 3n + 4?
    """)

    # Empirical: what's the actual minimum CL for each type?
    for n in [5, 7, 9]:
        multisets = gen_nonconsec_binary_multisets(n)
        if n == 9:
            max_len = 3 * n + 8  # Can't go too high at n=9
        else:
            max_len = 4 * n + 10

        for ms in multisets[:2]:  # sample
            t0 = time.time()
            words = enumerate_mover_words(ms, n, max_len)
            elapsed = time.time() - t0

            min_cl_by_type = defaultdict(lambda: float('inf'))
            count_by_type = defaultdict(int)

            for word in words:
                cycle = build_cycle(ms, n, word)
                if cycle is None:
                    continue
                info = classify_cycle(word, n)
                ell = len(word)

                key = (info['winding_odd'], info['uniform'])
                min_cl_by_type[key] = min(min_cl_by_type[key], ell)
                count_by_type[key] += 1

            print(f"\n  n={n}, ms={ms} ({elapsed:.1f}s, {len(words)} words)")
            for key in sorted(min_cl_by_type.keys()):
                odd_w, unif = key
                tag = f"{'odd' if odd_w else 'even'}-wind, {'uniform' if unif else 'non-uniform'}"
                print(f"    {tag}: min_CL={min_cl_by_type[key]}, count={count_by_type[key]}")

            # Theoretical minimum for fc
            fcs_min = [ms[p] for p in range(n)]  # minimum is 1 full cycle per proc
            cl_min = sum(fcs_min)
            print(f"    Theoretical min CL (1x each proc): {cl_min}")
            print(f"    3n+4 = {3*n+4}")


# ============================================================
# BONUS: fc distribution analysis
# ============================================================

def part_bonus_fc_analysis():
    print("\n" + "=" * 70)
    print("BONUS: Fire-count Distribution")
    print("=" * 70)

    for n in [5, 7]:
        multisets = gen_nonconsec_binary_multisets(n)
        max_len = 4 * n + 10

        for ms in multisets[:1]:
            words = enumerate_mover_words(ms, n, max_len)
            bp = binary_procs(ms, n)

            fc_distributions = defaultdict(list)

            for word in words:
                cycle = build_cycle(ms, n, word)
                if cycle is None:
                    continue
                info = classify_cycle(word, n)
                fc = Counter(word)

                key = (info['winding_odd'], info['uniform'])
                fc_tuple = tuple(fc[p] for p in range(n))
                fc_distributions[key].append(fc_tuple)

            print(f"\n  n={n}, ms={ms}")
            for key in sorted(fc_distributions.keys()):
                odd_w, unif = key
                tag = f"{'odd' if odd_w else 'even'}-wind, {'uniform' if unif else 'non-uniform'}"
                fcs = fc_distributions[key]
                fc_counts = Counter(fcs)
                print(f"    {tag}: {len(fcs)} cycles, {len(fc_counts)} distinct fc vectors")
                for fc_vec, cnt in fc_counts.most_common(5):
                    fc_labeled = {f"P{i}({ms[i]})": fc_vec[i] for i in range(n)}
                    print(f"      fc={fc_vec} (×{cnt}): {fc_labeled}")


# ============================================================
# Main
# ============================================================

if __name__ == "__main__":
    part1_cl_bounds()
    part2_pigeonhole()
    part3_hypothesis_test()
    part4_edge_flow()
    part_bonus_fc_analysis()
