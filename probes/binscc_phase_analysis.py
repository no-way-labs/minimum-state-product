#!/usr/bin/env python3
"""binscc_phase_analysis.py — Analyze binary-neighbor firing distribution
within ternary proc phases.

KEY INSIGHT: For ternary t between binary b_L, b_R:
- t has 3 phases (c[t]=0, c[t]=1, c[t]=2)
- (c[b_L], c[b_R]) trajectory determines alias at t
- Distribution (α_k, δ_k) of binary firings per phase controls alias

If any phase has 0 binary flips → alias at t (constant (L,R) matches mover)
If any phase has 2 same-coord flips → alias at t (start = endpoint)
Only surviving: each phase has ≥ 1 flip, no 2-same-coord flips → (1,1,2) distr

QUESTION: When ternary has (1,1,2) distribution (no alias at t),
does binary b ALWAYS have alias?
"""

import sys
from collections import Counter, defaultdict
import time


def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= 6 and config == start:
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


def has_mover_alias(ms, n, word, cycle, p):
    ell = len(cycle)
    mL = (p - 1) % n
    mR = (p + 1) % n
    ctx_to_count = {}
    mover_ctxs = set()
    for step in range(ell):
        c = cycle[step]
        ctx = (c[mL], c[p], c[mR])
        ctx_to_count[ctx] = ctx_to_count.get(ctx, 0) + 1
        if word[step] == p:
            mover_ctxs.add(ctx)
    for ctx in mover_ctxs:
        if ctx_to_count[ctx] >= 2:
            return True
    return False


def get_ternary_phase_dist(ms, n, word, cycle, t):
    """Get distribution of binary-neighbor firings across ternary phases.

    Returns: list of (alpha_k, delta_k) for k = 0..m_t-1
    where alpha_k = # of bL firings in phase k, delta_k = # of bR firings.
    """
    ell = len(cycle)
    bL = (t - 1) % n
    bR = (t + 1) % n
    m_t = ms[t]

    # Find t's firing steps
    t_steps = [s for s in range(ell) if word[s] == t]

    # Phase k = c[t]=k: from after (k-1)-th firing to k-th firing
    # Phase 0: from start/after last firing to first firing
    # We need to identify which phase each step belongs to
    phases = []  # phase_k for each step
    for s in range(ell):
        phases.append(cycle[s][t])

    # Count bL and bR firings per phase
    dist = []
    for k in range(m_t):
        alpha = sum(1 for s in range(ell)
                    if phases[s] == k and word[s] == bL)
        delta = sum(1 for s in range(ell)
                    if phases[s] == k and word[s] == bR)
        dist.append((alpha, delta))

    return dist


def classify_phase_dist(dist):
    """Classify phase distribution.
    Returns: 'zero_phase' if any phase has 0 flips,
             'double_same' if any phase has 2+ same-coord flips,
             'safe_112' if exactly (1,1,2) distribution (no alias from phases),
             'other'
    """
    for alpha, delta in dist:
        if alpha + delta == 0:
            return 'zero_phase'

    for alpha, delta in dist:
        if alpha >= 2 or delta >= 2:
            return 'double_same'

    return 'safe_112'


def main():
    print("=" * 70)
    print("TERNARY PHASE DISTRIBUTION ANALYSIS")
    print("=" * 70)

    n, ms = 5, [2, 3, 2, 3, 2]
    max_len = 21
    print(f"n={n} ms={ms}")
    bin_procs = [0, 2, 4]
    tern_procs = [1, 3]

    t0 = time.time()
    words = enumerate_mover_words(ms, n, max_len)
    t1 = time.time()
    print(f"{len(words)} words ({t1-t0:.1f}s)")

    total = 0

    # PART 1: Phase distribution at ternary procs
    print(f"\nPART 1: PHASE DISTRIBUTION")
    phase_class_count = {t: Counter() for t in tern_procs}
    phase_class_alias = {t: Counter() for t in tern_procs}

    # Track correlation: phase class vs mover alias
    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue
        total += 1

        for t in tern_procs:
            dist = get_ternary_phase_dist(ms, n, word, cycle, t)
            cls = classify_phase_dist(dist)
            phase_class_count[t][cls] += 1
            if has_mover_alias(ms, n, word, cycle, t):
                phase_class_alias[t][cls] += 1

    elapsed = time.time() - t0
    print(f"Total valid: {total} ({elapsed:.1f}s)")

    for t in tern_procs:
        print(f"\n  P{t} (ternary, between P{(t-1)%n} and P{(t+1)%n}):")
        for cls in ['zero_phase', 'double_same', 'safe_112', 'other']:
            cnt = phase_class_count[t].get(cls, 0)
            alias = phase_class_alias[t].get(cls, 0)
            if cnt > 0:
                print(f"    {cls}: {cnt} ({100*cnt/total:.1f}%), "
                      f"alias: {alias}/{cnt} ({100*alias/cnt:.1f}%)")

    # PART 2: When ternary is safe_112 AND has no alias, check binary
    print(f"\nPART 2: BINARY ALIAS WHEN TERNARY SAFE_112")
    safe_no_alias = 0
    safe_no_alias_bin_alias = Counter()  # which binary has alias
    safe_no_alias_any_bin = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue

        for t in tern_procs:
            dist = get_ternary_phase_dist(ms, n, word, cycle, t)
            cls = classify_phase_dist(dist)
            if cls != 'safe_112':
                continue
            if has_mover_alias(ms, n, word, cycle, t):
                continue

            safe_no_alias += 1
            bL = (t - 1) % n
            bR = (t + 1) % n

            has_b = False
            for b in bin_procs:
                if has_mover_alias(ms, n, word, cycle, b):
                    safe_no_alias_bin_alias[b] += 1
                    has_b = True
            if has_b:
                safe_no_alias_any_bin += 1

    print(f"  Ternary safe_112 with no alias: {safe_no_alias}")
    if safe_no_alias > 0:
        for b in bin_procs:
            cnt = safe_no_alias_bin_alias.get(b, 0)
            print(f"    P{b} (binary) has alias: {cnt}/{safe_no_alias} "
                  f"({100*cnt/safe_no_alias:.1f}%)")
        print(f"    ANY binary has alias: {safe_no_alias_any_bin}/{safe_no_alias}")

    # PART 3: When NO ternary has alias, analyze binary phase structure
    print(f"\nPART 3: BINARY ANALYSIS WHEN ALL TERNARY FAIL")
    no_tern_count = 0
    no_tern_bin_success = Counter()
    no_tern_any_success = 0

    # Detailed: what's the binary's neighbor distribution?
    bin_phase_when_tern_fail = Counter()

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue
        ell = len(cycle)

        # Check if NO ternary has alias
        any_tern = any(has_mover_alias(ms, n, word, cycle, t)
                       for t in tern_procs)
        if any_tern:
            continue

        no_tern_count += 1
        has_any_bin = False
        for b in bin_procs:
            if has_mover_alias(ms, n, word, cycle, b):
                no_tern_bin_success[b] += 1
                has_any_bin = True
        if has_any_bin:
            no_tern_any_success += 1

        # Binary phase analysis
        for b in bin_procs:
            mL = (b - 1) % n
            mR = (b + 1) % n
            # b fires twice: at c[b]=0 (UP) and c[b]=1 (DOWN)
            # Phase 0: c[b]=0; Phase 1: c[b]=1
            for phase in [0, 1]:
                alpha = sum(1 for s in range(ell)
                           if cycle[s][b] == phase and word[s] == mL)
                delta = sum(1 for s in range(ell)
                           if cycle[s][b] == phase and word[s] == mR)
                bin_phase_when_tern_fail[(b, phase, alpha, delta)] += 1

    print(f"  No ternary has alias: {no_tern_count}")
    if no_tern_count > 0:
        for b in bin_procs:
            cnt = no_tern_bin_success.get(b, 0)
            print(f"    P{b} binary has alias: {cnt}/{no_tern_count} "
                  f"({100*cnt/no_tern_count:.1f}%)")
        print(f"    ANY binary has alias: {no_tern_any_success}/{no_tern_count}")

        print(f"\n  Binary phase neighbor firing distribution:")
        for (b, phase, alpha, delta), cnt in sorted(
                bin_phase_when_tern_fail.items()):
            print(f"    P{b} phase={phase}: "
                  f"nL_fires={alpha} nR_fires={delta} × {cnt}")

    # PART 4: The FULL picture - when does the union fail?
    # (It never should, but let's verify and characterize the tight cases)
    print(f"\nPART 4: TIGHTEST CASES (fewest procs with alias)")
    alias_count_dist = Counter()  # how many procs have alias

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue

        alias_procs = sum(1 for p in range(n)
                         if has_mover_alias(ms, n, word, cycle, p))
        alias_count_dist[alias_procs] += 1

    print(f"  Procs with alias distribution:")
    for k, cnt in sorted(alias_count_dist.items()):
        print(f"    {k} procs: {cnt} ({100*cnt/total:.1f}%)")

    # PART 5: For cycles with exactly 1 proc having alias, characterize
    if alias_count_dist.get(1, 0) > 0:
        print(f"\n  1-alias-proc cycles:")
        count = 0
        for word in words:
            cycle = build_cycle(ms, n, word)
            if cycle is None:
                continue
            alias_procs = [p for p in range(n)
                          if has_mover_alias(ms, n, word, cycle, p)]
            if len(alias_procs) != 1:
                continue
            p = alias_procs[0]
            print(f"    ℓ={len(word)} alias only at P{p} (m={ms[p]})")
            count += 1
            if count >= 10:
                break

    # PART 6: Pigeonhole check — for each proc, how does ℓ compare to
    # context bound? Is alias GUARANTEED by counting alone?
    print(f"\nPART 6: PIGEONHOLE ANALYSIS")
    print("  For proc p: ℓ steps, at most D_p distinct contexts")
    print("  m_p mover contexts (all unique S values)")
    print("  If ℓ - m_p > D_p - m_p → nonmover bin has alias ≥ 2")
    print("  But need: ℓ > D_p to force ANY alias (which we have)")
    print("  Need: the specific mechanism forcing MOVER alias")
    print()

    # For each proc and each cycle length, compute the tight bound
    for p in range(n):
        mL = (p - 1) % n
        mR = (p + 1) % n
        F_p = ms[mL] + ms[p] + ms[mR]
        D_p = F_p + 1
        m_p = ms[p]
        nonmover_bins = D_p - m_p
        print(f"  P{p}: m={ms[p]}, F={F_p}, D≤{D_p}, "
              f"mover_bins={m_p}, nonmover_bins≤{nonmover_bins}")
        # For ℓ = min(12), nonmover steps = 12 - m_p
        for ell in [12, 14, 16, 18, 21]:
            nm_steps = ell - m_p
            # Average nonmover per nonmover bin
            avg = nm_steps / nonmover_bins if nonmover_bins > 0 else float('inf')
            # If all aliases are in nonmover bins, max nonmover count
            print(f"    ℓ={ell}: nm_steps={nm_steps}, "
                  f"nm_bins≤{nonmover_bins}, avg_nm={avg:.2f}")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
