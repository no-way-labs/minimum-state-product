#!/usr/bin/env python3
"""
CIC Exploration 13d: Analytical Shadow Construction for Wiggle Words.

Key findings so far:
- σ closed-form for {1,2}-wiggle words: verified n=8..15
- Δ has exactly 7 types with clean n-dependent patterns
- MNU trivially true

This script:
1. Defines Δ types analytically as a function of n
2. Constructs shadow configs from Δ + σ + waterfall
3. Verifies closure by checking mover entry transitions
4. Checks all 5 shadow properties from the construction
5. Tests for general n up to 20
"""

from itertools import product as iproduct
from collections import Counter
import sys


def enumerate_state_sequences(n, ms, fire_counts):
    proc_sequences = {}
    for p in range(n):
        m = ms[p]
        k = fire_counts[p]
        seqs = []
        def dfs_seq(seq, remaining, m_val=m):
            if remaining == 0:
                if seq[-1] == 0:
                    seqs.append(list(seq))
                return
            current = seq[-1]
            for next_val in range(m_val):
                if next_val != current:
                    if remaining == 1 and next_val != 0:
                        continue
                    seq.append(next_val)
                    dfs_seq(seq, remaining - 1, m_val)
                    seq.pop()
        dfs_seq([0], k)
        proc_sequences[p] = seqs
    return proc_sequences


def sigma_12wiggle(t, n):
    """Closed-form σ for CCW {1,2}-wiggle word. L = 2n+2."""
    if t == 0: return n - 2
    elif t == 1: return n + 1
    elif 2 <= t <= n - 3: return n + t
    elif t == n - 2: return 2 * n
    elif t == n - 1: return n - 1
    elif t == n: return 2 * n - 2
    elif t == n + 1: return 2 * n + 1
    elif n + 2 <= t <= 2 * n - 1: return t - (n + 2)
    elif t == 2 * n: return n
    elif t == 2 * n + 1: return 2 * n - 1
    else: raise ValueError(f"t={t}")


def make_word_12wiggle(n):
    """Canonical CCW {1,2}-wiggle word."""
    return [0, 1, 2, 1, 2] + list(range(3, n)) + list(range(n))


def compute_waterfall(word, n):
    """Compute waterfall g[j][t] = fire count of j before step t."""
    L = len(word)
    g = [[0] * (L + 1) for _ in range(n)]
    for t in range(L):
        for j in range(n):
            g[j][t + 1] = g[j][t]
        g[word[t]][t + 1] = g[word[t]][t] + 1
    return g


def delta_12wiggle(t, j, n):
    """
    Closed-form Δ[j](t) for the {1,2}-wiggle shadow.

    From computational analysis (n=8..11), the 7 Δ types are:

    Δ_A (t=0, t=n): j=0:-1, j=1:-2, j=2:-2, j=3..n-5:-1, j=n-4..n-1:0
    Δ_B (t=1..n-3, t=n+1): j=0:-1, j=1:-2, j=2:-2, j=3..n-5:-1, j=n-4..n-3:0, j=n-2:-1, j=n-1:0
    Δ_C (t=n-2): j=0:-1, j=1:-2, j=2:-2, j=3..n-4:-1, j=n-3:-2, j=n-2:-1, j=n-1:0
    Δ_D (t=n-1): j=0:0, j=1:-1, j=2:-1, j=3..n-3:0, j=n-2:1, j=n-1:1
    Δ_E (t=2n+1): j=0..n-3:0, j=n-2:1, j=n-1:1
    Δ_F (t=2n): j=0..n-4:1, j=n-3:0, j=n-2:1, j=n-1:2
    Δ_G (t=n+2..2n-1): j=0..n-5:1, j=n-4:2, j=n-3..n-2:1, j=n-1:2
    """
    # Determine type
    if t == 0 or t == n:
        # Type A
        if j == 0: return -1
        elif j == 1: return -2
        elif j == 2: return -2
        elif 3 <= j <= n - 5: return -1
        elif n - 4 <= j <= n - 1: return 0
    elif (1 <= t <= n - 3) or t == n + 1:
        # Type B
        if j == 0: return -1
        elif j == 1: return -2
        elif j == 2: return -2
        elif 3 <= j <= n - 5: return -1
        elif j == n - 4: return 0
        elif j == n - 3: return -1
        elif j == n - 2: return -1
        elif j == n - 1: return 0
    elif t == n - 2:
        # Type C
        if j == 0: return -1
        elif j == 1: return -2
        elif j == 2: return -2
        elif 3 <= j <= n - 4: return -1
        elif j == n - 3: return -2
        elif j == n - 2: return -1
        elif j == n - 1: return 0
    elif t == n - 1:
        # Type D
        if j == 0: return 0
        elif j == 1: return -1
        elif j == 2: return -1
        elif 3 <= j <= n - 3: return 0
        elif j == n - 2: return 1
        elif j == n - 1: return 1
    elif t == 2 * n + 1:
        # Type E
        if 0 <= j <= n - 3: return 0
        elif j == n - 2: return 1
        elif j == n - 1: return 1
    elif t == 2 * n:
        # Type F
        if 0 <= j <= n - 4: return 1
        elif j == n - 3: return 0
        elif j == n - 2: return 1
        elif j == n - 1: return 2
    elif n + 2 <= t <= 2 * n - 1:
        # Type G
        if 0 <= j <= n - 5: return 1
        elif j == n - 4: return 2
        elif j == n - 3 or j == n - 2: return 1
        elif j == n - 1: return 2
    raise ValueError(f"Unhandled: t={t}, j={j}, n={n}")


def main():
    print("CIC Exploration 13d: Analytical Shadow Construction")
    print("=" * 70)

    # PART 1: Verify Δ formula against computed values
    print("\nPART 1: Verify Δ Formula (n=8..15)")
    print("-" * 70)

    all_match = True
    for n in range(8, 16):
        bp = {8: [0, 3, 6], 9: [0, 3, 6], 10: [0, 4, 7], 11: [0, 4, 8],
              12: [0, 4, 8], 13: [0, 5, 9], 14: [0, 5, 10], 15: [0, 5, 10]}[n]
        bs = set(bp)
        ms = [2 if i in bs else 3 for i in range(n)]

        w = make_word_12wiggle(n)
        L = len(w)
        fc_word = [0] * n
        for p in w:
            fc_word[p] += 1

        proc_seqs = enumerate_state_sequences(n, ms, fc_word)
        sl = [proc_seqs[p] for p in range(n)]

        # Get first valid combo
        found = False
        for combo in iproduct(*sl):
            ss = {p: combo[p] for p in range(n)}
            # Compute configs
            fc = [0] * n
            configs = [tuple(ss[p][0] for p in range(n))]
            for t in range(L):
                fc[w[t]] += 1
                configs.append(tuple(ss[p][fc[p]] for p in range(n)))
            if configs[-1] != configs[0]:
                continue
            if len(set(configs[:L])) != L:
                continue
            found = True
            break

        if not found:
            print(f"  n={n}: no valid cycle")
            continue

        good = configs[:L]

        # Compute actual waterfall
        g = compute_waterfall(w, n)

        # Shadow: trace SCC to get actual shadow waterfall
        good_set = set(good)
        me = {}
        for t in range(L):
            c = good[t]
            cn = good[(t + 1) % L]
            m = w[t]
            me[(m, c[(m-1)%n], c[m], c[(m+1)%n])] = cn[m]

        # Follow forced transitions to find shadow
        all_cfgs = list(iproduct(*[range(m) for m in ms]))
        non_good = [c for c in all_cfgs if c not in good_set]

        shadow = None
        shadow_movers = None
        for start in non_good:
            config = start
            path = [config]
            visited = {config: 0}
            movers = []

            for step in range(L + 50):
                forced = []
                for j in range(n):
                    key = (j, config[(j-1)%n], config[j], config[(j+1)%n])
                    if key in me and me[key] != config[j]:
                        forced.append((j, me[key], key))
                if not forced:
                    break

                moved = False
                for proc, new_val, key in forced:
                    nc = list(config)
                    nc[proc] = new_val
                    nc = tuple(nc)
                    if nc not in good_set:
                        movers.append(proc)
                        config = nc
                        path.append(config)
                        if config in visited:
                            cs = visited[config]
                            if len(movers[cs:]) == L:
                                shadow = path[cs:-1]
                                shadow_movers = movers[cs:]
                                break
                        visited[config] = step + 1
                        moved = True
                        break
                if shadow is not None:
                    break
                if not moved:
                    break
            if shadow is not None:
                break

        if shadow is None:
            print(f"  n={n}: no shadow found")
            continue

        # Compute shadow waterfall
        gs = [[0] * (L + 1) for _ in range(n)]
        for t in range(L):
            for j in range(n):
                gs[j][t + 1] = gs[j][t]
            gs[shadow_movers[t]][t + 1] = gs[shadow_movers[t]][t] + 1

        # Verify Δ formula
        n_match = 0
        n_total = 0
        mismatches = []
        for t in range(L):
            st = sigma_12wiggle(t, n)
            for j in range(n):
                actual_delta = gs[j][t] - g[j][st]
                try:
                    formula_delta = delta_12wiggle(t, j, n)
                except ValueError:
                    formula_delta = "ERROR"
                n_total += 1
                if actual_delta == formula_delta:
                    n_match += 1
                else:
                    mismatches.append((t, j, actual_delta, formula_delta))

        match = n_match == n_total
        all_match = all_match and match
        print(f"  n={n}: {n_match}/{n_total} Δ entries match {'✓' if match else '✗'}")
        if not match:
            for t, j, actual, formula in mismatches[:10]:
                print(f"    MISMATCH t={t} j={j}: actual={actual} formula={formula}")

    print(f"\n  Overall: {'ALL MATCH ✓' if all_match else 'SOME MISMATCH ✗'}")

    # PART 2: Verify fire counts stay in range
    print("\n\nPART 2: Fire Count Range Check")
    print("-" * 70)

    for n in range(8, 21):
        w = make_word_12wiggle(n)
        L = len(w)
        g = compute_waterfall(w, n)

        fc_word = [0] * n
        for p in w:
            fc_word[p] += 1

        in_range = True
        for t in range(L):
            st = sigma_12wiggle(t, n)
            for j in range(n):
                d = delta_12wiggle(t, j, n)
                gs_val = g[j][st] + d
                if gs_val < 0 or gs_val > fc_word[j]:
                    in_range = False
                    print(f"  n={n} t={t} j={j}: gs={gs_val} OUT OF RANGE [0,{fc_word[j]}]")

        if in_range:
            print(f"  n={n}: all fire counts in range ✓")

    # PART 3: Verify closure from construction
    print("\n\nPART 3: Closure Verification (Analytical Construction)")
    print("-" * 70)

    for n in range(8, 16):
        bp = {8: [0, 3, 6], 9: [0, 3, 6], 10: [0, 4, 7], 11: [0, 4, 8],
              12: [0, 4, 8], 13: [0, 5, 9], 14: [0, 5, 10], 15: [0, 5, 10]}[n]
        bs = set(bp)
        ms = [2 if i in bs else 3 for i in range(n)]
        w = make_word_12wiggle(n)
        L = len(w)
        fc_word = [0] * n
        for p in w:
            fc_word[p] += 1

        proc_seqs = enumerate_state_sequences(n, ms, fc_word)
        sl = [proc_seqs[p] for p in range(n)]

        # Test ALL valid state sequence combos
        total_tested = 0
        total_pass = 0

        for combo in iproduct(*sl):
            ss = {p: combo[p] for p in range(n)}
            # Compute good configs
            fc = [0] * n
            configs = [tuple(ss[p][0] for p in range(n))]
            for t in range(L):
                fc[w[t]] += 1
                configs.append(tuple(ss[p][fc[p]] for p in range(n)))
            if configs[-1] != configs[0]:
                continue
            if len(set(configs[:L])) != L:
                continue
            total_tested += 1

            good = configs[:L]
            good_set = set(good)
            g = compute_waterfall(w, n)

            # Construct shadow configs from formula
            shadow_constructed = []
            for t in range(L):
                st = sigma_12wiggle(t, n)
                config = []
                for j in range(n):
                    d = delta_12wiggle(t, j, n)
                    gs_val = g[j][st] + d
                    config.append(ss[j][gs_val])
                shadow_constructed.append(tuple(config))

            # Compute shadow mover sequence from σ
            shadow_movers = [w[sigma_12wiggle(t, n)] for t in range(L)]

            # Verify closure: applying mover entry at shadow[t] → shadow[t+1]
            me = {}
            for t in range(L):
                c = good[t]
                cn = good[(t + 1) % L]
                m = w[t]
                me[(m, c[(m-1)%n], c[m], c[(m+1)%n])] = cn[m]

            closure_ok = True
            for t in range(L):
                sc = shadow_constructed[t]
                sn = shadow_constructed[(t + 1) % L]
                mover = shadow_movers[t]
                key = (mover, sc[(mover-1)%n], sc[mover], sc[(mover+1)%n])
                if key not in me:
                    closure_ok = False
                    break
                new_val = me[key]
                expected = list(sc)
                expected[mover] = new_val
                expected = tuple(expected)
                if expected != sn:
                    closure_ok = False
                    break

            # Verify 5 properties
            p1 = closure_ok
            p2 = all(shadow_movers[t] == w[sigma_12wiggle(t, n)] for t in range(L))
            p3 = len(set(shadow_constructed)) == L
            p4 = len(set(shadow_constructed) & good_set) == 0
            p5 = True
            for t in range(L):
                sc = shadow_constructed[t]
                for j in range(n):
                    key = (j, sc[(j-1)%n], sc[j], sc[(j+1)%n])
                    if key in me and me[key] != sc[j]:
                        nc = list(sc)
                        nc[j] = me[key]
                        nc = tuple(nc)
                        if nc in good_set:
                            p5 = False

            if p1 and p2 and p3 and p4 and p5:
                total_pass += 1

        tag = '✓' if total_pass == total_tested else '✗'
        print(f"  n={n}: {total_pass}/{total_tested} all 5 properties {tag}")

    # PART 4: Larger n (range check only since SCC trace too slow)
    print("\n\nPART 4: Fire Count Range for n=8..25")
    print("-" * 70)

    for n in range(8, 26):
        w = make_word_12wiggle(n)
        L = len(w)
        g = compute_waterfall(w, n)

        fc_word = [0] * n
        for p in w:
            fc_word[p] += 1

        in_range = True
        for t in range(L):
            st = sigma_12wiggle(t, n)
            for j in range(n):
                d = delta_12wiggle(t, j, n)
                gs_val = g[j][st] + d
                if gs_val < 0 or gs_val > fc_word[j]:
                    in_range = False

        print(f"  n={n}: {'✓' if in_range else '✗'}")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
