#!/usr/bin/env python3
"""
CIC Exploration 13c: Closed-Form Shadow Permutation for Wiggle Words.

From 13a+13b: σ_wiggle exists, is state-sequence-independent, and MNU is trivially true.

This script:
1. Derives closed-form σ for the canonical CCW {1,2}-wiggle word
2. Tests the formula for n=7..15
3. Generalizes to other wiggle positions via symmetry
4. Constructs shadow configs explicitly via waterfall + offset
5. Proves closure and movers from the construction
"""

from itertools import product as iproduct
from collections import Counter, defaultdict
import sys


def generate_wiggle_words(n, binary_positions):
    binary_set = set(binary_positions)
    words = set()
    for direction in [+1, -1]:
        base = [(i * direction) % n for i in range(2 * n)]
        for insert_pos in range(2 * n):
            p = base[insert_pos]
            next_p = base[(insert_pos + 1) % (2 * n)]
            step = (next_p - p) % n
            if step == 1:
                bounce = (p - 1) % n
            elif step == n - 1:
                bounce = (p + 1) % n
            else:
                continue
            if p in binary_set or bounce in binary_set:
                continue
            word = list(base[:insert_pos + 1]) + [bounce, p] + list(base[insert_pos + 1:])
            L = len(word)
            valid = True
            for i in range(L):
                diff = abs(word[i] - word[(i + 1) % L])
                if diff != 1 and diff != n - 1:
                    valid = False
                    break
            if not valid:
                continue
            mc = Counter(word)
            if not all(mc.get(q, 0) >= 2 for q in range(n)):
                continue
            if not all(mc.get(b, 0) % 2 == 0 for b in binary_positions):
                continue
            min_idx = word.index(min(word))
            rotated = word[min_idx:] + word[:min_idx]
            words.add(tuple(rotated))
    return [list(w) for w in sorted(words)]


def get_fire_counts(word, n):
    fc = [0] * n
    for p in word:
        fc[p] += 1
    return fc


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


def compute_configs(word, n, ms, state_seqs):
    L = len(word)
    fc = [0] * n
    configs = []
    config = tuple(state_seqs[p][0] for p in range(n))
    configs.append(config)
    for t in range(L):
        mover = word[t]
        fc[mover] += 1
        config = tuple(state_seqs[p][fc[p]] for p in range(n))
        configs.append(config)
    return configs


def check_valid_cycle(configs, L):
    if configs[-1] != configs[0]:
        return False
    return len(set(configs[:L])) == L


def extract_shadow_permutation(word, n, ms, state_seqs):
    cfgs = compute_configs(word, n, ms, state_seqs)
    L = len(word)
    if not check_valid_cycle(cfgs, L):
        return None, None, None

    cycle_configs = cfgs[:L]
    good_set = set(cycle_configs)

    me = {}
    for i in range(L):
        c = cycle_configs[i]
        cn = cycle_configs[(i + 1) % L]
        m = word[i]
        key = (m, c[(m - 1) % n], c[m], c[(m + 1) % n])
        me[key] = cn[m]

    all_cfgs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_cfgs if c not in good_set]

    for start in non_good:
        config = start
        path = [config]
        visited = {config: 0}
        movers_used = []
        entry_keys_used = []

        for step in range(L + 50):
            forced = []
            for j in range(n):
                key = (j, config[(j - 1) % n], config[j], config[(j + 1) % n])
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
                    movers_used.append(proc)
                    entry_keys_used.append(key)
                    config = nc
                    path.append(config)
                    if config in visited:
                        cs = visited[config]
                        cycle_movers = movers_used[cs:]
                        cycle_keys = entry_keys_used[cs:]

                        if len(cycle_movers) == L:
                            good_keys = []
                            for i in range(L):
                                c = cfgs[i]
                                m = word[i]
                                gk = (m, c[(m-1)%n], c[m], c[(m+1)%n])
                                good_keys.append(gk)

                            sigma = [None] * L
                            used_good = [False] * L
                            for t in range(L):
                                sk = cycle_keys[t]
                                for g in range(L):
                                    if not used_good[g] and good_keys[g] == sk:
                                        sigma[t] = g
                                        used_good[g] = True
                                        break

                            return cycle_movers, sigma, path[cs:-1]
                    visited[config] = step + 1
                    moved = True
                    break
            if not moved:
                break

    return None, None, None


def sigma_formula_12wiggle(t, n):
    """
    Closed-form σ for the canonical CCW {1,2}-wiggle word:
    w = [0, 1, 2, 1, 2, 3, 4, ..., n-1, 0, 1, 2, 3, 4, ..., n-1]
    L = 2n+2.

    σ(t) =
      n-2           if t = 0
      n+1           if t = 1
      n+t           if 2 ≤ t ≤ n-3
      2n            if t = n-2
      n-1           if t = n-1   (FIXED POINT)
      2n-2          if t = n
      2n+1          if t = n+1
      t-(n+2)       if n+2 ≤ t ≤ 2n-1
      n             if t = 2n
      2n-1          if t = 2n+1
    """
    L = 2 * n + 2
    if t == 0:
        return n - 2
    elif t == 1:
        return n + 1
    elif 2 <= t <= n - 3:
        return n + t
    elif t == n - 2:
        return 2 * n
    elif t == n - 1:
        return n - 1
    elif t == n:
        return 2 * n - 2
    elif t == n + 1:
        return 2 * n + 1
    elif n + 2 <= t <= 2 * n - 1:
        return t - (n + 2)
    elif t == 2 * n:
        return n
    elif t == 2 * n + 1:
        return 2 * n - 1
    else:
        raise ValueError(f"t={t} out of range for L={L}")


def main():
    print("CIC Exploration 13c: Closed-Form Wiggle Shadow Permutation")
    print("=" * 70)

    # PART 1: Verify closed-form σ for CCW {1,2}-wiggle
    print("\nPART 1: Verify Closed-Form σ for {1,2}-wiggle (n=8..15)")
    print("-" * 70)

    for n in range(8, 16):
        bp = [0, 3, 6] if n <= 9 else [0, max(3, n//3), max(6, 2*n//3)]
        # Need valid non-adjacent bp with ≥3 binary
        # Use evenly spaced for general n
        if n <= 9:
            bp = [0, 3, 6]
        elif n == 10:
            bp = [0, 4, 7]
        elif n == 11:
            bp = [0, 4, 8]
        elif n == 12:
            bp = [0, 4, 8]
        elif n == 13:
            bp = [0, 5, 9]
        elif n == 14:
            bp = [0, 5, 10]
        elif n == 15:
            bp = [0, 5, 10]

        # Verify bp non-adjacent
        bp_set = set(bp)
        ok = True
        for b in bp:
            if (b+1) % n in bp_set or (b-1) % n in bp_set:
                ok = False
        if not ok:
            print(f"  n={n}: bp={bp} NOT non-adjacent, skip")
            continue

        ms = [2 if i in bp_set else 3 for i in range(n)]

        # Find the specific CCW {1,2}-wiggle word
        words = generate_wiggle_words(n, bp)
        # Look for the canonical form: [0, 1, 2, 1, 2, 3, ..., n-1, 0, 1, 2, ..., n-1]
        target = [0, 1, 2, 1, 2] + list(range(3, n)) + list(range(n))
        target_found = target in words

        if not target_found:
            # Try to find any {1,2}-wiggle word
            found = False
            for w in words:
                fc = get_fire_counts(w, n)
                wp = [p for p in range(n) if fc[p] == 3]
                if set(wp) == {1, 2}:
                    target = w
                    found = True
                    break
            if not found:
                print(f"  n={n} bp={bp}: no {1,2}-wiggle word found")
                continue

        w = target
        L = len(w)
        fc = get_fire_counts(w, n)
        proc_seqs = enumerate_state_sequences(n, ms, fc)
        sl = [proc_seqs[p] for p in range(n)]

        for combo in iproduct(*sl):
            ss = {p: combo[p] for p in range(n)}
            sm, sigma_actual, sc = extract_shadow_permutation(w, n, ms, ss)
            if sigma_actual is not None:
                break
        else:
            print(f"  n={n}: no valid cycle found")
            continue

        # Compare with formula
        sigma_formula = [sigma_formula_12wiggle(t, n) for t in range(L)]
        match = sigma_actual == sigma_formula
        print(f"  n={n} L={L}: formula {'✓' if match else '✗'}", end="")
        if not match:
            print(f"\n    actual:  {sigma_actual}")
            print(f"    formula: {sigma_formula}")
            # Show where they differ
            for t in range(L):
                if sigma_actual[t] != sigma_formula[t]:
                    print(f"    DIFF at t={t}: actual={sigma_actual[t]} formula={sigma_formula[t]}")
        else:
            print()

    # PART 2: All wiggle words at n=7,8 — find the general pattern
    print("\n\nPART 2: All Wiggle Words — General Pattern")
    print("-" * 70)

    for n, bp in [(7, [0, 2, 4]), (8, [0, 3, 6])]:
        bs = set(bp)
        ms = [2 if i in bs else 3 for i in range(n)]
        words = generate_wiggle_words(n, bp)

        print(f"\n  n={n} bp={bp}: {len(words)} wiggle words")

        for w in words:
            fc = get_fire_counts(w, n)
            wp = sorted([p for p in range(n) if fc[p] == 3])
            proc_seqs = enumerate_state_sequences(n, ms, fc)
            sl = [proc_seqs[p] for p in range(n)]

            for combo in iproduct(*sl):
                ss = {p: combo[p] for p in range(n)}
                sm, sigma, sc = extract_shadow_permutation(w, n, ms, ss)
                if sigma is not None:
                    break
            else:
                continue

            L = len(w)
            # Identify the wiggle structure
            # Find where the bounce is in the word
            # The bounce creates a pattern ..., a, b, a, ... where b is the bounce target
            bounce_pos = None
            for i in range(1, L - 1):
                if w[i - 1] == w[i + 1] and w[i] != w[i - 1]:
                    bounce_pos = i
                    break

            # Direction: check if main sweep is CW or CCW
            non_bounce_diffs = []
            for i in range(L):
                if i != bounce_pos and (bounce_pos is None or i != bounce_pos - 1):
                    d = (w[(i + 1) % L] - w[i]) % n
                    non_bounce_diffs.append(d)

            cw_count = sum(1 for d in non_bounce_diffs if d == 1)
            ccw_count = sum(1 for d in non_bounce_diffs if d == n - 1)
            direction = "CCW" if ccw_count > cw_count else "CW"

            print(f"  word={w} wiggle={wp} bounce@{bounce_pos} dir={direction}")
            print(f"    σ={sigma}")

    # PART 3: Waterfall-based shadow config construction
    print("\n\nPART 3: Waterfall Shadow Config Construction")
    print("-" * 70)

    for n in [8, 9, 10]:
        bp = [0, 3, 6] if n <= 9 else [0, 4, 7]
        bs = set(bp)
        ms = [2 if i in bs else 3 for i in range(n)]

        w = [0, 1, 2, 1, 2] + list(range(3, n)) + list(range(n))
        L = len(w)
        fc = get_fire_counts(w, n)
        proc_seqs = enumerate_state_sequences(n, ms, fc)
        sl = [proc_seqs[p] for p in range(n)]

        for combo in iproduct(*sl):
            ss = {p: combo[p] for p in range(n)}
            cfgs = compute_configs(w, n, ms, ss)
            if check_valid_cycle(cfgs, L):
                break

        good = cfgs[:L]
        good_set = set(good)

        # Extract shadow
        sm, sigma, shadow = extract_shadow_permutation(w, n, ms, ss)
        if sigma is None:
            print(f"  n={n}: no shadow found")
            continue

        print(f"\n  n={n} L={L}")
        print(f"  Waterfall of good cycle (fire count of j before step t):")

        # Compute waterfall
        g = [[0] * (L + 1) for _ in range(n)]
        for t in range(L):
            for j in range(n):
                g[j][t + 1] = g[j][t]
            g[w[t]][t + 1] = g[w[t]][t] + 1

        # Compute shadow waterfall
        gs = [[0] * (L + 1) for _ in range(n)]
        for t in range(L):
            for j in range(n):
                gs[j][t + 1] = gs[j][t]
            gs[sm[t]][t + 1] = gs[sm[t]][t] + 1

        # Key question: how does shadow config[t][j] relate to
        # good config at some shifted position?
        print(f"\n  Shadow config[t] = state_seqs[j][gs[j][t]] for each j")
        print(f"  Good config[σ(t)] = state_seqs[j][g[j][σ(t)]] for each j")
        print(f"  Difference in fire counts: gs[j][t] - g[j][σ(t)]")
        print()
        print(f"  {'t':>3} {'σ(t)':>5} {'mover':>6}", end="")
        for j in range(n):
            print(f"  Δg[{j}]", end="")
        print()

        for t in range(L):
            st = sigma[t]
            print(f"  {t:3d} {st:5d} {sm[t]:6d}", end="")
            for j in range(n):
                delta = gs[j][t] - g[j][st]
                print(f"  {delta:5d}", end="")
            print()

    # PART 4: Shadow config = good[σ(t)] with fire count shift
    print("\n\nPART 4: Fire Count Shift Pattern")
    print("-" * 70)

    for n in [8, 9, 10, 11]:
        bp = {8: [0, 3, 6], 9: [0, 3, 6], 10: [0, 4, 7], 11: [0, 4, 8]}[n]
        bs = set(bp)
        ms = [2 if i in bs else 3 for i in range(n)]

        w = [0, 1, 2, 1, 2] + list(range(3, n)) + list(range(n))
        L = len(w)
        fc_word = get_fire_counts(w, n)
        proc_seqs = enumerate_state_sequences(n, ms, fc_word)
        sl = [proc_seqs[p] for p in range(n)]

        for combo in iproduct(*sl):
            ss = {p: combo[p] for p in range(n)}
            cfgs = compute_configs(w, n, ms, ss)
            if check_valid_cycle(cfgs, L):
                break

        good = cfgs[:L]
        good_set = set(good)
        sm, sigma, shadow = extract_shadow_permutation(w, n, ms, ss)
        if sigma is None:
            continue

        # Compute waterfalls
        g = [[0] * (L + 1) for _ in range(n)]
        for t in range(L):
            for j in range(n):
                g[j][t + 1] = g[j][t]
            g[w[t]][t + 1] = g[w[t]][t] + 1

        gs = [[0] * (L + 1) for _ in range(n)]
        for t in range(L):
            for j in range(n):
                gs[j][t + 1] = gs[j][t]
            gs[sm[t]][t + 1] = gs[sm[t]][t] + 1

        # For each t, compute Δ[j] = gs[j][t] - g[j][σ(t)]
        # The shadow config at t is determined by gs[j][t] for each j.
        # state_seqs[j][gs[j][t]] = shadow[t][j]
        # state_seqs[j][g[j][σ(t)]] = good[σ(t)][j]
        # So shadow[t][j] ≠ good[σ(t)][j] iff gs[j][t] ≠ g[j][σ(t)] (mod fire count)

        # Key: for BINARY procs, state_seqs is [0,1,0] so state depends on fc mod 2
        # For TERNARY 2-fire procs, state_seqs is [0,x,0] so state depends on fc (0,1,2)
        # The Δ tells us the shift in the state sequence

        # Collect all delta vectors
        deltas = []
        for t in range(L):
            st = sigma[t]
            delta = tuple(gs[j][t] - g[j][st] for j in range(n))
            deltas.append(delta)

        unique_deltas = sorted(set(deltas))
        print(f"\n  n={n}: {len(unique_deltas)} unique Δ vectors")
        for d in unique_deltas:
            count = deltas.count(d)
            print(f"    Δ={d} appears {count} times")

    # PART 5: Can we express Δ as a function of t?
    print("\n\nPART 5: Δ(t) as a function of t")
    print("-" * 70)

    for n in [9, 11]:
        bp = {9: [0, 3, 6], 11: [0, 4, 8]}[n]
        bs = set(bp)
        ms = [2 if i in bs else 3 for i in range(n)]

        w = [0, 1, 2, 1, 2] + list(range(3, n)) + list(range(n))
        L = len(w)
        fc_word = get_fire_counts(w, n)
        proc_seqs = enumerate_state_sequences(n, ms, fc_word)
        sl = [proc_seqs[p] for p in range(n)]

        for combo in iproduct(*sl):
            ss = {p: combo[p] for p in range(n)}
            cfgs = compute_configs(w, n, ms, ss)
            if check_valid_cycle(cfgs, L):
                break

        good = cfgs[:L]
        sm, sigma, shadow = extract_shadow_permutation(w, n, ms, ss)
        if sigma is None:
            continue

        g = [[0] * (L + 1) for _ in range(n)]
        for t in range(L):
            for j in range(n):
                g[j][t + 1] = g[j][t]
            g[w[t]][t + 1] = g[w[t]][t] + 1

        gs = [[0] * (L + 1) for _ in range(n)]
        for t in range(L):
            for j in range(n):
                gs[j][t + 1] = gs[j][t]
            gs[sm[t]][t + 1] = gs[sm[t]][t] + 1

        print(f"\n  n={n} L={L}")
        print(f"  {'t':>3} {'σ(t)':>5} {'Δ':>40} {'mover':>6} {'σ-mover':>8}")
        for t in range(L):
            st = sigma[t]
            delta = tuple(gs[j][t] - g[j][st] for j in range(n))
            # Show which component changed
            print(f"  {t:3d} {st:5d} {str(delta):>40} {sm[t]:6d} {w[st]:8d}")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
