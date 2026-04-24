#!/usr/bin/env python3
"""
CIC Exploration 13f: Complete Shadow Construction with Offsets.

shadow[t][j] = ss[j][(g[j][σ(t)] + Δ[j](t) + offset[j]) mod fc[j]]

where:
- σ: closed-form shadow permutation
- Δ: closed-form fire count shift
- offset: closed-form initial fire count offset
- g: waterfall matrix (from good cycle word)
- ss: state sequences (from state sequence assignment)
- fc: fire counts

This script verifies the COMPLETE construction produces valid shadow cycles
for ALL state sequence assignments, n=8..15.
"""

from itertools import product as iproduct
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


def delta_12wiggle(t, j, n):
    if t == 0 or t == n:
        if j == 0: return -1
        elif j == 1: return -2
        elif j == 2: return -2
        elif 3 <= j <= n - 5: return -1
        elif n - 4 <= j <= n - 1: return 0
    elif (1 <= t <= n - 3) or t == n + 1:
        if j == 0: return -1
        elif j == 1: return -2
        elif j == 2: return -2
        elif 3 <= j <= n - 5: return -1
        elif j == n - 4: return 0
        elif j == n - 3: return -1
        elif j == n - 2: return -1
        elif j == n - 1: return 0
    elif t == n - 2:
        if j == 0: return -1
        elif j == 1: return -2
        elif j == 2: return -2
        elif 3 <= j <= n - 4: return -1
        elif j == n - 3: return -2
        elif j == n - 2: return -1
        elif j == n - 1: return 0
    elif t == n - 1:
        if j == 0: return 0
        elif j == 1: return -1
        elif j == 2: return -1
        elif 3 <= j <= n - 3: return 0
        elif j == n - 2: return 1
        elif j == n - 1: return 1
    elif t == 2 * n + 1:
        if 0 <= j <= n - 3: return 0
        elif j == n - 2: return 1
        elif j == n - 1: return 1
    elif t == 2 * n:
        if 0 <= j <= n - 4: return 1
        elif j == n - 3: return 0
        elif j == n - 2: return 1
        elif j == n - 1: return 2
    elif n + 2 <= t <= 2 * n - 1:
        if 0 <= j <= n - 5: return 1
        elif j == n - 4: return 2
        elif j == n - 3 or j == n - 2: return 1
        elif j == n - 1: return 2
    raise ValueError(f"t={t}, j={j}, n={n}")


def offset_12wiggle(j, n):
    """Closed-form offset for {1,2}-wiggle shadow."""
    if j == 0: return 1
    elif j == 1: return 2
    elif j == 2: return 2
    elif 3 <= j <= n - 5: return 1
    elif j == n - 4: return 0
    elif j == n - 3: return 0
    elif j == n - 2: return 1
    elif j == n - 1: return 0
    raise ValueError(f"j={j}, n={n}")


def compute_waterfall(word, n):
    L = len(word)
    g = [[0] * (L + 1) for _ in range(n)]
    for t in range(L):
        for j in range(n):
            g[j][t + 1] = g[j][t]
        g[word[t]][t + 1] = g[word[t]][t] + 1
    return g


def make_word(n):
    return [0, 1, 2, 1, 2] + list(range(3, n)) + list(range(n))


def main():
    print("CIC Exploration 13f: Complete Shadow Construction")
    print("=" * 70)

    # PART 1: Verify construction for ALL state sequence combos
    print("\nPART 1: Full Construction Verification (n=8..15)")
    print("-" * 70)

    for n in range(8, 16):
        bp = {8: [0, 3, 6], 9: [0, 3, 6], 10: [0, 4, 7], 11: [0, 4, 8],
              12: [0, 4, 8], 13: [0, 5, 9], 14: [0, 5, 10],
              15: [0, 5, 10]}[n]
        bs = set(bp)
        ms = [2 if i in bs else 3 for i in range(n)]
        w = make_word(n)
        L = len(w)

        fc = [0] * n
        for p in w:
            fc[p] += 1

        g = compute_waterfall(w, n)
        proc_seqs = enumerate_state_sequences(n, ms, fc)
        sl = [proc_seqs[p] for p in range(n)]

        total = 0
        p1_pass = 0
        p2_pass = 0
        p3_pass = 0
        p4_pass = 0
        p5_pass = 0
        all_pass = 0

        for combo in iproduct(*sl):
            ss = {p: combo[p] for p in range(n)}

            # Compute good cycle
            fcc = [0] * n
            configs = [tuple(ss[p][0] for p in range(n))]
            for t in range(L):
                fcc[w[t]] += 1
                configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
            if configs[-1] != configs[0]:
                continue
            if len(set(configs[:L])) != L:
                continue

            total += 1
            good = configs[:L]
            good_set = set(good)

            # Extract mover entries
            me = {}
            for t in range(L):
                c = good[t]
                cn = good[(t + 1) % L]
                m = w[t]
                key = (m, c[(m - 1) % n], c[m], c[(m + 1) % n])
                me[key] = cn[m]

            # Construct shadow from closed-form
            shadow = []
            for t in range(L):
                st = sigma_12wiggle(t, n)
                config = []
                for j in range(n):
                    d = delta_12wiggle(t, j, n)
                    o = offset_12wiggle(j, n)
                    idx = (g[j][st] + d + o) % fc[j]
                    config.append(ss[j][idx])
                shadow.append(tuple(config))

            shadow_movers = [w[sigma_12wiggle(t, n)] for t in range(L)]

            # P1: Closure
            closure = True
            for t in range(L):
                sc = shadow[t]
                sn = shadow[(t + 1) % L]
                mover = shadow_movers[t]
                key = (mover, sc[(mover - 1) % n], sc[mover],
                       sc[(mover + 1) % n])
                if key not in me:
                    closure = False
                    break
                new_val = me[key]
                expected = list(sc)
                expected[mover] = new_val
                if tuple(expected) != sn:
                    closure = False
                    break
            if closure:
                p1_pass += 1

            # P2: Movers match
            p2 = True
            for t in range(L):
                if shadow_movers[t] != w[sigma_12wiggle(t, n)]:
                    p2 = False
                    break
            if p2:
                p2_pass += 1

            # P3: Distinct
            p3 = len(set(shadow)) == L
            if p3:
                p3_pass += 1

            # P4: Disjoint from good
            p4 = len(set(shadow) & good_set) == 0
            if p4:
                p4_pass += 1

            # P5: Escape
            p5 = True
            for t in range(L):
                sc = shadow[t]
                for j in range(n):
                    key = (j, sc[(j - 1) % n], sc[j], sc[(j + 1) % n])
                    if key in me and me[key] != sc[j]:
                        nc = list(sc)
                        nc[j] = me[key]
                        if tuple(nc) in good_set:
                            p5 = False
            if p5:
                p5_pass += 1

            if closure and p2 and p3 and p4 and p5:
                all_pass += 1

        print(f"  n={n}: {total} valid combos")
        print(f"    P1(closure):  {p1_pass}/{total}")
        print(f"    P2(movers):   {p2_pass}/{total}")
        print(f"    P3(distinct): {p3_pass}/{total}")
        print(f"    P4(disjoint): {p4_pass}/{total}")
        print(f"    P5(escape):   {p5_pass}/{total}")
        tag = '✓' if all_pass == total else '✗'
        print(f"    ALL:          {all_pass}/{total} {tag}")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
