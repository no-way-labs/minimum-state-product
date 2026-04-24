#!/usr/bin/env python3
"""Debug: why does the analytical shadow construction fail closure?"""

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
        raise ValueError(f"t={t}")


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
    raise ValueError(f"Unhandled: t={t}, j={j}, n={n}")


def compute_waterfall(word, n):
    L = len(word)
    g = [[0] * (L + 1) for _ in range(n)]
    for t in range(L):
        for j in range(n):
            g[j][t + 1] = g[j][t]
        g[word[t]][t + 1] = g[word[t]][t] + 1
    return g


def main():
    n = 8
    bp = [0, 3, 6]
    bs = set(bp)
    ms = [2 if i in bs else 3 for i in range(n)]
    w = [0, 1, 2, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7]
    L = len(w)

    fc_word = [0] * n
    for p in w:
        fc_word[p] += 1

    proc_seqs = enumerate_state_sequences(n, ms, fc_word)
    sl = [proc_seqs[p] for p in range(n)]

    # Get first valid combo
    for combo in iproduct(*sl):
        ss = {p: combo[p] for p in range(n)}
        fc = [0] * n
        configs = [tuple(ss[p][0] for p in range(n))]
        for t in range(L):
            fc[w[t]] += 1
            configs.append(tuple(ss[p][fc[p]] for p in range(n)))
        if configs[-1] != configs[0]:
            continue
        if len(set(configs[:L])) != L:
            continue
        break

    good = configs[:L]
    good_set = set(good)
    g = compute_waterfall(w, n)

    # Extract mover entries from good cycle
    me = {}
    for t in range(L):
        c = good[t]
        cn = good[(t + 1) % L]
        m = w[t]
        key = (m, c[(m - 1) % n], c[m], c[(m + 1) % n])
        me[key] = cn[m]

    # Construct shadow from formula
    shadow = []
    for t in range(L):
        st = sigma_12wiggle(t, n)
        config = []
        for j in range(n):
            d = delta_12wiggle(t, j, n)
            gs_val = g[j][st] + d
            config.append(ss[j][gs_val])
        shadow.append(tuple(config))

    shadow_movers = [w[sigma_12wiggle(t, n)] for t in range(L)]

    # Also extract actual shadow via SCC trace
    all_cfgs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_cfgs if c not in good_set]

    actual_shadow = None
    actual_movers = None
    for start in non_good:
        config = start
        path = [config]
        visited = {config: 0}
        movers = []

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
                    movers.append(proc)
                    config = nc
                    path.append(config)
                    if config in visited:
                        cs = visited[config]
                        if len(movers[cs:]) == L:
                            actual_shadow = path[cs:-1]
                            actual_movers = movers[cs:]
                            break
                    visited[config] = step + 1
                    moved = True
                    break
            if actual_shadow is not None:
                break
            if not moved:
                break
        if actual_shadow is not None:
            break

    print("State sequences:")
    for p in range(n):
        print(f"  proc {p}: {ss[p]}")

    print(f"\nConstructed shadow vs Actual shadow:")
    print(f"  {'t':>3} {'c_mover':>7} {'a_mover':>7} "
          f"{'constructed':>30} {'actual':>30} {'match':>5}")
    for t in range(L):
        c_match = "✓" if shadow[t] == actual_shadow[t] else "✗"
        print(f"  {t:3d} {shadow_movers[t]:7d} {actual_movers[t]:7d} "
              f"{str(shadow[t]):>30} {str(actual_shadow[t]):>30} {c_match:>5}")

    # Check: is the actual shadow a rotation of the constructed one?
    print("\n  Checking rotations...")
    constructed_set = set(shadow)
    actual_set = set(actual_shadow)
    print(f"  Constructed set size: {len(constructed_set)}")
    print(f"  Actual set size: {len(actual_set)}")
    print(f"  Intersection: {len(constructed_set & actual_set)}")
    print(f"  Constructed only: {len(constructed_set - actual_set)}")
    print(f"  Actual only: {len(actual_set - constructed_set)}")

    # Check closure for constructed shadow
    print("\n  Closure check for constructed shadow:")
    for t in range(L):
        sc = shadow[t]
        sn = shadow[(t + 1) % L]
        mover = shadow_movers[t]
        key = (mover, sc[(mover - 1) % n], sc[mover], sc[(mover + 1) % n])
        if key not in me:
            print(f"  t={t}: entry {key} NOT in mover entries!")
            continue
        new_val = me[key]
        expected = list(sc)
        expected[mover] = new_val
        expected = tuple(expected)
        if expected != sn:
            print(f"  t={t}: mover={mover}, "
                  f"applied entry gives {expected}, but next is {sn}")
            # Show which positions differ
            for j in range(n):
                if expected[j] != sn[j]:
                    print(f"    pos {j}: expected {expected[j]}, got {sn[j]}")

    # Check closure for actual shadow
    print("\n  Closure check for actual shadow:")
    fails = 0
    for t in range(L):
        sc = actual_shadow[t]
        sn = actual_shadow[(t + 1) % L]
        mover = actual_movers[t]
        key = (mover, sc[(mover - 1) % n], sc[mover], sc[(mover + 1) % n])
        if key not in me:
            print(f"  t={t}: entry NOT found")
            fails += 1
            continue
        new_val = me[key]
        expected = list(sc)
        expected[mover] = new_val
        expected = tuple(expected)
        if expected != sn:
            print(f"  t={t}: FAIL")
            fails += 1
    if fails == 0:
        print("  All pass ✓")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
