#!/usr/bin/env python3
"""
ra13_existence_2xfc.py — Check if OW-NU consistent cycles exist
with fc = 2*ms (double fire counts). If they don't exist for any fc
multiple, the case is vacuously empty.

Also: verify that the non-existence is actually due to structural entry conflict.
"""
import time
from itertools import combinations, product as iproduct


def total_displacement(word, n):
    W = 0
    L = len(word)
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 0:
            pass
        elif diff <= n // 2:
            W += diff
        else:
            W -= (n - diff)
    return W


def step_directions(word, n):
    L = len(word)
    dirs = []
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 0:
            dirs.append(0)
        elif diff == 1:
            dirs.append(1)
        elif diff == n - 1:
            dirs.append(-1)
        else:
            dirs.append(diff if diff <= n // 2 else diff - n)
    return dirs


def gen_words(n, fc_target, max_results=200, timeout_s=10):
    """Generate +-1 ring walk words with given fire count vector."""
    target_cl = sum(fc_target)
    results = []
    t0 = time.time()
    def dfs(word, fc):
        if time.time() - t0 > timeout_s or len(results) >= max_results:
            return
        if len(word) == target_cl:
            if all(fc[p] == fc_target[p] for p in range(n)):
                results.append(tuple(word))
            return
        remaining = target_cl - len(word)
        needed = sum(max(0, fc_target[p] - fc[p]) for p in range(n))
        if needed > remaining:
            return
        last = word[-1]
        for nxt in [(last + 1) % n, (last - 1) % n]:
            if fc[nxt] < fc_target[nxt]:
                fc[nxt] += 1
                word.append(nxt)
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1
    for start in range(n):
        if time.time() - t0 > timeout_s or len(results) >= max_results:
            break
        fc = [0] * n
        fc[start] = 1
        if fc[start] <= fc_target[start]:
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


def find_consistent_cycle(word, n, ms, max_starts=30, timeout=3):
    L = len(word)
    all_starts = list(iproduct(*[range(m) for m in ms]))
    t0 = time.time()

    for start in all_starts[:max_starts]:
        if time.time() - t0 > timeout:
            break
        found = [None]
        def dfs(t, configs, trans):
            if found[0] is not None or time.time() - t0 > timeout:
                return
            if t == L:
                if tuple(configs[0]) == tuple(configs[-1]):
                    config_set = set(tuple(c) for c in configs[:L])
                    if len(config_set) == L:
                        found[0] = [tuple(c) for c in configs[:L]]
                return
            mover = word[t]
            cur = configs[t]
            old_val = cur[mover]
            for new_val in range(ms[mover]):
                if new_val == old_val:
                    continue
                nxt = list(cur)
                nxt[mover] = new_val
                consistent = True
                new_trans = dict(trans)
                for p in range(n):
                    lp, rp = (p-1)%n, (p+1)%n
                    ctx = (p, cur[lp], cur[p], cur[rp])
                    val = new_val if p == mover else cur[p]
                    if ctx in new_trans:
                        if new_trans[ctx] != val:
                            consistent = False
                            break
                    else:
                        new_trans[ctx] = val
                if not consistent:
                    continue
                nxt_t = tuple(nxt)
                if t + 1 < L:
                    if nxt_t in set(tuple(c) for c in configs[:t+1]):
                        continue
                configs.append(nxt)
                dfs(t + 1, configs, new_trans)
                configs.pop()
                if found[0] is not None:
                    return
        dfs(0, [list(start)], {})
        if found[0] is not None:
            return found[0]
    return None


def check_structural_ec(word, n, ms):
    """
    Check if the mover word STRUCTURE alone forces entry conflict.

    For each proc p, find steps where p is mover vs non-mover.
    Check if there exist steps s1 (mover) and s2 (non-mover) where
    the prefix fire count parity at p's neighbors is the same.

    For binary neighbors, this means (L, R) at s1 and s2 have
    same parity at all neighboring positions. For binary p itself,
    the self-parity is the key: at mover step, pfc(p) has some parity,
    at non-mover step, pfc(p) has same parity => same p-value => same context
    but contradictory requirement (fire vs stay).
    """
    L = len(word)

    for p in range(n):
        lp = (p - 1) % n
        rp = (p + 1) % n

        # Only works when ALL of p, lp, rp are binary (3 consecutive)
        if ms[p] != 2 or ms[lp] != 2 or ms[rp] != 2:
            continue

        mover_steps = [t for t in range(L) if word[t] == p]
        nonmover_steps = [t for t in range(L) if word[t] != p]

        # Compute prefix fire counts
        pfc = {q: [0] * (L + 1) for q in [lp, p, rp]}
        for t in range(L):
            for q in [lp, p, rp]:
                pfc[q][t + 1] = pfc[q][t] + (1 if word[t] == q else 0)

        for s1 in mover_steps:
            for s2 in nonmover_steps:
                if (pfc[lp][s1] % 2 == pfc[lp][s2] % 2 and
                    pfc[p][s1] % 2 == pfc[p][s2] % 2 and
                    pfc[rp][s1] % 2 == pfc[rp][s2] % 2):
                    return True, p

    return False, None


def check_general_ec(word, n, ms):
    """
    More general: check if ANY proc has a forced entry conflict.
    For each proc p, at each pair of steps (mover, non-mover),
    check if the accumulated config at (lp, p, rp) MUST be the same.

    For binary procs: config determined by parity of prefix fire count.
    For ternary: config determined by prefix fire count mod 3.

    Entry conflict at p: exists (s1: mover, s2: non-mover) such that
    for all q in {lp, p, rp}: pfc(q, s1) mod ms[q] == pfc(q, s2) mod ms[q].
    """
    L = len(word)

    for p in range(n):
        lp = (p - 1) % n
        rp = (p + 1) % n

        pfc = {q: [0] * (L + 1) for q in [lp, p, rp]}
        for t in range(L):
            for q in [lp, p, rp]:
                pfc[q][t + 1] = pfc[q][t] + (1 if word[t] == q else 0)

        mover_steps = [t for t in range(L) if word[t] == p]
        nonmover_steps = [t for t in range(L) if word[t] != p]

        for s1 in mover_steps:
            for s2 in nonmover_steps:
                if (pfc[lp][s1] % ms[lp] == pfc[lp][s2] % ms[lp] and
                    pfc[p][s1] % ms[p] == pfc[p][s2] % ms[p] and
                    pfc[rp][s1] % ms[rp] == pfc[rp][s2] % ms[rp]):
                    return True, p

    return False, None


def has_no_triple(ms, n):
    for i in range(n):
        if ms[i] == 2 and ms[(i+1) % n] == 2 and ms[(i+2) % n] == 2:
            return False
    return True


def main():
    print("RA13 Existence with 2x fc + Structural EC Analysis")
    print("=" * 70)

    n = 5
    ms = [2, 3, 2, 3, 2]
    print(f"n={n}, ms={ms}")

    # Part 1: Check fc = 2*ms
    print(f"\n--- fc = 2*ms ---")
    fc_2x = [2 * m for m in ms]
    words_2x = gen_words(n, fc_2x, max_results=100, timeout_s=10)
    unique_2x = {}
    for w in words_2x:
        c = canonicalize(w)
        if c not in unique_2x:
            unique_2x[c] = w

    ow_nu_2x = []
    for w in unique_2x.values():
        wl = list(w)
        W = total_displacement(wl, n)
        dirs = step_directions(wl, n)
        ns = [d for d in dirs if d != 0]
        uniform = all(d == ns[0] for d in ns) if ns else True
        if abs(W) == n and not uniform:
            ow_nu_2x.append(wl)

    print(f"Total unique words: {len(unique_2x)}")
    print(f"OW-NU words: {len(ow_nu_2x)}")

    n_found = 0
    for wl in ow_nu_2x[:20]:
        result = find_consistent_cycle(wl, n, ms, max_starts=30, timeout=3)
        if result:
            n_found += 1
            print(f"  FOUND: word={wl[:10]}..., W={total_displacement(wl, n)}")
    print(f"Consistent cycles found: {n_found}/{min(20, len(ow_nu_2x))}")

    # Part 2: Structural EC analysis on fc=ms words
    print(f"\n--- Structural EC analysis (fc=ms) ---")
    fc_1x = list(ms)
    words_1x = gen_words(n, fc_1x, max_results=200, timeout_s=5)
    unique_1x = {}
    for w in words_1x:
        c = canonicalize(w)
        if c not in unique_1x:
            unique_1x[c] = w

    ow_nu_1x = []
    for w in unique_1x.values():
        wl = list(w)
        W = total_displacement(wl, n)
        dirs = step_directions(wl, n)
        ns = [d for d in dirs if d != 0]
        uniform = all(d == ns[0] for d in ns) if ns else True
        if abs(W) == n and not uniform:
            ow_nu_1x.append(wl)

    print(f"OW-NU words: {len(ow_nu_1x)}")

    # Check structural EC (3-consecutive binary version)
    n_struct_ec = 0
    for wl in ow_nu_1x:
        has_ec, proc = check_structural_ec(wl, n, ms)
        if has_ec:
            n_struct_ec += 1
    print(f"With 3-consec-binary structural EC: {n_struct_ec}/{len(ow_nu_1x)}")

    # Check general EC (works for non-consecutive)
    n_general_ec = 0
    ec_procs = []
    for wl in ow_nu_1x:
        has_ec, proc = check_general_ec(wl, n, ms)
        if has_ec:
            n_general_ec += 1
            ec_procs.append(proc)
    print(f"With general structural EC: {n_general_ec}/{len(ow_nu_1x)}")

    if ec_procs:
        from collections import Counter
        proc_counts = Counter(ec_procs)
        print(f"EC proc distribution: {dict(proc_counts)}")

    # Part 3: Same for fc=2*ms
    print(f"\n--- Structural EC analysis (fc=2*ms) ---")
    n_general_ec_2x = 0
    for wl in ow_nu_2x:
        has_ec, proc = check_general_ec(wl, n, ms)
        if has_ec:
            n_general_ec_2x += 1
    print(f"With general structural EC: {n_general_ec_2x}/{len(ow_nu_2x)}")

    # Part 4: Also check ALL word types for comparison
    print(f"\n--- EC coverage by word type ---")
    all_words = list(unique_1x.values())
    type_ec = {}
    for wl in all_words:
        W = total_displacement(list(wl), n)
        dirs = step_directions(list(wl), n)
        ns = [d for d in dirs if d != 0]
        uniform = all(d == ns[0] for d in ns) if ns else True
        absW = abs(W)

        if absW == 0:
            cat = 'zero'
        elif absW == n and uniform:
            cat = 'ow_u'
        elif absW == n and not uniform:
            cat = 'ow_nu'
        elif absW == 2 * n:
            cat = 'sweep'
        else:
            cat = 'other'

        if cat not in type_ec:
            type_ec[cat] = [0, 0]

        has_ec, _ = check_general_ec(list(wl), n, ms)
        type_ec[cat][0] += 1
        if has_ec:
            type_ec[cat][1] += 1

    for cat in sorted(type_ec.keys()):
        total, ec = type_ec[cat]
        pct = 100.0 * ec / total if total else 0
        print(f"  {cat:10s}: {ec}/{total} have structural EC ({pct:.1f}%)")

    # Part 5: n=7 structural EC check
    print(f"\n{'='*70}")
    print(f"n=7 structural EC check")
    n7 = 7
    for ms7 in [[2, 3, 2, 3, 2, 3, 3], [2, 2, 3, 3, 2, 3, 3], [3, 2, 3, 2, 3, 2, 3]]:
        if not has_no_triple(ms7, n7):
            continue
        prod7 = 1
        for m in ms7:
            prod7 *= m
        if prod7 >= 4 * 3 ** (n7 - 2):
            continue

        words7 = gen_words(n7, ms7, max_results=200, timeout_s=5)
        unique7 = {}
        for w in words7:
            c = canonicalize(w)
            if c not in unique7:
                unique7[c] = w

        n_ow_nu = 0
        n_ec = 0
        for w in unique7.values():
            wl = list(w)
            W = total_displacement(wl, n7)
            dirs = step_directions(wl, n7)
            ns = [d for d in dirs if d != 0]
            uniform = all(d == ns[0] for d in ns) if ns else True
            if abs(W) == n7 and not uniform:
                n_ow_nu += 1
                has_ec, _ = check_general_ec(wl, n7, ms7)
                if has_ec:
                    n_ec += 1

        print(f"  ms={ms7}: {n_ec}/{n_ow_nu} OW-NU words have structural EC")


if __name__ == '__main__':
    main()
