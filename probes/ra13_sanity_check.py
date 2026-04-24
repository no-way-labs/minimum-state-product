#!/usr/bin/env python3
"""
ra13_sanity_check.py — Sanity check: do consistent good cycles exist AT ALL
for various multisets? Test sweep + non-adjacent binary + consecutive binary.
"""
from itertools import product as iproduct, combinations


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


def gen_words(n, ms, max_results=500, timeout_s=10):
    import time
    target_cl = sum(ms)
    results = []
    t0 = time.time()
    def dfs(word, fc):
        if time.time() - t0 > timeout_s or len(results) >= max_results:
            return
        if len(word) == target_cl:
            if all(fc[p] == ms[p] for p in range(n)):
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
        if time.time() - t0 > timeout_s or len(results) >= max_results:
            break
        fc = [0] * n
        fc[start] = 1
        if fc[start] <= ms[start]:
            dfs([start], fc)
    return results


def find_consistent_cycle(word, n, ms, max_starts=72):
    """Try to find a transition-consistent config sequence for this mover word."""
    L = len(word)
    all_starts = list(iproduct(*[range(m) for m in ms]))

    for start in all_starts[:max_starts]:
        found = [None]

        def dfs(t, configs, trans):
            if found[0] is not None:
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
                    lp, rp = (p - 1) % n, (p + 1) % n
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


def main():
    print("RA13 Sanity Check: Which cycle types have consistent instances?")
    print("=" * 70)

    # Test 1: Known good system — Sol3v1 at n=5: ms=[2,3,3,3,3]
    # This is a VALID system, so it MUST have a consistent good cycle.
    n = 5
    ms = [2, 3, 3, 3, 3]
    print(f"\n--- Test 1: Sol3v1, n={n}, ms={ms} ---")
    words = gen_words(n, ms, max_results=100, timeout_s=5)
    print(f"Words: {len(words)}")

    for w in words[:10]:
        wl = list(w)
        W = total_displacement(wl, n)
        result = find_consistent_cycle(wl, n, ms)
        if result:
            dirs = step_directions(wl, n)
            ns = [d for d in dirs if d != 0]
            uniform = all(d == ns[0] for d in ns) if ns else True
            print(f"  word W={W}, uniform={uniform}: FOUND consistent cycle")
            break
    else:
        print("  No consistent cycle found in first 10 words")

    # Test 2: Non-adjacent binary at n=5: ms=[2,3,2,3,2]
    ms2 = [2, 3, 2, 3, 2]
    print(f"\n--- Test 2: n={n}, ms={ms2} (3 non-adj binary) ---")
    words2 = gen_words(n, ms2, max_results=100, timeout_s=5)
    print(f"Words: {len(words2)}")

    counts = {'ow_nu': 0, 'ow_u': 0, 'sweep': 0, 'zero': 0, 'other': 0}
    consistent_counts = {'ow_nu': 0, 'ow_u': 0, 'sweep': 0, 'zero': 0, 'other': 0}

    for w in words2:
        wl = list(w)
        W = total_displacement(wl, n)
        dirs = step_directions(wl, n)
        ns = [d for d in dirs if d != 0]
        uniform = all(d == ns[0] for d in ns) if ns else True
        absW = abs(W)

        if absW == 0:
            cat = 'zero'
        elif absW == n:
            cat = 'ow_u' if uniform else 'ow_nu'
        elif absW == 2 * n:
            cat = 'sweep'
        else:
            cat = 'other'
        counts[cat] += 1

        result = find_consistent_cycle(wl, n, ms2)
        if result:
            consistent_counts[cat] += 1

    print("Word counts and consistent cycle existence:")
    for cat in ['zero', 'ow_u', 'ow_nu', 'sweep', 'other']:
        total = counts[cat]
        cons = consistent_counts[cat]
        print(f"  {cat:10s}: {total:3d} words, {cons:3d} have consistent cycles")

    # Test 3: Same at n=7
    n7 = 7
    ms7 = [2, 3, 2, 3, 2, 3, 3]
    print(f"\n--- Test 3: n={n7}, ms={ms7} (3 non-adj binary) ---")
    words7 = gen_words(n7, ms7, max_results=200, timeout_s=10)
    print(f"Words: {len(words7)}")

    counts7 = {'ow_nu': 0, 'ow_u': 0, 'sweep': 0, 'zero': 0, 'other': 0}
    consistent7 = {'ow_nu': 0, 'ow_u': 0, 'sweep': 0, 'zero': 0, 'other': 0}

    for w in words7[:50]:
        wl = list(w)
        W = total_displacement(wl, n7)
        dirs = step_directions(wl, n7)
        ns = [d for d in dirs if d != 0]
        uniform = all(d == ns[0] for d in ns) if ns else True
        absW = abs(W)

        if absW == 0:
            cat = 'zero'
        elif absW == n7:
            cat = 'ow_u' if uniform else 'ow_nu'
        elif absW == 2 * n7:
            cat = 'sweep'
        else:
            cat = 'other'
        counts7[cat] += 1

        result = find_consistent_cycle(wl, n7, ms7, max_starts=20)
        if result:
            consistent7[cat] += 1

    print("Word counts and consistent cycle existence (first 50):")
    for cat in ['zero', 'ow_u', 'ow_nu', 'sweep', 'other']:
        total = counts7[cat]
        cons = consistent7[cat]
        print(f"  {cat:10s}: {total:3d} words, {cons:3d} have consistent cycles")


if __name__ == '__main__':
    main()
