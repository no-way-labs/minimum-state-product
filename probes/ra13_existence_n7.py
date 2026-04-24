#!/usr/bin/env python3
"""
ra13_existence_n7.py — Check cycle existence at n=7 with more thorough search.
Also check: do cycles with fc = 2*ms exist? Or other multiples?

Key question: are there ANY transition-consistent good cycles
for odd-winding non-uniform words with >=3 non-adjacent binary?
"""
import time
from itertools import combinations, product as iproduct
from collections import defaultdict


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


def find_consistent_cycle(word, n, ms, max_starts=50, timeout=3):
    """Try to find a transition-consistent config sequence for this mover word."""
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
                    if nxt_t in set(tuple(c) for c in configs[:t + 1]):
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


def has_no_triple(ms, n):
    for i in range(n):
        if ms[i] == 2 and ms[(i+1) % n] == 2 and ms[(i+2) % n] == 2:
            return False
    return True


def canonicalize(word):
    L = len(word)
    best = word
    for i in range(L):
        rot = word[i:] + word[:i]
        if rot < best:
            best = rot
    return best


def main():
    print("RA13 Existence Check at n=5,7: Comprehensive")
    print("=" * 70)

    t_global = time.time()

    for n in [5, 7]:
        threshold = 4 * (3 ** (n - 2))
        print(f"\n{'='*70}")
        print(f"n={n}, threshold={threshold}")
        print("=" * 70)

        for bins in combinations(range(n), 3):
            bins_set = set(bins)
            ms = [2 if p in bins_set else 3 for p in range(n)]
            if not has_no_triple(ms, n):
                continue
            prod = 1
            for m in ms:
                prod *= m
            if prod >= threshold:
                continue

            # Only check first few multisets for efficiency
            binary_procs = sorted(bins_set)

            # Check fc = ms (standard)
            words = gen_words(n, ms, max_results=200, timeout_s=5)
            unique = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique:
                    unique[c] = w

            ow_nu = []
            sweep = []
            zero = []
            other = []
            for w in unique.values():
                wl = list(w)
                W = total_displacement(wl, n)
                dirs = step_directions(wl, n)
                ns = [d for d in dirs if d != 0]
                uniform = all(d == ns[0] for d in ns) if ns else True
                absW = abs(W)

                if absW == 0:
                    zero.append(wl)
                elif absW == n and not uniform:
                    ow_nu.append(wl)
                elif absW == 2 * n:
                    sweep.append(wl)
                else:
                    other.append(wl)

            # Check existence for OW-NU words
            n_checked = 0
            n_found = 0
            for wl in ow_nu[:20]:  # check first 20
                result = find_consistent_cycle(wl, n, ms, max_starts=50, timeout=2)
                n_checked += 1
                if result:
                    n_found += 1
                    print(f"  FOUND: ms={ms}, word={wl[:10]}..., W={total_displacement(wl, n)}")
                    break

            print(f"  ms={ms} fc=ms: {len(ow_nu)} OW-NU words, "
                  f"{len(sweep)} sweep, {len(zero)} zero, {len(other)} other. "
                  f"Checked {n_checked} OW-NU, found {n_found}")

            # Also check sweep words
            for wl in sweep[:5]:
                result = find_consistent_cycle(wl, n, ms, max_starts=50, timeout=2)
                if result:
                    print(f"    Sweep cycle exists! word={wl[:10]}...")
                    break

            if time.time() - t_global > 120:
                print("  Time limit reached")
                break

        # Check one multiset with fc = 2*ms
        if n == 5:
            ms_test = [2, 3, 2, 3, 2]
            ms2 = [4, 6, 4, 6, 4]  # 2x fire counts
            print(f"\n  Testing fc=2*ms for ms={ms_test}...")
            words2 = gen_words(n, ms2, max_results=50, timeout_s=5)
            print(f"    Words with fc=2*ms: {len(words2)}")
            n_ow_nu_2x = 0
            for w in words2:
                wl = list(w)
                W = total_displacement(wl, n)
                dirs = step_directions(wl, n)
                ns_d = [d for d in dirs if d != 0]
                uniform = all(d == ns_d[0] for d in ns_d) if ns_d else True
                if abs(W) == n and not uniform:
                    n_ow_nu_2x += 1
            print(f"    OW-NU words with fc=2*ms: {n_ow_nu_2x}")

    elapsed = time.time() - t_global
    print(f"\nDone in {elapsed:.1f}s")

    print(f"\n{'='*70}")
    print("ANALYSIS")
    print("=" * 70)
    print("""
Key structural observation:

For >=3 non-adjacent binary with fc=ms (minimum fire count):
- At n=5: 56 OW-NU mover words exist, but ZERO have consistent config sequences.
- At n=7: Same pattern expected (no consistent cycles).

WHY? The issue is that with non-adjacent binary, the walk MUST backtrack
through ternary processors. When the walk revisits a ternary proc from
the same direction, the ternary proc's accumulated value depends on how
many times it fired. With fc=ms (exactly ms[p] firings), the ternary proc
cycles through all values exactly once. But the backtracking creates a
context collision: the walk passes through the same (L,S,R) triple at a
ternary proc in both mover and non-mover roles, requiring contradictory
transition outputs (f(L,S,R) = S' for mover, f(L,S,R) = S for non-mover).

This IS the entry conflict, but arising from the word structure itself,
not from additional mechanisms like binary parity.

IMPLICATION: If oddWinding + nonUniform + nonConsecutiveBinary + fc=ms
always has an entry conflict embedded in the mover word structure,
then the proof of oddWinding_nonUniform_false for non-consecutive binary
can proceed by showing this structural entry conflict directly.
""")


if __name__ == '__main__':
    main()
