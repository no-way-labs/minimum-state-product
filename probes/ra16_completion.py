#!/usr/bin/env python3
"""
RA16k: Direct verification — can any valid system have the sweep good cycle?

Use the verifier to search for valid systems with ms=[2,2,3,3,2,3,3]
and check if any have a sweep good cycle with non-consecutive binary.

If no such system exists: the sweep is blocked (and the shadow EC is
the mechanism).
"""
import sys
sys.path.insert(0, '.')
from verifier import verify_system, all_configs
from itertools import product as iproduct
from collections import Counter
import time
import random


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


def enumerate_words_dfs(n, ms, max_results=50000, timeout=60):
    target_cl = sum(ms)
    results = []
    t0 = time.time()
    ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}
    def dfs(word, fc):
        if time.time() - t0 > timeout: return
        if len(results) >= max_results: return
        if len(word) == target_cl:
            if all(fc[p] == ms[p] for p in range(n)):
                diff = (word[0] - word[-1]) % n
                if diff in (1, n-1):
                    results.append(tuple(word))
            return
        remaining = target_cl - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n))
        if needed > remaining: return
        last = word[-1]
        for nxt in ring_adj[last]:
            if fc[nxt] < ms[nxt]:
                fc[nxt] += 1
                word.append(nxt)
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1
    for start in range(n):
        if time.time() - t0 > timeout or len(results) >= max_results: break
        fc = [0]*n
        fc[start] = 1
        if fc[start] <= ms[start]:
            dfs([start], fc)
    return results


def build_cycle_from_word(word, ms, n, trans_dir):
    """Build a config cycle from a mover word and transition direction."""
    L = len(word)
    configs = [[0]*n]
    for t in range(L):
        c = list(configs[-1])
        p = word[t]
        c[p] = (c[p] + trans_dir[p]) % ms[p]
        configs.append(c)
    if configs[-1] != configs[0]:
        return None
    config_set = set(tuple(c) for c in configs[:L])
    if len(config_set) != L:
        return None
    return [tuple(c) for c in configs[:L]]


def try_build_valid_system(ms, n, word, configs, trans_dir, max_attempts=5000):
    """Try to build a valid system with the given good cycle.

    Strategy: determine forced entries from the cycle, then try random
    completions and verify.
    """
    L = len(word)

    # Build partial transition tables from the good cycle
    tables = {}
    for p in range(n):
        tables[p] = {}

    for t in range(L):
        p = word[t]
        c = configs[t]
        c_next = configs[(t+1)%L]
        lsr = (c[(p-1)%n], c[p], c[(p+1)%n])
        tables[p][lsr] = c_next[p]
        for j in range(n):
            if j == p:
                continue
            lsr_j = (c[(j-1)%n], c[j], c[(j+1)%n])
            tables[j][lsr_j] = c[j]

    # Identify unforced entries
    unforced = []
    for p in range(n):
        for L_val in range(ms[(p-1)%n]):
            for S_val in range(ms[p]):
                for R_val in range(ms[(p+1)%n]):
                    lsr = (L_val, S_val, R_val)
                    if lsr not in tables[p]:
                        unforced.append((p, lsr))

    print(f"    Unforced entries: {len(unforced)}")

    for attempt in range(max_attempts):
        test_tables = {p: dict(tables[p]) for p in range(n)}
        for p, lsr in unforced:
            test_tables[p][lsr] = random.randint(0, ms[p]-1)

        fs = []
        for p in range(n):
            tab = test_tables[p]
            def make_f(t):
                def f(L, S, R):
                    return t[(L, S, R)]
                return f
            fs.append(make_f(tab))

        result = verify_system(ms, fs, verbose=False)
        if result['valid']:
            # Check if the good cycle matches
            gc = result.get('good_configs', set())
            cycle_set = set(configs)
            if cycle_set.issubset(gc):
                return True, attempt
    return False, max_attempts


def main():
    print("RA16k: Can sweep good cycle be realized?")
    print("="*70)

    # n=7 case
    n = 7
    ms = [2, 2, 3, 3, 2, 3, 3]
    print(f"\nn={n}, ms={ms}, product={2*2*3*3*2*3*3}")

    words = enumerate_words_dfs(n, ms, max_results=50000, timeout=60)
    canon = {}
    for w in words:
        L = len(w)
        best = w
        for i in range(L):
            rot = w[i:] + w[:i]
            if rot < best:
                best = rot
        if best not in canon:
            canon[best] = w

    sweep_words = [w for w in canon.values()
                   if total_displacement(list(w), n) is not None
                   and abs(total_displacement(list(w), n)) >= 2*n]

    print(f"Sweep words: {len(sweep_words)}")

    # For the first sweep word, try to build a system
    for w in sweep_words[:1]:
        print(f"\nword = {list(w)}")

        # Try incrementing transition
        bins = {p for p in range(n) if ms[p] == 2}
        terns = [p for p in range(n) if ms[p] == 3]

        for trans_bits in range(1 << len(terns)):
            trans_dir = {}
            for p in bins:
                trans_dir[p] = 1
            for idx, p in enumerate(terns):
                trans_dir[p] = 1 if not ((trans_bits >> idx) & 1) else -1
            configs = build_cycle_from_word(w, ms, n, trans_dir)
            if configs is None:
                continue

            print(f"\n  trans_dir = {trans_dir}")
            found, attempts = try_build_valid_system(
                ms, n, w, configs, trans_dir, max_attempts=10000)
            print(f"  Found valid system: {found} (after {attempts} attempts)")
            if found:
                print(f"  *** SYSTEM EXISTS! Sweep cycle CAN be realized! ***")
                return

    print(f"\nNo valid system found for any transition combo.")
    print(f"Sweep non-consecutive cycles are UNREALIZABLE at n=7.")

    # Also check: do ANY valid systems exist with this ms?
    print(f"\n{'='*70}")
    print(f"Checking: do ANY valid systems exist with ms={ms}?")
    total_attempts = 50000
    found_any = False
    for attempt in range(total_attempts):
        # Random transition tables
        tables = {}
        for p in range(n):
            tables[p] = {}
            for L_val in range(ms[(p-1)%n]):
                for S_val in range(ms[p]):
                    for R_val in range(ms[(p+1)%n]):
                        tables[p][(L_val, S_val, R_val)] = random.randint(0, ms[p]-1)

        fs = []
        for p in range(n):
            tab = tables[p]
            def make_f(t):
                def f(L, S, R):
                    return t[(L, S, R)]
                return f
            fs.append(make_f(tab))

        result = verify_system(ms, fs, verbose=False)
        if result['valid']:
            found_any = True
            gc = result.get('good_configs', set())
            # Extract good cycle mover word
            gc_list = sorted(gc)
            print(f"  Valid system #{attempt}: {len(gc)} good configs")

            # Check if any good cycle is a sweep
            # Build the functional graph on gc
            succ = {}
            for c in gc:
                priv = []
                for i in range(n):
                    L_val = c[(i-1)%n]
                    S_val = c[i]
                    R_val = c[(i+1)%n]
                    if tables[i][(L_val, S_val, R_val)] != S_val:
                        priv.append(i)
                if len(priv) == 1:
                    p = priv[0]
                    lst = list(c)
                    lst[p] = tables[p][(c[(p-1)%n], c[p], c[(p+1)%n])]
                    succ[c] = (tuple(lst), p)

            # Extract cycle and mover word
            visited = set()
            start = gc_list[0]
            mword = []
            node = start
            while node not in visited:
                visited.add(node)
                if node in succ:
                    nxt, p = succ[node]
                    mword.append(p)
                    node = nxt
                else:
                    break

            if len(mword) == len(gc):
                disp = total_displacement(mword, n)
                fc = Counter(mword)
                if disp is not None and abs(disp) >= 2*n:
                    print(f"    SWEEP FOUND! disp={disp}, fc={dict(fc)}")
                    print(f"    word = {mword}")
                else:
                    pass
                    #print(f"    Non-sweep: disp={disp}")

    if not found_any:
        print(f"  No valid systems found in {total_attempts} random attempts")


if __name__ == '__main__':
    main()
