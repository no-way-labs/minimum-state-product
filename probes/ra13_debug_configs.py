#!/usr/bin/env python3
"""
ra13_debug_configs.py — Debug: understand why single-direction transitions
fail to produce valid config sequences for odd-winding non-uniform words.

Then try ALL starting configs (not just all-zero) and context-dependent transitions.
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


def generate_words_dfs(n, ms, max_results=500, timeout=10):
    target_cl = sum(ms)
    results = []
    t0 = time.time()

    def dfs(word, fc):
        if time.time() - t0 > timeout or len(results) >= max_results:
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
        if time.time() - t0 > timeout or len(results) >= max_results:
            break
        fc = [0] * n
        fc[start] = 1
        if fc[start] <= ms[start]:
            dfs([start], fc)
    return results


def build_configs_from_start(word, n, ms, trans_dir, start_config):
    """Build configs starting from arbitrary config."""
    L = len(word)
    configs = [list(start_config)]
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


def is_trans_consistent(word, n, configs):
    L = len(word)
    trans = {}
    for t in range(L):
        for p in range(n):
            lp, rp = (p - 1) % n, (p + 1) % n
            ctx = (p, configs[t][lp], configs[t][p], configs[t][rp])
            val = configs[(t + 1) % L][p]
            if ctx in trans:
                if trans[ctx] != val:
                    return False
            trans[ctx] = val
    return True


def are_non_adjacent(b1, b2, n):
    return (b1 - b2) % n > 1 and (b2 - b1) % n > 1


def check_binary_flip(word, n, ms, configs, bins_to_flip):
    L = len(word)
    companion = []
    for t in range(L):
        sc = list(configs[t])
        for p in bins_to_flip:
            sc[p] = 1 - sc[p]
        companion.append(tuple(sc))
    orig_set = set(configs)
    comp_set = set(companion)
    if len(comp_set) != L:
        return False, "not_distinct"
    if len(orig_set & comp_set) > 0:
        return False, "not_disjoint"
    for t in range(L):
        mover = word[t]
        for p in range(n):
            if p == mover:
                if companion[(t + 1) % L][p] == companion[t][p]:
                    return False, f"mover_no_fire(p={p},t={t})"
            else:
                if companion[(t + 1) % L][p] != companion[t][p]:
                    return False, f"nonmover_change(p={p},t={t})"
    # Trans consistency between original and companion
    trans = {}
    for t in range(L):
        for p in range(n):
            lp, rp = (p - 1) % n, (p + 1) % n
            ctx = (p, configs[t][lp], configs[t][p], configs[t][rp])
            val = configs[(t + 1) % L][p]
            trans[ctx] = val
    for t in range(L):
        for p in range(n):
            lp, rp = (p - 1) % n, (p + 1) % n
            ctx = (p, companion[t][lp], companion[t][p], companion[t][rp])
            val = companion[(t + 1) % L][p]
            if ctx in trans:
                if trans[ctx] != val:
                    return False, f"trans_conflict(p={p},t={t})"
    return True, "OK"


def has_no_triple(ms, n):
    for i in range(n):
        if ms[i] == 2 and ms[(i+1) % n] == 2 and ms[(i+2) % n] == 2:
            return False
    return True


def main():
    print("RA13 Debug: Config generation for odd-winding non-uniform cycles")
    print("=" * 70)

    # Part 1: Diagnose why single-direction from all-zeros fails
    n = 7
    ms = [2, 3, 2, 3, 2, 3, 3]
    ternary = [p for p in range(n) if ms[p] == 3]
    binary_procs = [p for p in range(n) if ms[p] == 2]
    print(f"\nn={n}, ms={ms}")

    words = generate_words_dfs(n, ms, max_results=200, timeout=5)
    print(f"DFS words: {len(words)}")

    ow_nu_words = []
    for w in words:
        wl = list(w)
        W = total_displacement(wl, n)
        if abs(W) != n:
            continue
        dirs = step_directions(wl, n)
        ns = [d for d in dirs if d != 0]
        if not ns or all(d == ns[0] for d in ns):
            continue
        ow_nu_words.append(wl)

    print(f"Odd-winding non-uniform: {len(ow_nu_words)}")

    if ow_nu_words:
        wl = ow_nu_words[0]
        print(f"\nDebug word: {wl}")
        print(f"  W={total_displacement(wl, n)}, dirs={step_directions(wl, n)}")

        # Why does all-incrementing from all-zeros fail?
        td = {p: 1 for p in range(n)}
        L = len(wl)
        configs = [[0] * n]
        for t in range(L):
            c = list(configs[-1])
            p = wl[t]
            c[p] = (c[p] + td[p]) % ms[p]
            configs.append(c)

        if configs[-1] != configs[0]:
            print(f"  FAIL: does not return (final={configs[-1]})")
        else:
            config_set = set(tuple(c) for c in configs[:L])
            print(f"  Returns to start. Distinct: {len(config_set)}/{L}")
            if len(config_set) < L:
                seen = {}
                for t in range(L):
                    ct = tuple(configs[t])
                    if ct in seen:
                        print(f"  First dup: t={t} == t={seen[ct]}: {ct}")
                        break
                    seen[ct] = t

    # Part 2: Try ALL starting configs with all transition combos
    print(f"\n{'='*70}")
    print("Part 2: All starting configs x all transition combos")
    print("=" * 70)

    n_total_consistent = 0
    n_total_valid = 0
    n_flip_tested = 0
    n_flip_pass = 0
    n_flip_fail = 0
    failure_reasons = defaultdict(int)

    nonadj_pairs = [pair for pair in combinations(binary_procs, 2)
                    if are_non_adjacent(pair[0], pair[1], n)]
    print(f"Non-adjacent binary pairs: {nonadj_pairs}")

    # For each word, try all starting configs and all transition combos
    for w_idx, wl in enumerate(ow_nu_words[:10]):  # limit to 10 words for speed
        for trans_bits in range(1 << len(ternary)):
            td = {}
            for p in range(n):
                if ms[p] == 2:
                    td[p] = 1
                else:
                    idx = ternary.index(p)
                    td[p] = 1 if not ((trans_bits >> idx) & 1) else -1

            # Try all starting configs
            for start in iproduct(*[range(m) for m in ms]):
                configs = build_configs_from_start(wl, n, ms, td, start)
                if configs is None:
                    continue
                n_total_valid += 1

                if not is_trans_consistent(wl, n, configs):
                    continue
                n_total_consistent += 1

                # Test binary flip
                for pair in nonadj_pairs:
                    ok, reason = check_binary_flip(wl, n, ms, configs, list(pair))
                    n_flip_tested += 1
                    if ok:
                        n_flip_pass += 1
                    else:
                        n_flip_fail += 1
                        failure_reasons[reason.split('(')[0]] += 1

        if (w_idx + 1) % 2 == 0:
            print(f"  After {w_idx+1} words: {n_total_valid} valid, "
                  f"{n_total_consistent} consistent, "
                  f"{n_flip_tested} flip tests ({n_flip_pass} pass, {n_flip_fail} fail)")

    print(f"\n{'='*70}")
    print("RESULTS")
    print(f"  Valid config sequences: {n_total_valid}")
    print(f"  Transition-consistent: {n_total_consistent}")
    print(f"  Flip tests: {n_flip_tested}")
    print(f"  Pass: {n_flip_pass}")
    print(f"  Fail: {n_flip_fail}")
    if n_flip_tested > 0:
        print(f"  Rate: {100.0*n_flip_pass/n_flip_tested:.2f}%")

    if failure_reasons:
        print("\nFailure breakdown:")
        for r, c in sorted(failure_reasons.items(), key=lambda x: -x[1]):
            print(f"  {r}: {c}")

    if n_flip_fail == 0 and n_flip_tested > 0:
        print("\n>>> Binary flip works for all transition-consistent odd-winding non-uniform!")
    elif n_total_consistent == 0:
        print("\n>>> NO transition-consistent cycles found with single-direction model.")
        print("Need to explore context-dependent transitions.")

    # Part 3: If no consistent cycles, try building cycles from REAL systems
    if n_total_consistent == 0:
        print(f"\n{'='*70}")
        print("Part 3: Build real systems and find their good cycles")
        print("=" * 70)

        # For each transition function, find ALL good cycles
        # A transition function: for each proc p, for each (L,S,R), output S'.
        # For mover: S' != S (must change). For non-mover: S' = S.
        # So the transition function just decides: for each proc and each context,
        # what is the NEW value when firing.

        # For binary proc: fire always flips (0->1, 1->0). Only 1 option.
        # For ternary proc: fire changes to one of 2 other values.
        #   Given context (L,S,R), S can change to (S+1)%3 or (S+2)%3.

        # Build a small system and enumerate its good cycles
        print("Building systems for n=7, ms=[2,3,2,3,2,3,3]...")

        # For each ternary proc, enumerate transition tables
        # Each ternary proc sees contexts (L, S, R) where L in {0,1,...,m_{left}-1}, etc.
        # For each context, the proc either fires or not (determined by the mover word).
        # When it fires, it goes to one of 2 possible values.

        # This is too large to enumerate exhaustively. Instead, let's just try
        # the two canonical directions (inc/dec) for each ternary proc and see
        # if any produce odd-winding non-uniform cycles.

        # Actually, let me try a different approach: generate ALL valid good cycles
        # by DFS through (config, mover) pairs.

        print("Attempting small-scale good cycle enumeration...")
        # For n=7 this is too large. Let's try n=5 first.

        n5 = 5
        ms5 = [2, 3, 2, 3, 2]
        threshold5 = 4 * 3 ** (n5 - 2)
        prod5 = 1
        for m in ms5:
            prod5 *= m
        print(f"\nn={n5}, ms={ms5}, prod={prod5}, threshold={threshold5}")
        print(f"Sub-threshold: {prod5 < threshold5}")

        # Generate all configs
        all_configs = list(iproduct(*[range(m) for m in ms5]))
        print(f"Total configs: {len(all_configs)}")

        # For each pair of configs that differ in exactly one position,
        # and that position is the mover, build transition edges
        # Then find cycles.

        # This is BFS/DFS on the good-cycle state graph.
        # State: (config, which-proc-just-fired) — but we want cycles of configs.

        # Simpler: try building cycles from random starting configs.
        import random
        random.seed(42)

        found_cycles = []
        attempts = 0

        for _ in range(10000):
            attempts += 1
            config = list(random.choice(all_configs))
            start = tuple(config)
            path = [start]
            movers = []
            seen = {start}
            stuck = False

            for step in range(sum(ms5) + 5):  # max cycle length
                c = list(path[-1])
                # Choose a random mover
                possible_movers = list(range(n5))
                random.shuffle(possible_movers)

                moved = False
                for mover in possible_movers:
                    # Choose a random new value
                    old_val = c[mover]
                    options = [v for v in range(ms5[mover]) if v != old_val]
                    random.shuffle(options)
                    for new_val in options:
                        nc = list(c)
                        nc[mover] = new_val
                        nc_t = tuple(nc)
                        if nc_t == start and len(path) >= n5:
                            # Found a cycle!
                            movers.append(mover)
                            # Check: is it a valid good cycle?
                            # (all distinct configs, proper mover word)
                            if len(path) == len(set(path)):
                                W = total_displacement(movers, n5)
                                if abs(W) == n5:
                                    dirs = step_directions(movers, n5)
                                    ns = [d for d in dirs if d != 0]
                                    if ns and not all(d == ns[0] for d in ns):
                                        # Check transition consistency
                                        configs = list(path)
                                        configs.append(start)  # close
                                        if is_trans_consistent(movers, n5, configs):
                                            found_cycles.append((list(path), list(movers)))
                            movers.pop()
                            moved = True
                            break
                        elif nc_t not in seen and len(path) < sum(ms5) + 5:
                            path.append(nc_t)
                            movers.append(mover)
                            seen.add(nc_t)
                            moved = True
                            break
                    if moved:
                        break
                if not moved:
                    stuck = True
                    break

        print(f"Random attempts: {attempts}")
        print(f"Found odd-winding non-uniform consistent cycles: {len(found_cycles)}")

        if found_cycles:
            for path, movers in found_cycles[:3]:
                print(f"  word={movers}, len={len(movers)}, W={total_displacement(movers, n5)}")
                print(f"  dirs={step_directions(movers, n5)}")
                print(f"  configs[0]={path[0]}")

                # Test binary flip
                binary5 = [p for p in range(n5) if ms5[p] == 2]
                nonadj5 = [pair for pair in combinations(binary5, 2)
                           if are_non_adjacent(pair[0], pair[1], n5)]
                configs_list = list(path)
                for pair in nonadj5:
                    ok, reason = check_binary_flip(movers, n5, ms5, configs_list, list(pair))
                    print(f"  Flip {pair}: {ok} ({reason})")


if __name__ == '__main__':
    main()
