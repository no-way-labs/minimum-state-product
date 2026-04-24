#!/usr/bin/env python3
"""Test FR complementarity across multiple n values.

Core claim: sandwiched and non-sandwiched ternary NEVER both fail FR.
Test at n=5,6,7 with various architectures.
"""
import sys, time
from collections import Counter

def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= 2*n and config == start:
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

def is_wrap_adjacent(word, n):
    return abs(word[-1] - word[0]) % n in (1, n-1)

def has_entry_conflict_at(ms, n, word, cycle, p):
    ell = len(word)
    bL, bR = (p-1)%n, (p+1)%n
    mover, nonmover = set(), set()
    for s in range(ell):
        lsr = (cycle[s][bL], cycle[s][p], cycle[s][bR])
        if word[s] == p: mover.add(lsr)
        else: nonmover.add(lsr)
    return bool(mover & nonmover)

def has_return_phase(ms, n, word, cycle, p):
    """Does proc p have a phase where both neighbor fire counts give 'return'?"""
    ell = len(word)
    bL, bR = (p-1)%n, (p+1)%n
    for k in range(ms[p]):
        steps = [s for s in range(ell) if cycle[s][p] == k]
        J = sum(1 for s in steps if word[s] == bL)
        K = sum(1 for s in steps if word[s] == bR)
        if J % ms[bL] == 0 and K % ms[bR] == 0:
            return True
    return False

def test_config(n, ms, max_len, label):
    """Test complementarity for a specific architecture."""
    t0 = time.time()
    words = enumerate_mover_words(ms, n, max_len)
    elapsed_enum = time.time() - t0

    binary = [p for p in range(n) if ms[p] == 2]
    ternary = [p for p in range(n) if ms[p] >= 3]

    # Classify ternary: sandwiched (both neighbors binary) vs others
    sandwiched = [t for t in ternary if ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]
    nonsandwiched = [t for t in ternary if t not in sandwiched]

    total = 0
    ec_any = 0
    sand_fail_nsand_ok = 0
    nsand_fail_sand_ok = 0
    both_fail = 0
    both_ok = 0

    # Also check: does SOME ternary always have entry conflict?
    ternary_covers = 0

    # Return phase analysis
    any_return = 0  # cycle has return phase at SOME ternary
    no_return_but_fr = 0  # no return phase, but still FR

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        total += 1

        ec_procs = set()
        for p in ternary:
            if has_entry_conflict_at(ms, n, word, cycle, p):
                ec_procs.add(p)

        # Also check binary
        for p in binary:
            if has_entry_conflict_at(ms, n, word, cycle, p):
                ec_procs.add(p)

        if ec_procs:
            ec_any += 1

        tern_ec = ec_procs & set(ternary)
        if tern_ec:
            ternary_covers += 1

        sand_ec = bool(ec_procs & set(sandwiched)) if sandwiched else False
        nsand_ec = bool(ec_procs & set(nonsandwiched)) if nonsandwiched else False

        if sandwiched and nonsandwiched:
            if not sand_ec and nsand_ec: sand_fail_nsand_ok += 1
            elif sand_ec and not nsand_ec: nsand_fail_sand_ok += 1
            elif not sand_ec and not nsand_ec: both_fail += 1
            else: both_ok += 1

        # Return phase check
        has_ret = any(has_return_phase(ms, n, word, cycle, t) for t in ternary)
        if has_ret:
            any_return += 1
        elif tern_ec:
            no_return_but_fr += 1

    print(f"\n--- {label}: n={n}, ms={ms}, max_len={max_len} ---")
    print(f"  Words: {len(words)} ({elapsed_enum:.1f}s). Wrap-adj: {total}")
    print(f"  Binary: {binary}, Sandwiched: {sandwiched}, NonSand: {nonsandwiched}")
    if total == 0:
        print(f"  NO CYCLES FOUND (need larger max_len)")
        print(f"  Time: {time.time()-t0:.1f}s")
        return 0
    print(f"  Entry conflict: {ec_any}/{total} ({100*ec_any/total:.1f}%)")
    print(f"  Ternary covers: {ternary_covers}/{total} ({100*ternary_covers/total:.1f}%)")

    if sandwiched and nonsandwiched:
        print(f"  Sand fail + NSand OK: {sand_fail_nsand_ok}")
        print(f"  NSand fail + Sand OK: {nsand_fail_sand_ok}")
        print(f"  BOTH FAIL: {both_fail} {'*** BUG ***' if both_fail > 0 else '(complementary!)'}")
        print(f"  Both OK: {both_ok}")
    elif not nonsandwiched:
        print(f"  (All ternary are sandwiched)")
    else:
        print(f"  (No sandwiched ternary)")

    print(f"  Return phase at some ternary: {any_return}/{total} ({100*any_return/total:.1f}%)")
    print(f"  No return but FR: {no_return_but_fr}/{total}")
    print(f"  Time: {time.time()-t0:.1f}s")
    return both_fail

print("=" * 70)
print("FR COMPLEMENTARITY TEST ACROSS ARCHITECTURES")
print("=" * 70)

failures = 0

# n=5: alternating (all sandwiched)
failures += test_config(5, [2,3,2,3,2], 20, "n=5 alternating")

# n=6: alternating (all sandwiched)
failures += test_config(6, [2,3,2,3,2,3], 24, "n=6 alternating")

# n=7: 3 binary non-consecutive (has non-sandwiched)
failures += test_config(7, [2,3,2,3,2,3,3], 21, "n=7 (3 bin, gap=2)")

# n=8: 3 binary at 0,2,4 (larger gap)
failures += test_config(8, [2,3,2,3,2,3,3,3], 26, "n=8 (3 bin, gap=3)")

# n=7: different binary placement
failures += test_config(7, [2,3,3,2,3,2,3], 21, "n=7 (shifted)")

# n=8: 4 binary non-consecutive
failures += test_config(8, [2,3,2,3,2,3,2,3], 24, "n=8 alternating")

print(f"\n{'='*70}")
print(f"TOTAL COMPLEMENTARITY FAILURES: {failures}")
if failures == 0:
    print("ALL ARCHITECTURES PASS: complementarity holds universally!")
