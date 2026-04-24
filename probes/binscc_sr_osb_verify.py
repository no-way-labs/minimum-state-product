#!/usr/bin/env python3
"""Verify the Single-Round One-Sided Bounce FR Theorem at multiple n.

KEY RESULTS TO VERIFY:
1. SR-OSB FR Theorem: In a single-round ternary phase where one binary
   neighbor fires >=2 and the other fires 0, FR always holds.
2. SR-OSB Universality: Every wrap-adjacent cycle has at least one such phase.

If both hold, entry conflict is universal for >=3 non-consecutive binary.
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

def analyze_cycle(ms, n, word, cycle):
    """Analyze SR-OSB and FR properties of a cycle."""
    ell = len(word)
    fc = Counter(word)
    binn = [p for p in range(n) if ms[p] == 2]
    tern = [p for p in range(n) if ms[p] >= 3]

    sr_osb_fr = False      # has SR-OSB phase with FR
    sr_osb_nofr = False     # has SR-OSB phase WITHOUT FR
    has_sr_osb = False
    any_fr = False

    for t in tern:
        bL = (t - 1) % n
        bR = (t + 1) % n
        if ms[bL] != 2 or ms[bR] != 2:
            continue  # not flanked by binary

        is_single_round = (fc[t] == ms[t])

        for k in range(ms[t]):
            ps = [s for s in range(ell) if cycle[s][t] == k]
            if len(ps) <= 1:
                continue
            mover_steps = [s for s in ps if word[s] == t]
            nm_steps = [s for s in ps if word[s] != t]
            if not mover_steps or not nm_steps:
                continue

            bLf = sum(1 for s in ps if word[s] == bL)
            bRf = sum(1 for s in ps if word[s] == bR)

            # Check FR at this phase
            mlrs = set()
            nmlrs = set()
            for s in ps:
                lr = (cycle[s][bL], cycle[s][bR])
                if word[s] == t:
                    mlrs.add(lr)
                else:
                    nmlrs.add(lr)
            has_fr_here = bool(mlrs & nmlrs)
            if has_fr_here:
                any_fr = True

            # One-sided bounce: one >= 2, other = 0 (or both = 0)
            is_osb = (min(bLf, bRf) == 0 and max(bLf, bRf) != 1)
            if is_osb and is_single_round:
                has_sr_osb = True
                if has_fr_here:
                    sr_osb_fr = True
                else:
                    sr_osb_nofr = True

    return has_sr_osb, sr_osb_fr, sr_osb_nofr, any_fr

# Test configurations
configs = [
    # (n, ms, max_length, description)
    (6, [2, 3, 2, 3, 2, 3], 24, "n=6 alt (3B+3T)"),
    (7, [2, 3, 2, 3, 2, 3, 3], 28, "n=7 (3B+4T)"),
    (8, [2, 3, 2, 3, 2, 3, 2, 3], 28, "n=8 alt (4B+4T)"),
]

print("=" * 70)
print("SR-OSB FR THEOREM VERIFICATION")
print("=" * 70)

for n, ms, max_len, desc in configs:
    print(f"\n{'='*60}")
    print(f"{desc}: n={n}, ms={ms}")
    t0 = time.time()

    words = enumerate_mover_words(ms, n, max_len)
    enum_time = time.time() - t0
    print(f"  Words: {len(words)} ({enum_time:.1f}s)")

    total = 0
    has_osb = 0
    osb_fr = 0
    osb_nofr_count = 0
    any_fr_count = 0
    no_fr_count = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        total += 1

        ho, of, onf, af = analyze_cycle(ms, n, word, cycle)
        if ho:
            has_osb += 1
        if of:
            osb_fr += 1
        if onf:
            osb_nofr_count += 1
        if af:
            any_fr_count += 1
        else:
            no_fr_count += 1

    if total == 0:
        print("  No wrap-adjacent cycles found")
        continue

    elapsed = time.time() - t0
    print(f"  Wrap-adjacent cycles: {total}")
    print(f"  SR-OSB coverage:  {has_osb}/{total} ({100*has_osb/total:.1f}%)")
    print(f"  SR-OSB => FR:     {osb_fr}/{total} (SR-OSB phases with FR)")
    print(f"  SR-OSB FR-fails:  {osb_nofr_count} (should be 0)")
    print(f"  Any FR:           {any_fr_count}/{total} ({100*any_fr_count/total:.1f}%)")
    print(f"  All-fail:         {no_fr_count} (should be 0)")
    print(f"  Time: {elapsed:.1f}s")

    # Summary for this n
    if osb_nofr_count == 0:
        print(f"  >>> SR-OSB FR THEOREM HOLDS at n={n}")
    else:
        print(f"  >>> SR-OSB FR THEOREM FAILS at n={n}!")

    if has_osb == total:
        print(f"  >>> SR-OSB UNIVERSALITY HOLDS at n={n}")
    else:
        print(f"  >>> SR-OSB UNIVERSALITY FAILS at n={n}!")

    sys.stdout.flush()

print(f"\n{'='*70}")
print("DONE")
sys.stdout.flush()
