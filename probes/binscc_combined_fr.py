#!/usr/bin/env python3
"""Combined FR coverage: Both-Even + SR-OSB + value matching.

Both-Even FR: if bLf AND bRf are both even (incl 0) in a phase → FR.
SR-OSB FR: if min(bLf,bRf)=0 AND max≥2 in a phase → FR.

Question: what's the GAP? Phases where neither applies?
A phase is "uncovered" iff:
  - At least one of bLf,bRf is odd (not both-even)
  - AND min(bLf,bRf)≥1 OR max(bLf,bRf)≤1 (not SR-OSB)

Key insight: on bipartite ring, ALL binary fc are even.
So both-even fails ONLY when anti-diagonal parity pattern.
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

print("=" * 70)
print("COMBINED FR COVERAGE ANALYSIS")
print("=" * 70)

# Test at n=6 and n=8 (bipartite)
for n, ms, max_len, desc in [
    (6, [2,3,2,3,2,3], 24, "n=6 alt"),
    (8, [2,3,2,3,2,3,2,3], 28, "n=8 alt"),
]:
    print(f"\n{'='*60}")
    print(f"{desc}: n={n}, ms={ms}")

    tern = [p for p in range(n) if ms[p] >= 3]
    binn = [p for p in range(n) if ms[p] == 2]
    sandwiched = [t for t in tern if ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

    t0 = time.time()
    words = enumerate_mover_words(ms, n, max_len)
    print(f"  Words: {len(words)} ({time.time()-t0:.1f}s)")

    total = 0
    # Per-cycle: which mechanisms give FR?
    fr_by_both_even = 0     # some phase has both-even → FR
    fr_by_sr_osb = 0        # some phase has SR-OSB → FR
    fr_by_value_match = 0   # FR but neither both-even nor SR-OSB at that phase
    no_fr = 0

    # Per-ternary anti-diagonal analysis
    anti_diag_count = Counter()  # how many ternary are anti-diagonal per cycle
    all_anti_diag = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        total += 1
        ell = len(word)
        fc = Counter(word)

        has_be_fr = False  # FR via both-even at some ternary
        has_osb_fr = False  # FR via SR-OSB at some ternary
        has_any_fr = False  # FR at some ternary (any mechanism)
        n_anti_diag = 0

        for t in sandwiched:
            if fc[t] != ms[t]:
                continue  # single-round only
            bL = (t - 1) % n
            bR = (t + 1) % n

            t_has_be = False
            t_has_osb = False
            t_has_fr = False

            # Check parity pattern
            parities = []
            for k in range(ms[t]):
                ps = [s for s in range(ell) if cycle[s][t] == k]
                bLf = sum(1 for s in ps if word[s] == bL)
                bRf = sum(1 for s in ps if word[s] == bR)

                pL = bLf % 2
                pR = bRf % 2
                parities.append((pL, pR))

                # Both-even check
                if pL == 0 and pR == 0:
                    t_has_be = True

                # SR-OSB check
                if min(bLf, bRf) == 0 and max(bLf, bRf) >= 2:
                    t_has_osb = True

                # Actual FR check
                if len(ps) > 1:
                    mlrs = set()
                    nmlrs = set()
                    for s in ps:
                        lr = (cycle[s][bL], cycle[s][bR])
                        if word[s] == t:
                            mlrs.add(lr)
                        else:
                            nmlrs.add(lr)
                    if mlrs & nmlrs:
                        t_has_fr = True

            if t_has_be:
                has_be_fr = True
            if t_has_osb:
                has_osb_fr = True
            if t_has_fr:
                has_any_fr = True

            # Check if anti-diagonal (|A|=2, |B|=2, |A∩B|=1)
            A = [k for k, (pL, pR) in enumerate(parities) if pL == 1]
            B = [k for k, (pL, pR) in enumerate(parities) if pR == 1]
            is_anti = (len(A) == 2 and len(B) == 2 and
                       len(set(A) & set(B)) == 1)
            if is_anti:
                n_anti_diag += 1

        anti_diag_count[n_anti_diag] += 1
        if n_anti_diag == len(sandwiched):
            all_anti_diag += 1

        if has_be_fr:
            fr_by_both_even += 1
        elif has_osb_fr:
            fr_by_sr_osb += 1
        elif has_any_fr:
            fr_by_value_match += 1
        else:
            no_fr += 1

    print(f"  Wrap-adjacent: {total}")
    print(f"\n  FR coverage:")
    print(f"    Both-Even (first): {fr_by_both_even}/{total} "
          f"({100*fr_by_both_even/total:.1f}%)")
    print(f"    SR-OSB (remaining): {fr_by_sr_osb}/{total} "
          f"({100*fr_by_sr_osb/total:.1f}%)")
    print(f"    Value-match (remaining): {fr_by_value_match}/{total} "
          f"({100*fr_by_value_match/total:.1f}%)")
    print(f"    No FR: {no_fr}/{total}")
    print(f"    TOTAL FR: {fr_by_both_even+fr_by_sr_osb+fr_by_value_match}/{total}")

    print(f"\n  Anti-diagonal analysis:")
    print(f"    Distribution of #anti-diagonal ternary per cycle:")
    for k, cnt in sorted(anti_diag_count.items()):
        print(f"      {k}/{len(sandwiched)} anti-diagonal: {cnt}")
    print(f"    ALL sandwiched ternary anti-diagonal: {all_anti_diag}")

    if all_anti_diag > 0:
        print(f"\n  >>> {all_anti_diag} cycles have ALL ternary anti-diagonal!")
        print(f"      These need SR-OSB or value-match for FR.")
    else:
        print(f"\n  >>> Both-Even covers ALL cycles (no all-anti-diagonal).")
        print(f"      Both-Even alone proves FR universality!")

    elapsed = time.time() - t0
    print(f"  Time: {elapsed:.1f}s")

sys.stdout.flush()
