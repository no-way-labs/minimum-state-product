#!/usr/bin/env python3
"""Does every cycle have at least one ternary with a (≥3,0)/(0,≥3) phase?

If yes: that ternary has EC (phase-level universal), so the cycle has EC.
This would close the proof.

Also: for cycles where a ternary FAILS EC, does it have a (≥3,0)/(0,≥3) phase?
If yes, the phase gives EC but we need PROCESSOR-level EC.
Wait, (≥3,0) at phase level IS processor-level EC (the conflict is within that phase).
"""
import time
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

for n, ms, label, max_len in [
    (4, [2,3,2,3], "n=4", 14),
    (5, [2,3,2,3,2], "n=5", 16),
    (6, [2,3,2,3,2,3], "n=6", 24),
]:
    t0 = time.time()
    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]
    total = 0
    has_toggle3 = 0  # cycle has ≥1 ternary with (≥3,0)/(0,≥3) phase
    no_toggle3 = 0
    no_toggle3_but_ec = 0  # no (≥3,0) but still has EC
    no_toggle3_no_ec = 0
    no_toggle3_details = []

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        total += 1
        ell = len(word)

        cycle_has_t3 = False
        cycle_has_ec = False
        for t in sandwiched:
            bL, bR = (t-1)%n, (t+1)%n
            proc_ec = has_entry_conflict_at(ms, n, word, cycle, t)
            if proc_ec:
                cycle_has_ec = True
            for k in range(3):
                steps = [s for s in range(ell) if cycle[s][t] == k]
                J = sum(1 for s in steps if word[s] == bL)
                K = sum(1 for s in steps if word[s] == bR)
                if (J >= 3 and K == 0) or (J == 0 and K >= 3):
                    cycle_has_t3 = True

        if cycle_has_t3:
            has_toggle3 += 1
        else:
            no_toggle3 += 1
            if cycle_has_ec:
                no_toggle3_but_ec += 1
            else:
                no_toggle3_no_ec += 1
            if len(no_toggle3_details) < 5:
                fc = Counter(word)
                jk_all = {}
                for t in sandwiched:
                    bL, bR = (t-1)%n, (t+1)%n
                    jks = []
                    for k in range(3):
                        steps = [s for s in range(ell) if cycle[s][t] == k]
                        J = sum(1 for s in steps if word[s] == bL)
                        K = sum(1 for s in steps if word[s] == bR)
                        jks.append((J, K))
                    jk_all[t] = jks
                no_toggle3_details.append((word, fc, jk_all))

    elapsed = time.time() - t0
    print(f"\n{label} ({elapsed:.1f}s): {total} cycles")
    print(f"  Has (≥3,0)/(0,≥3) at some ternary: {has_toggle3} ({100*has_toggle3/total:.1f}%)")
    print(f"  No (≥3,0)/(0,≥3) at any ternary: {no_toggle3}")
    if no_toggle3 > 0:
        print(f"    ...but still has EC: {no_toggle3_but_ec}")
        print(f"    ...and NO EC at all: {no_toggle3_no_ec}")
        for word, fc, jk_all in no_toggle3_details[:3]:
            fc_list = [fc.get(p,0) for p in range(n)]
            print(f"    fc={fc_list}")
            for t in sandwiched:
                ec = has_entry_conflict_at(ms, n, word, cycle, t)
                print(f"      P{t}: {jk_all[t]} ec={ec}")
