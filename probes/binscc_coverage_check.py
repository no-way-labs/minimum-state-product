#!/usr/bin/env python3
"""Coverage check: Both-Even Return (M=1) + Toggle-FR (≥3,0)/(0,≥3) + Zero-Side (≥2,0 M=1).

For each cycle: does at least one ternary have EC via a PROVED mechanism?
1. Both-Even Return: phase with J even, K even, M=1 (fc[T]=3)
2. Toggle-FR: phase with (J≥3,K=0) or (J=0,K≥3) — any M
3. Zero-Side: phase with (J≥2,K=0) or (J=0,K≥2) with M=1

Note: #3 includes #2 when M=1. But #2 works for any M.
Combined: if fc[T]=3 and some phase has J%2==K%2 or J≥2&K=0 or J=0&K≥2 → EC.
                fc[T]>3 and some phase has J≥3&K=0 or J=0&K≥3 → EC.
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

for n, ms, label, max_len in [
    (5, [2,3,2,3,2], "n=5", 16),
    (6, [2,3,2,3,2,3], "n=6", 24),
    (8, [2,3,2,3,2,3,2,3], "n=8", 24),
]:
    t0 = time.time()
    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]

    total = 0
    covered = 0
    uncovered = 0
    uncov_details = []

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        total += 1
        ell = len(word)
        fc = Counter(word)

        cycle_covered = False
        for t in sandwiched:
            bL, bR = (t-1)%n, (t+1)%n
            m = fc[t]  # should be multiple of 3
            M_per_phase = m // 3  # movers per phase

            for k in range(3):
                steps = [s for s in range(ell) if cycle[s][t] == k]
                J = sum(1 for s in steps if word[s] == bL)
                K = sum(1 for s in steps if word[s] == bR)

                # Mechanism 1: Both-Even Return (M=1)
                if M_per_phase == 1 and J % 2 == 0 and K % 2 == 0:
                    cycle_covered = True
                    break

                # Mechanism 2: Toggle-FR (any M)
                if (J >= 3 and K == 0) or (J == 0 and K >= 3):
                    cycle_covered = True
                    break

                # Mechanism 3: Zero-Side EC (M=1)
                if M_per_phase == 1:
                    if (J >= 2 and K == 0) or (J == 0 and K >= 2):
                        cycle_covered = True
                        break

            if cycle_covered:
                break

        if cycle_covered:
            covered += 1
        else:
            uncovered += 1
            if len(uncov_details) < 3:
                jk_info = {}
                for t in sandwiched:
                    bL, bR = (t-1)%n, (t+1)%n
                    jks = []
                    for k in range(3):
                        steps = [s for s in range(ell) if cycle[s][t] == k]
                        J = sum(1 for s in steps if word[s] == bL)
                        K = sum(1 for s in steps if word[s] == bR)
                        jks.append((J, K))
                    jk_info[t] = (fc[t], jks)
                uncov_details.append(([fc.get(p,0) for p in range(n)], jk_info))

    elapsed = time.time() - t0
    print(f"\n{label} ({elapsed:.1f}s): {total} cycles")
    print(f"  Covered by proved mechanisms: {covered} ({100*covered/total:.1f}%)")
    print(f"  NOT covered: {uncovered}")
    if uncov_details:
        for fc_list, jk_info in uncov_details:
            print(f"    fc={fc_list}")
            for t in sandwiched:
                fct, jks = jk_info[t]
                print(f"      P{t} (fc={fct}): {jks}")
    elif uncovered == 0:
        print(f"    *** ALL COVERED! ***")
