#!/usr/bin/env python3
"""Debug: verify zero_phase cases. Analytically, when ternary t is between
two binary procs, every phase should have ≥1 binary-neighbor firing.
If zero_phase exists, find WHY."""

import sys
from collections import Counter


def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= 6 and config == start:
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


def main():
    n, ms = 5, [2, 3, 2, 3, 2]
    words = enumerate_mover_words(ms, n, 21)
    print(f"{len(words)} words")

    t = 1  # ternary between binary 0 and 2
    bL = 0
    bR = 2

    found = 0
    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue
        ell = len(cycle)

        # Check phase distribution
        for k in range(ms[t]):
            alpha = sum(1 for s in range(ell)
                        if cycle[s][t] == k and word[s] == bL)
            delta = sum(1 for s in range(ell)
                        if cycle[s][t] == k and word[s] == bR)
            if alpha + delta == 0:
                found += 1
                print(f"\nZERO PHASE FOUND: word={word}")
                print(f"  ℓ={ell}, phase k={k}")
                print(f"  alpha(P{bL})={alpha}, delta(P{bR})={delta}")
                # Show all steps in phase k
                print(f"  Steps with c[{t}]={k}:")
                for s in range(ell):
                    if cycle[s][t] == k:
                        print(f"    step {s}: word={word[s]}, "
                              f"config={cycle[s]}")
                # Show t-firings
                t_steps = [s for s in range(ell) if word[s] == t]
                print(f"  T-firings at steps: {t_steps}")
                print(f"  T-firing configs: "
                      f"{[cycle[s][t] for s in t_steps]}")
                if found >= 3:
                    break
        if found >= 3:
            break

    if found == 0:
        print("\nNO zero_phase found! Previous result was wrong.")

    # Also check: how many t-firings total?
    print(f"\n\nRound analysis:")
    round_dist = Counter()
    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue
        t_count = sum(1 for s in range(len(cycle)) if word[s] == t)
        round_dist[t_count // ms[t]] += 1
    print(f"  T-firing rounds: {dict(sorted(round_dist.items()))}")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
