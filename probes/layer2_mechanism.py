#!/usr/bin/env python3
"""
Precise mechanism identification for all-normalForm EC at sandwiched ternary.

KEY INSIGHT from the data:
- Phase patterns are: ((1,0),(1,1),(2,1)), ((0,1),(1,1),(1,2)),
  ((0,1),(1,0),(1,3)), ((0,1),(1,0),(3,1))
- J+K per phase: either 1, 2, or 3+1=4.
- Total J = fc(bL)/some, total K = fc(bR)/some.

The deeper mechanism is CONTEXT COLLISION across phases.

At a sandwiched ternary t with m(t)=3:
- 3 phases, 3 S-levels (0,1,2).
- At S-level v: the mover (L,R) pair is the context when t fires from value v.
- The nonmover (L,R) pairs at S-level v are all other steps where c[t]=v.
- EC = mover pair appears in nonmover set.

With binary neighbors: L in {0,1}, R in {0,1}. So only 4 possible (L,R) pairs.
3 phases each claim one mover (L,R) pair. Nonmover pairs are ALL remaining
contexts at that S-level.

This is a pigeonhole-type argument: with only 4 possible (L,R) pairs and
3 phases needing disjoint mover/nonmover sets, the constraints propagate.

Let me trace the exact mover/nonmover sets for the normalForm cycles.
"""

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


def is_normal_form(J, K):
    if J % 2 == 0 and K % 2 == 0:
        return False
    if J >= 2 and K == 0:
        return False
    if J == 0 and K >= 2:
        return False
    return True


n, ms = 7, [2, 3, 2, 3, 2, 3, 3]
max_len = 24
sandwiched = [p for p in range(n) if ms[p] >= 3
              and ms[(p-1) % n] == 2 and ms[(p+1) % n] == 2]

words = enumerate_mover_words(ms, n, max_len)

# For each all-normalForm cycle at sandwiched t, show S-level EC structure
count = 0
s_level_patterns = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    for t in sandwiched:
        ell = len(word)
        bL = (t - 1) % n
        bR = (t + 1) % n

        t_fires = [i for i in range(ell) if word[i] == t]
        if not t_fires:
            continue

        phases = []
        for idx in range(len(t_fires)):
            s = t_fires[idx]
            a = t_fires[(idx - 1) % len(t_fires)]
            if s > a:
                interior = list(range(a + 1, s))
            else:
                interior = list(range(a + 1, ell)) + list(range(0, s))
            J = sum(1 for st in interior if word[st] == bL)
            K = sum(1 for st in interior if word[st] == bR)
            phases.append((J, K))

        all_nf = all(is_normal_form(J, K) for J, K in phases)
        if not all_nf:
            continue

        count += 1

        # Extract S-level data
        for sv in range(ms[t]):
            mover_pairs = set()
            nonmover_pairs = set()
            for i in range(ell):
                if cycle[i][t] == sv:
                    lr = (cycle[i][bL], cycle[i][bR])
                    if word[i] == t:
                        mover_pairs.add(lr)
                    else:
                        nonmover_pairs.add(lr)

            overlap = mover_pairs & nonmover_pairs
            # Count nonmover size and mover count
            mover_list = [i for i in range(ell) if cycle[i][t] == sv and word[i] == t]
            nonmover_list = [i for i in range(ell) if cycle[i][t] == sv and word[i] != t]

            s_level_patterns[(len(mover_list), len(nonmover_list), len(mover_pairs), len(nonmover_pairs), len(overlap) > 0)] += 1

        if count <= 5:
            print(f"\n--- Cycle at t={t}, phases={phases} ---")
            for sv in range(ms[t]):
                mover_list = [(i, (cycle[i][bL], cycle[i][bR])) for i in range(ell)
                              if cycle[i][t] == sv and word[i] == t]
                nonmover_list = [(i, (cycle[i][bL], cycle[i][bR])) for i in range(ell)
                                 if cycle[i][t] == sv and word[i] != t]
                mover_pairs = set(lr for _, lr in mover_list)
                nonmover_pairs = set(lr for _, lr in nonmover_list)
                overlap = mover_pairs & nonmover_pairs
                print(f"  S={sv}: mover={mover_list}, nonmover_pairs={nonmover_pairs}, overlap={overlap}")

print(f"\nTotal all-normalForm instances: {count}")
print(f"\nS-level pattern distribution (mover_count, nonmover_count, mover_distinct, nonmover_distinct, has_EC):")
for (mc, nmc, md, nd, ec), cnt in sorted(s_level_patterns.items(), key=lambda x: -x[1]):
    print(f"  ({mc}, {nmc}, {md}, {nd}, EC={ec}): {cnt}")
