#!/usr/bin/env python3
"""
Trace WHERE EC occurs when all phases at sandwiched t are normalForm.

Key finding: EC at t only 50% of the time. The other 50% must have EC elsewhere.
WHERE?
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


def find_ec_procs(word, cycle, ms, n):
    """Find ALL procs where EC exists."""
    ell = len(word)
    ec_procs = []
    for p in range(n):
        pL = (p - 1) % n
        pR = (p + 1) % n
        for sv in range(ms[p]):
            mover = set()
            nonmover = set()
            for i in range(ell):
                if cycle[i][p] == sv:
                    triple = (cycle[i][pL], cycle[i][p], cycle[i][pR])
                    if word[i] == p:
                        mover.add(triple)
                    else:
                        nonmover.add(triple)
            if mover & nonmover:
                ec_procs.append(p)
                break
    return ec_procs


n, ms = 7, [2, 3, 2, 3, 2, 3, 3]
max_len = 24
sandwiched = [p for p in range(n) if ms[p] >= 3
              and ms[(p-1) % n] == 2 and ms[(p+1) % n] == 2]

words = enumerate_mover_words(ms, n, max_len)

ec_location_when_not_at_t = Counter()
ec_location_relation = Counter()  # relation of EC proc to sandwiched t

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)

    for t in sandwiched:
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

        # Find EC procs
        ec_procs = find_ec_procs(word, cycle, ms, n)

        # Check if t has EC
        t_has_ec = t in ec_procs

        if not t_has_ec:
            # Where IS the EC?
            for p in ec_procs:
                dist = min(abs(p - t), n - abs(p - t))
                ec_location_when_not_at_t[p] += 1
                ec_location_relation[dist] += 1

                # What kind of proc is p?
                is_binary = ms[p] == 2
                is_sandwiched = ms[p] >= 3 and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2

print(f"n={n}, ms={ms}, sandwiched={sandwiched}")
print(f"\nWhen EC not at t, EC is at proc:")
for p, cnt in sorted(ec_location_when_not_at_t.items(), key=lambda x: -x[1]):
    kind = "binary" if ms[p] == 2 else ("sandwiched" if p in sandwiched else "boundary-ternary")
    print(f"  p={p} ({kind}, m={ms[p]}): {cnt}")

print(f"\nDistance from t to EC proc:")
for d, cnt in sorted(ec_location_relation.items()):
    print(f"  dist={d}: {cnt}")

# Now check: is EC always at bL, bR, LL, or RR?
print(f"\n--- Detailed EC proc identification ---")
neighbor_ec = Counter()
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)

    for t in sandwiched:
        bL = (t - 1) % n
        bR = (t + 1) % n
        LL = (t - 2) % n
        RR = (t + 2) % n

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

        ec_procs = find_ec_procs(word, cycle, ms, n)
        t_has_ec = t in ec_procs

        if not t_has_ec:
            names = []
            for p in ec_procs:
                if p == bL: names.append("bL")
                elif p == bR: names.append("bR")
                elif p == LL: names.append("LL")
                elif p == RR: names.append("RR")
                else:
                    dist = min(abs(p - t), n - abs(p - t))
                    names.append(f"dist{dist}")
            neighbor_ec[tuple(sorted(set(names)))] += 1

print(f"\nEC location pattern when NOT at t:")
for pattern, cnt in sorted(neighbor_ec.items(), key=lambda x: -x[1]):
    print(f"  {pattern}: {cnt}")
