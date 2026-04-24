#!/usr/bin/env python3
"""RA13 Walk Structure: When all adj binary pairs have (1,1), what's the provider?"""

from itertools import permutations
from collections import Counter


def compute_winding(word, n):
    L = len(word)
    cw = ccw = 0
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 1: cw += 1
        elif diff == n - 1: ccw += 1
    return cw, ccw


def _enumerate_walks_dfs(n, length, ms):
    results = []
    def dfs(path, fc):
        pos = path[-1]
        step = len(path)
        if step == length:
            diff = (path[0] - pos) % n
            if diff != 1 and diff != n - 1: return
            if any(f < 2 for f in fc): return
            if all(f <= 2 for f in fc): return
            cw, ccw = compute_winding(path, n)
            if cw == 0 or cw != ccw: return
            results.append(tuple(path))
            return
        remaining = length - step
        unfired = sum(1 for f in fc if f < 2)
        if unfired > remaining: return
        for d in [1, -1]:
            nxt = (pos + d) % n
            if fc[nxt] >= ms[nxt] and ms[nxt] == 2: continue
            if fc[nxt] >= 2 * ms[nxt]: continue
            fc[nxt] += 1
            path.append(nxt)
            dfs(path, fc)
            path.pop()
            fc[nxt] -= 1
    fc = [0] * n
    fc[0] = 1
    dfs([0], fc)
    unique = set()
    result = []
    for w in results:
        best = w
        for i in range(len(w)):
            rot = w[i:] + w[:i]
            if rot < best: best = rot
        if best not in unique:
            unique.add(best)
            result.append(list(best))
    return result


def generate_subthreshold_multisets(n, threshold):
    results = []
    max_state = min(threshold // (2 ** (n - 1)) + 1, 10)
    def gen(pos, min_val, current, prod):
        if pos == n:
            if prod < threshold:
                num_bin = sum(1 for m in current if m == 2)
                if num_bin >= 3:
                    results.append(tuple(current))
            return
        remaining = n - pos
        for m in range(max(2, min_val), max_state + 1):
            new_prod = prod * m
            if new_prod >= threshold: break
            if remaining > 1 and new_prod * (2 ** (remaining - 1)) >= threshold:
                if m > 2: break
            gen(pos + 1, m, current + [m], new_prod)
    gen(0, 2, [], 1)
    return results


def get_all_ring_placements(sorted_ms, n):
    seen = set()
    results = []
    for perm in set(permutations(sorted_ms)):
        best = perm
        for i in range(n):
            rot = perm[i:] + perm[:i]
            if rot < best: best = rot
        rev = perm[::-1]
        for i in range(n):
            rot = rev[i:] + rev[:i]
            if rot < best: best = rot
        if best not in seen:
            seen.add(best)
            results.append(list(best))
    return results


def find_provider_binary_centric(word, n, ms, fc):
    L = len(word)
    for b in range(n):
        if ms[b] != 2 or fc[b] != 2: continue
        b_fires = [i for i, x in enumerate(word) if x == b]
        for t in [(b-1)%n, (b+1)%n]:
            if fc[t] < 2: continue
            t_fires = [i for i, x in enumerate(word) if x == t]
            fc_t = len(t_fires)
            other = (t-1)%n if b == (t+1)%n else (t+1)%n
            o_fires = [i for i, x in enumerate(word) if x == other]
            for idx in range(fc_t):
                start = t_fires[(idx-1)%fc_t]
                end = t_fires[idx]
                gap = (end - start) % L
                b_in = sum(1 for bf in b_fires if 0 < (bf - start) % L < gap)
                o_in = sum(1 for of_ in o_fires if 0 < (of_ - start) % L < gap)
                if b_in == fc[b] and o_in == 0:
                    return t, idx, b, other, ms[t], ms[other]
    return None


def classify_all_adj_binary_pairs(word, n, ms, fc):
    L = len(word)
    pairs = []
    for t in range(n):
        b = (t + 1) % n
        if ms[t] != 2 or ms[b] != 2 or fc[t] != 2 or fc[b] != 2: continue
        t_fires = [i for i, x in enumerate(word) if x == t]
        b_fires = [i for i, x in enumerate(word) if x == b]
        gap = (t_fires[1] - t_fires[0]) % L
        b_between = sum(1 for bf in b_fires if 0 < (bf - t_fires[0]) % L < gap)
        pairs.append((t, b, b_between))
    return pairs


def main():
    print("RA13 Walk Structure: All-(1,1) words analysis")
    print("=" * 70)

    n = 7
    threshold = 4 * (3 ** (n - 2))
    sorted_multisets = generate_subthreshold_multisets(n, threshold)

    all_11_count = 0
    all_11_providers = Counter()
    all_11_examples = []

    for sorted_ms in sorted_multisets:
        placements = get_all_ring_placements(sorted_ms, n)
        for ms in placements:
            max_len = min(sum(ms), 4 * n)
            min_len = 2 * n + 1
            for cycle_len in range(min_len, max_len + 1):
                walks = _enumerate_walks_dfs(n, cycle_len, ms)
                for w in walks:
                    fc = [0] * n
                    for p in w: fc[p] += 1
                    pairs = classify_all_adj_binary_pairs(w, n, ms, fc)
                    if not pairs: continue
                    all_11 = all(p[2] == 1 for p in pairs)
                    if not all_11: continue
                    all_11_count += 1
                    prov = find_provider_binary_centric(w, n, ms, fc)
                    if prov:
                        t, idx, b, other, m_t, m_other = prov
                        all_11_providers[(m_t, ms[b], m_other)] += 1
                        if len(all_11_examples) < 5:
                            all_11_examples.append({
                                'ms': list(ms), 'word': list(w), 'fc': list(fc),
                                'pairs': pairs,
                                'prov': (t, b, other, m_t, ms[b], m_other, fc[t])
                            })
                    else:
                        print(f"  NO PROVIDER: ms={list(ms)}, word={list(w)}")

    print(f"\n  All-(1,1) words at n=7: {all_11_count}")
    print(f"\n  Provider (m_t, m_active, m_silent):")
    for arch, cnt in all_11_providers.most_common():
        print(f"    {arch}: {cnt}")
    print(f"\n  Examples:")
    for ex in all_11_examples:
        print(f"    ms={ex['ms']}, word={ex['word']}, fc={ex['fc']}")
        t, b, other, m_t, m_b, m_other, fc_t = ex['prov']
        print(f"    provider: t={t}(m={m_t},fc={fc_t}), active=b={b}(m={m_b}), silent={other}(m={m_other})")
        print(f"    adj binary pairs: {ex['pairs']}")


if __name__ == "__main__":
    main()
