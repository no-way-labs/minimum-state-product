#!/usr/bin/env python3
"""Does every cycle (n≥6) have some ternary T with fc[T]=3 and a both-even phase?

THEOREM (Both-Even Return):
  With M_k=1, if J_k even and K_k even: mover = first nonmover → EC.

PROOF:
  First step of phase k: nonmover entry (L₀, k, R₀).
  L toggles J_k times, R toggles K_k times.
  Mover (last step): (L₀ ⊕ J_k, R₀ ⊕ K_k).
  With J_k even, K_k even: mover = (L₀, R₀). ∎

So escape requires ALL phases anti-diagonal (J,K have different parities).
Does the ring structure prevent this for ALL ternary simultaneously?
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
    (5, [2,3,2,3,2], "n=5 alt", 16),
    (6, [2,3,2,3,2,3], "n=6 alt", 24),
    (8, [2,3,2,3,2,3,2,3], "n=8 alt", 24),
]:
    t0 = time.time()
    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]

    total = 0
    has_be_ternary = 0  # cycle has some ternary with fc=3 and both-even phase
    no_be_any = 0
    no_be_details = []

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        total += 1
        ell = len(word)
        fc = Counter(word)

        found_be = False
        for t in sandwiched:
            if fc[t] != 3:
                continue  # only check fc=3 (M=1)
            bL, bR = (t-1)%n, (t+1)%n
            for k in range(3):
                steps = [s for s in range(ell) if cycle[s][t] == k]
                J = sum(1 for s in steps if word[s] == bL)
                K = sum(1 for s in steps if word[s] == bR)
                if J % 2 == 0 and K % 2 == 0:
                    found_be = True
                    break
            if found_be:
                break

        if found_be:
            has_be_ternary += 1
        else:
            no_be_any += 1
            if len(no_be_details) < 5:
                fc_list = [fc.get(p,0) for p in range(n)]
                jk_all = {}
                for t in sandwiched:
                    if fc[t] != 3:
                        jk_all[t] = "fc=" + str(fc[t])
                        continue
                    bL, bR = (t-1)%n, (t+1)%n
                    jks = []
                    for kk in range(3):
                        steps = [s for s in range(ell) if cycle[s][t] == kk]
                        J = sum(1 for s in steps if word[s] == bL)
                        K = sum(1 for s in steps if word[s] == bR)
                        jks.append((J, K))
                    jk_all[t] = jks
                no_be_details.append((fc_list, jk_all))

    elapsed = time.time() - t0
    print(f"\n{label} ({elapsed:.1f}s): {total} cycles")
    print(f"  Has ternary w/ fc=3 & both-even phase: {has_be_ternary} ({100*has_be_ternary/total:.1f}%)")
    print(f"  ALL fc=3 ternary all anti-diagonal: {no_be_any}")

    if no_be_any > 0:
        print(f"  Examples:")
        for fc_list, jk_all in no_be_details:
            print(f"    fc={fc_list}")
            for t in sandwiched:
                print(f"      P{t}: {jk_all[t]}")
    else:
        print(f"  *** EVERY cycle has both-even at some fc=3 ternary! ***")

# PART 2: Check if the Both-Even Return theorem is truly universal for M=1
print(f"\n{'='*70}")
print("VERIFICATION: Both-Even Return (M=1) → EC")
print("=" * 70)

n, ms = 6, [2,3,2,3,2,3]
words = enumerate_mover_words(ms, n, 24)
sandwiched = [1, 3, 5]

be_m1_ec = Counter()
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    fc = Counter(word)
    for t in sandwiched:
        if fc[t] != 3:
            continue
        bL, bR = (t-1)%n, (t+1)%n
        for k in range(3):
            steps = [s for s in range(ell) if cycle[s][t] == k]
            J = sum(1 for s in steps if word[s] == bL)
            K = sum(1 for s in steps if word[s] == bR)
            if J % 2 == 0 and K % 2 == 0:
                # Check phase EC
                m_lr, nm_lr = set(), set()
                for s in steps:
                    lr = (cycle[s][bL], cycle[s][bR])
                    if word[s] == t:
                        m_lr.add(lr)
                    else:
                        nm_lr.add(lr)
                has_ec = bool(m_lr & nm_lr)
                be_m1_ec[has_ec] += 1

print(f"Both-Even with M=1: ec=True: {be_m1_ec[True]}, ec=False: {be_m1_ec[False]}")
if be_m1_ec[False] == 0:
    print("*** UNIVERSAL! Both-Even Return + M=1 always gives EC. ***")
