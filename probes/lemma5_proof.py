#!/usr/bin/env python3
"""Quick fix: check bounce detection at n=5."""
import itertools
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
                if abs(word[-1] - word[0]) % n in (1, n-1):
                    results.append(tuple(word))
            return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
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

ms = [3,2,2,2,2]; n = 5
qs = [2,3]
words = enumerate_mover_words(ms, n, 15)
valid = [(w, build_cycle(ms, n, w)) for w in words if len(w)==15]
valid = [(w, c) for w, c in valid if c is not None]

for word, cycle in valid[:5]:
    ell = len(word)
    fc = Counter(word)
    for q in qs:
        if fc[q] != 2: continue
        qL = (q-1)%n; qR = (q+1)%n
        q_steps = [s for s in range(ell) if word[s] == q]
        s1, s2 = q_steps

        # Departure: the mover AFTER q fires is q+1 or q-1
        dep_s1 = word[(s1+1)%ell]
        dep_s2 = word[(s2+1)%ell]

        # Arrival: the mover BEFORE q fires is q+1 or q-1
        arr_s1 = word[(s1-1+ell)%ell]
        arr_s2 = word[(s2-1+ell)%ell]

        print(f"word={word}, q={q}")
        print(f"  s1={s1}, s2={s2}")
        print(f"  dep_s1={dep_s1} ({'qL' if dep_s1==qL else 'qR'}), "
              f"arr_s2={arr_s2} ({'qL' if arr_s2==qL else 'qR'})")
        print(f"  dep_s2={dep_s2} ({'qL' if dep_s2==qL else 'qR'}), "
              f"arr_s1={arr_s1} ({'qL' if arr_s1==qL else 'qR'})")

        # I1 = (s1, s2): starts at dep_s1, ends at arr_s2
        # "bounce" = dep_s1 == arr_s2 (same proc, not same side)
        # Actually: dep_s1 IS a proc number. arr_s2 IS a proc number.
        # They should both be qL or qR.
        # bounce = they're the same proc
        bounce_i1 = (dep_s1 == arr_s2)
        bounce_i2 = (dep_s2 == arr_s1)
        print(f"  I1 bounce: {bounce_i1}, I2 bounce: {bounce_i2}")

        # The issue at n=5: arr might not be qL or qR!
        # At s1: word[s1]=q. The mover at s1-1 is word[s1-1].
        # For the walk: word[s1-1] is adjacent to word[s1]=q.
        # So word[s1-1] is qL or qR. Always.
        # But maybe dep_s1 is NOT qL or qR?
        # dep_s1 = word[s1+1]. Since word[s1]=q, word[s1+1] is adjacent to q.
        # So dep_s1 must be qL or qR.
        assert dep_s1 in [qL, qR], f"dep_s1={dep_s1} not in [{qL},{qR}]"
        assert arr_s2 in [qL, qR], f"arr_s2={arr_s2} not in [{qL},{qR}]"
        print()
        break  # just first q per word
