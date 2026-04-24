#!/usr/bin/env python3
"""Debug: check actual OW-NU words and their step structure."""
from itertools import combinations


def total_displacement(word, n):
    W = 0
    L = len(word)
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 0:
            pass
        elif diff <= n // 2:
            W += diff
        else:
            W -= (n - diff)
    return W


def step_directions(word, n):
    L = len(word)
    dirs = []
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 0:
            dirs.append(0)
        elif diff == 1:
            dirs.append(1)
        elif diff == n - 1:
            dirs.append(-1)
        else:
            dirs.append(diff if diff <= n // 2 else diff - n)
    return dirs


def gen_words(n, fc_target, max_results=50, timeout_s=5):
    import time
    target_cl = sum(fc_target)
    results = []
    t0 = time.time()
    def dfs(word, fc):
        if time.time() - t0 > timeout_s or len(results) >= max_results:
            return
        if len(word) == target_cl:
            if all(fc[p] == fc_target[p] for p in range(n)):
                results.append(tuple(word))
            return
        remaining = target_cl - len(word)
        needed = sum(max(0, fc_target[p] - fc[p]) for p in range(n))
        if needed > remaining:
            return
        last = word[-1]
        for nxt in [(last + 1) % n, (last - 1) % n]:
            if fc[nxt] < fc_target[nxt]:
                fc[nxt] += 1
                word.append(nxt)
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1
    for start in range(n):
        if time.time() - t0 > timeout_s or len(results) >= max_results:
            break
        fc = [0] * n
        fc[start] = 1
        if fc[start] <= fc_target[start]:
            dfs([start], fc)
    return results


n = 5
ms = [2, 2, 3, 2, 3]
fc_target = list(ms)
words = gen_words(n, fc_target, max_results=20)
print(f"Generated {len(words)} words")

for w in words[:10]:
    wl = list(w)
    W = total_displacement(wl, n)
    dirs = step_directions(wl, n)
    cw = sum(1 for d in dirs if d == 1)
    ccw = sum(1 for d in dirs if d == -1)
    ns_d = [d for d in dirs if d != 0]
    uniform = all(d == ns_d[0] for d in ns_d) if ns_d else True
    print(f"  word={wl}, W={W}, CW={cw}, CCW={ccw}, uniform={uniform}")
    if abs(W) == n:
        print(f"    *** ODD WINDING, non-uniform={not uniform}")
        print(f"    dirs={dirs}")
        # Check: CW-CCW should be +-5 or +-5 + k*n for some k
        print(f"    CW-CCW={cw-ccw}, n={n}")
        # But wait: dirs may contain values other than +-1!
        print(f"    sum(dirs)={sum(dirs)}")
