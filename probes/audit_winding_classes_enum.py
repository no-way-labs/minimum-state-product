"""Structured enumeration: classify good cycles by winding class.

Uses the same DFS as audit_fc2_nopivot.py but classifies by winding
and runs multiple multisets.
"""
from collections import Counter

N = 9

def left(p, n=N): return (p - 1) % n
def right(p, n=N): return (p + 1) % n

def classify(word, n):
    CL = len(word)
    cw = sum(1 for k in range(CL) if word[(k + 1) % CL] == right(word[k], n))
    ccw = sum(1 for k in range(CL) if word[(k + 1) % CL] == left(word[k], n))
    if ccw == 0 and cw > 0:
        return "sweep-cw"
    if cw == 0 and ccw > 0:
        return "sweep-ccw"
    if cw == ccw:
        return "zw-cw0" if cw == 0 else "zw-cwpos"
    return "odd-winding"

def enumerate_gc(ms, n, cl, cap=200000):
    fire_target = [m if m in (2, 3) else None for m in ms]  # min fc = ms[p] for binary or ternary
    results = []

    def dfs(word, fc, config, start_config):
        if len(results) >= cap:
            return
        if len(word) == cl:
            if config != start_config:
                return
            if fc != fire_target:
                return
            cfg = list(start_config)
            seen = {tuple(cfg)}
            for m in word:
                cfg[m] = (cfg[m] + 1) % ms[m]
                t = tuple(cfg)
                if t in seen and t != start_config:
                    return
                seen.add(t)
            if tuple(cfg) != start_config:
                return
            results.append(tuple(word))
            return
        remaining = cl - len(word)
        needed = sum(max(0, fire_target[p] - fc[p]) for p in range(n))
        if needed > remaining:
            return
        last = word[-1]
        for nxt in (left(last, n), last, right(last, n)):
            if fc[nxt] + 1 > fire_target[nxt]:
                continue
            new_config = list(config)
            new_config[nxt] = (new_config[nxt] + 1) % ms[nxt]
            word.append(nxt)
            fc[nxt] += 1
            dfs(word, fc, tuple(new_config), start_config)
            word.pop()
            fc[nxt] -= 1

    start = tuple([0] * n)
    for p_start in range(n):
        c = list(start)
        c[p_start] = (c[p_start] + 1) % ms[p_start]
        fc = [0] * n
        fc[p_start] = 1
        dfs([p_start], fc, tuple(c), start)
    return results

MULTISETS = [
    ("all-odd-gap",       [2, 3, 3, 2, 3, 3, 2, 3, 3]),
    ("pivot-nosmallset",  [2, 2, 3, 2, 3, 3, 3, 3, 3]),
    ("3-all-spaced",      [2, 3, 3, 3, 2, 3, 3, 3, 2]),
    ("all-binary",        [2, 2, 2, 2, 2, 2, 2, 2, 2]),
]

for label, ms in MULTISETS:
    product = 1
    for m in ms: product *= m
    min_cl = sum(ms)  # works because ms entries are the min-fc
    sub = product < 8748
    print(f"\n{label}: ms={ms}, product={product}, subthreshold={sub}, min CL={min_cl}")
    cycles = enumerate_gc(ms, N, min_cl, cap=500000)
    print(f"  {len(cycles)} good cycles at CL={min_cl}")
    if cycles:
        classes = Counter()
        for w in cycles:
            classes[classify(w, N)] += 1
        for cls, cnt in classes.most_common():
            print(f"    {cls:15s}: {cnt} ({100*cnt/len(cycles):.1f}%)")
