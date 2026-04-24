"""Session 7: verify the clustering-failing odd-winding cycles split
cleanly by winding number.

Hypothesis: every residual cycle has |cw - ccw| = 18 (|winding| = 2),
every covered cycle has |cw - ccw| < 18 (|winding| = 1).

If true, Sorry #2 narrows to "double-sweep odd winding no-pivot" — a
specific structurally-uniform family, not an amorphous 3% residue.

Also test across the other no-pivot multisets and check clustering at the
covered side has winding ≤ 1.
"""
from collections import Counter

N = 9
MULTISETS = [
    ("all-odd-gap", [2, 3, 3, 2, 3, 3, 2, 3, 3]),
    ("pivot-layout", [2, 2, 3, 2, 3, 3, 3, 3, 3]),
    ("3-all-spaced", [2, 3, 3, 3, 2, 3, 3, 3, 2]),
]

def left(p, n=N): return (p - 1) % n
def right(p, n=N): return (p + 1) % n

def enumerate_gc(ms, n, cl, cap=500000):
    fire_target = list(ms)
    results = []
    def dfs(word, fc, config, start_config):
        if len(results) >= cap: return
        if len(word) == cl:
            if config != start_config: return
            if fc != fire_target: return
            cfg = list(start_config)
            seen = {tuple(cfg)}
            for m in word:
                cfg[m] = (cfg[m] + 1) % ms[m]
                t = tuple(cfg)
                if t in seen and t != start_config: return
                seen.add(t)
            if tuple(cfg) != start_config: return
            results.append(tuple(word))
            return
        remaining = cl - len(word)
        needed = sum(max(0, fire_target[p] - fc[p]) for p in range(n))
        if needed > remaining: return
        last = word[-1]
        for nxt in (left(last, n), last, right(last, n)):
            if fc[nxt] + 1 > fire_target[nxt]: continue
            new_config = list(config)
            new_config[nxt] = (new_config[nxt] + 1) % ms[nxt]
            word.append(nxt)
            fc[nxt] += 1
            dfs(word, fc, tuple(new_config), start_config)
            word.pop()
            fc[nxt] -= 1
    start = tuple([0]*n)
    for p_start in range(n):
        c = list(start); c[p_start] = (c[p_start] + 1) % ms[p_start]
        fc = [0]*n; fc[p_start] = 1
        dfs([p_start], fc, tuple(c), start)
    return results

def winding_diff(word, n):
    CL = len(word)
    cw = sum(1 for k in range(CL) if word[(k+1)%CL] == right(word[k], n))
    ccw = sum(1 for k in range(CL) if word[(k+1)%CL] == left(word[k], n))
    return cw - ccw

def has_provider_interval(word, ms, n):
    CL = len(word)
    fc = [0] * n
    for m in word: fc[m] += 1
    for i in range(n):
        if fc[i] < 2: continue
        li = left(i, n); ri = right(i, n)
        if ms[li] != 2 and ms[ri] != 2: continue
        fs = [k for k in range(CL) if word[k] == i]
        for idx in range(len(fs)):
            a1 = fs[idx]
            a2 = fs[(idx+1) % len(fs)]
            if a2 <= a1: a2 += CL
            if a2 - a1 < 2: continue
            lc = 0; rc = 0
            for k_raw in range(a2 - 1, a1, -1):
                k = k_raw % CL
                m = word[k]
                if m == i: continue
                if m == li: lc += 1
                if m == ri: rc += 1
                lo = (lc == 0) or (ms[li] == 2 and lc % 2 == 0 and lc >= 2)
                ro = (rc == 0) or (ms[ri] == 2 and rc % 2 == 0 and rc >= 2)
                if lo and ro and m != i and (lc > 0 or rc > 0):
                    return True
    return False

def build_configs(word, ms, n):
    cfg = [0]*n
    configs = [tuple(cfg)]
    for m in word:
        cfg[m] = (cfg[m] + 1) % ms[m]
        configs.append(tuple(cfg))
    return configs[:-1]

def has_any_ec(word, configs, n):
    for p in range(n):
        mov, non = set(), set()
        lp = left(p, n); rp = right(p, n)
        for k in range(len(word)):
            cfg = configs[k]
            ctx = (cfg[lp], cfg[p], cfg[rp])
            if word[k] == p: mov.add(ctx)
            else: non.add(ctx)
        if mov & non: return True
    return False

for label, ms in MULTISETS:
    print(f"\n=== {label}: ms={ms} ===")
    cl = sum(ms)
    cycles = enumerate_gc(ms, N, cl, cap=500000)
    res_windings = Counter()
    cov_windings = Counter()
    ec_windings = Counter()
    for w in cycles:
        diff = winding_diff(w, N)
        if diff == 0: continue  # ZW or sweep
        if abs(diff) == cl: continue  # pure sweep
        # odd winding
        if has_provider_interval(w, ms, N):
            cov_windings[abs(diff)] += 1
        else:
            configs = build_configs(list(w), ms, N)
            if has_any_ec(list(w), configs, N):
                ec_windings[abs(diff)] += 1
            else:
                res_windings[abs(diff)] += 1
    print(f"  Covered (clustering) |winding|: {dict(sorted(cov_windings.items()))}")
    print(f"  EC-positive residual |winding|: {dict(sorted(ec_windings.items()))}")
    print(f"  EC-free residual    |winding|: {dict(sorted(res_windings.items()))}")
