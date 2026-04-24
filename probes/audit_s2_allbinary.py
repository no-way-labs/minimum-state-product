"""Session 2 audit: what mechanism closes all-binary n=9 ZW cw>0 good cycles?

All-binary: ms=(2,2,2,2,2,2,2,2,2). CL=18 at min fire.
Session 1 found 162 ZW cw>0 good cycles.

Questions:
1. Does every such cycle have a direct EC at some binary proc?
2. Does the 0/2 provider route cover them? (Every proc has binary neighbors,
   so the "has binary neighbor" gate is trivial.)
3. Does binary_fc>=4 pigeonhole apply? All have fc=2 here so no.
4. What's the cleanest mechanism for the Lean theorem?
"""
from collections import Counter

N = 9
MS = [2] * 9

def left(p, n=N): return (p - 1) % n
def right(p, n=N): return (p + 1) % n

def enumerate_gc(ms, n, cl, cap=50000):
    fire_target = list(ms)
    results = []
    def dfs(word, fc, config, start_config):
        if len(results) >= cap:
            return
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

def winding(word, n):
    CL = len(word)
    cw = sum(1 for k in range(CL) if word[(k+1)%CL] == right(word[k], n))
    ccw = sum(1 for k in range(CL) if word[(k+1)%CL] == left(word[k], n))
    if ccw == 0 and cw > 0: return "sweep-cw"
    if cw == 0 and ccw > 0: return "sweep-ccw"
    if cw == ccw: return "zw-cw0" if cw == 0 else "zw-cwpos"
    return "odd-winding"

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
        if mov & non:
            return True
    return False

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

print(f"All-binary n=9: ms={MS}")
cycles = enumerate_gc(MS, N, sum(MS), cap=50000)
print(f"Total good cycles at CL={sum(MS)}: {len(cycles)}\n")

# Classify + EC check + provider check
by_class = Counter()
results = {"zw-cwpos": {"total": 0, "has_ec": 0, "has_provider": 0, "ec_free": []}}
for w in cycles:
    cls = winding(w, N)
    by_class[cls] += 1
    if cls != "zw-cwpos": continue
    results["zw-cwpos"]["total"] += 1
    configs = build_configs(list(w), MS, N)
    if has_any_ec(list(w), configs, N):
        results["zw-cwpos"]["has_ec"] += 1
    else:
        if len(results["zw-cwpos"]["ec_free"]) < 3:
            results["zw-cwpos"]["ec_free"].append(w)
    if has_provider_interval(w, MS, N):
        results["zw-cwpos"]["has_provider"] += 1

print(f"By class: {dict(by_class)}")
print()
r = results["zw-cwpos"]
print(f"ZW cw>0: {r['total']} cycles")
print(f"  has EC (any proc):   {r['has_ec']:4d} / {r['total']}")
print(f"  has 0/2 provider:    {r['has_provider']:4d} / {r['total']}")
print(f"  EC-free samples:     {len(r['ec_free'])}")
if r['ec_free']:
    print(f"    first: {r['ec_free'][0]}")
