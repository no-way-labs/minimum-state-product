"""Check properties of residual cycles at n=9, ms=(2,3,3,2,3,3,2,3,3).

(1) Is every residual a "natural cycle sweep" (fc[p] = m_p)?
(2) What does the waterfall potential look like?
(3) Is there a non-residual bad cycle structure?
"""
import sys
sys.setrecursionlimit(20000)
from collections import Counter

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 24

def left(p): return (p - 1) % N
def right(p): return (p + 1) % N

def enumerate_residual(cap=200):
    fire_target = list(MS)
    results = []

    def winding_diff(word):
        CL_ = len(word)
        cw = sum(1 for k in range(CL_) if word[(k+1)%CL_] == right(word[k]))
        ccw = sum(1 for k in range(CL_) if word[(k+1)%CL_] == left(word[k]))
        return abs(cw - ccw)

    def has_provider_interval(word):
        CL_ = len(word)
        fc = [0] * N
        for m in word: fc[m] += 1
        for i in range(N):
            if fc[i] < 2: continue
            li = left(i); ri = right(i)
            if MS[li] != 2 and MS[ri] != 2: continue
            fs = [k for k in range(CL_) if word[k] == i]
            for idx in range(len(fs)):
                a1 = fs[idx]; a2 = fs[(idx+1) % len(fs)]
                if a2 <= a1: a2 += CL_
                if a2 - a1 < 2: continue
                lc = 0; rc = 0
                for k_raw in range(a2 - 1, a1, -1):
                    k = k_raw % CL_
                    m = word[k]
                    if m == i: continue
                    if m == li: lc += 1
                    if m == ri: rc += 1
                    lo = (lc == 0) or (MS[li] == 2 and lc % 2 == 0 and lc >= 2)
                    ro = (rc == 0) or (MS[ri] == 2 and rc % 2 == 0 and rc >= 2)
                    if lo and ro and m != i and (lc > 0 or rc > 0):
                        return True
        return False

    def has_any_ec(word, configs):
        for p in range(N):
            mov, non = set(), set()
            lp = left(p); rp = right(p)
            for k in range(len(word)):
                cfg = configs[k]
                ctx = (cfg[lp], cfg[p], cfg[rp])
                if word[k] == p: mov.add(ctx)
                else: non.add(ctx)
            if mov & non: return True
        return False

    def build_configs(word):
        cfg = [0]*N
        configs = [tuple(cfg)]
        for m in word:
            cfg[m] = (cfg[m] + 1) % MS[m]
            configs.append(tuple(cfg))
        return configs[:-1]

    def dfs(word, fc, config, start_config):
        if len(results) >= cap: return
        if len(word) == CL:
            if config != start_config: return
            if fc != fire_target: return
            cfg = list(start_config)
            seen = {tuple(cfg)}
            for m in word:
                cfg[m] = (cfg[m] + 1) % MS[m]
                t = tuple(cfg)
                if t in seen and t != start_config: return
                seen.add(t)
            if tuple(cfg) != start_config: return
            wd = tuple(word)
            if winding_diff(wd) != 18: return
            if has_provider_interval(wd): return
            cfgs = build_configs(list(wd))
            if has_any_ec(list(wd), cfgs): return
            results.append(wd)
            return
        remaining = CL - len(word)
        needed = sum(max(0, fire_target[p] - fc[p]) for p in range(N))
        if needed > remaining: return
        last = word[-1]
        for nxt in (left(last), last, right(last)):
            if fc[nxt] + 1 > fire_target[nxt]: continue
            new_config = list(config)
            new_config[nxt] = (new_config[nxt] + 1) % MS[nxt]
            word.append(nxt)
            fc[nxt] += 1
            dfs(word, fc, tuple(new_config), start_config)
            word.pop()
            fc[nxt] -= 1
    start = tuple([0]*N)
    for p_start in range(N):
        if len(results) >= cap: break
        c = list(start); c[p_start] = (c[p_start] + 1) % MS[p_start]
        fc = [0]*N; fc[p_start] = 1
        dfs([p_start], fc, tuple(c), start)
    return results

samples = enumerate_residual(cap=500)
print(f"found {len(samples)} residual samples")
print()

# Verify fc = m_p for ALL samples
for i, w in enumerate(samples[:5]):
    fc = Counter(w)
    print(f"sample {i}: fc = {[fc[p] for p in range(N)]}, m = {MS}")
all_match = all(all(Counter(w)[p] == MS[p] for p in range(N)) for w in samples)
print(f"all fc = m_p: {all_match}")

# Walker dynamics: always ccw?
print()
for i, w in enumerate(samples[:5]):
    cw = sum(1 for k in range(CL) if w[(k+1)%CL] == right(w[k]))
    ccw = sum(1 for k in range(CL) if w[(k+1)%CL] == left(w[k]))
    s = sum(1 for k in range(CL) if w[(k+1)%CL] == w[k])
    print(f"sample {i}: cw={cw} ccw={ccw} stay={s}")
