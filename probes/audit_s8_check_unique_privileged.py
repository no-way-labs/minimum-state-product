"""Check: does the residual gc actually satisfy `unique_privileged` at ALL
its configs, under the default rule extension?

Lean's GoodCycle structure requires: ∀ c ∈ gc.configs, ∃! i, privileged sys c i.

If we construct sys from gc's observed mover triples + default no-fire on
unobserved, then at each gc config, the chosen mover is privileged. But
is it the UNIQUE privileged proc? Or does the default rule accidentally
make OTHER procs privileged too at gc configs?

If multiple procs are privileged at some gc config under the default rule,
then the constructed (sys, gc) pair is NOT a valid GoodCycle — it violates
unique_privileged. The residual would not be realizable as a Lean GoodCycle
under the default rule.

For other rule extensions (not default), unique_privileged might hold.
"""
from itertools import product
import sys
sys.setrecursionlimit(20000)

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]

def left(p, n=N): return (p - 1) % n
def right(p, n=N): return (p + 1) % n

def build_rule(word, ms, n):
    CL = len(word)
    cfg = [0]*n
    configs = [tuple(cfg)]
    for m in word:
        cfg[m] = (cfg[m] + 1) % ms[m]
        configs.append(tuple(cfg))
    configs = configs[:-1]
    rule = {p: {} for p in range(n)}
    for k in range(CL):
        cfg_k = configs[k]
        mover = word[k]
        for p in range(n):
            lp = left(p, n); rp = right(p, n)
            ctx = (cfg_k[lp], cfg_k[p], cfg_k[rp])
            if p == mover:
                rule[p][ctx] = (cfg_k[p] + 1) % ms[p]
            else:
                if ctx not in rule[p]:
                    rule[p][ctx] = cfg_k[p]
    return rule, configs

def get_priv(rule, cfg, n, ms):
    """Get privileged procs under default-no-fire rule."""
    privs = []
    for p in range(n):
        lp = left(p, n); rp = right(p, n)
        ctx = (cfg[lp], cfg[p], cfg[rp])
        if ctx in rule[p]:
            if rule[p][ctx] != cfg[p]:
                privs.append(p)
        # else: default no-fire
    return privs

def enumerate_residual(ms, n, cl, cap):
    fire_target = list(ms)
    results = []

    def winding_diff(word):
        CL = len(word)
        cw = sum(1 for k in range(CL) if word[(k+1)%CL] == right(word[k], n))
        ccw = sum(1 for k in range(CL) if word[(k+1)%CL] == left(word[k], n))
        return abs(cw - ccw)

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

    def build_configs_fn(word, ms, n):
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
            wd = tuple(word)
            if winding_diff(wd) != 18: return
            if has_provider_interval(wd, ms, n): return
            cfgs = build_configs_fn(list(wd), ms, n)
            if has_any_ec(list(wd), cfgs, n): return
            results.append(wd)
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
        if len(results) >= cap: break
        c = list(start); c[p_start] = (c[p_start] + 1) % ms[p_start]
        fc = [0]*n; fc[p_start] = 1
        dfs([p_start], fc, tuple(c), start)
    return results

print("Testing unique_privileged at gc configs under default rule...")
samples = enumerate_residual(MS, N, 24, cap=20)
print(f"Enumerated {len(samples)} residual samples\n")

all_unique = 0
some_multi = 0
multi_details = []

for s_idx, w in enumerate(samples):
    rule, gc_configs = build_rule(list(w), MS, N)
    unique_at_all = True
    max_priv_count = 0
    for k, cfg in enumerate(gc_configs):
        privs = get_priv(rule, cfg, N, MS)
        if len(privs) > max_priv_count:
            max_priv_count = len(privs)
        if len(privs) != 1:
            unique_at_all = False
    if unique_at_all:
        all_unique += 1
    else:
        some_multi += 1
        multi_details.append((s_idx, max_priv_count))

print(f"All-unique-priv samples: {all_unique}/{len(samples)}")
print(f"Some multi-priv samples: {some_multi}/{len(samples)}")
if multi_details:
    print(f"Multi-priv details (sample idx, max priv count): {multi_details[:5]}")
