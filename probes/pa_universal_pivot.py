"""Test: for every residual gc, does there exist a pivot proc p* and a shift
delta such that  bad[k] = gc[(k+delta) mod CL] with p* frozen, EXCEPT at
`fire(p*)` steps of gc plus a small number of immediately following steps
(the "patch")?

We compute: for every residual sample, enumerate all pivots p* and all deltas.
For each, classify steps as "clean" (diff only at p*) or "patch" (diff > 1 proc).
Look for: is there always a choice (p*, delta) such that the clean/patch
partition is consistent — i.e., patches are short and bounded in number?

Key structural target: the patches occur ONLY in a neighborhood of gc's
"firing steps for p*".
"""
import sys
sys.setrecursionlimit(20000)
from collections import Counter

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 24  # period

def left(p): return (p - 1) % N
def right(p): return (p + 1) % N

def build_rule_and_configs(word, ms):
    cfg = [0]*N
    configs = [tuple(cfg)]
    for m in word:
        cfg[m] = (cfg[m] + 1) % ms[m]
        configs.append(tuple(cfg))
    configs = configs[:-1]
    rule = {p: {} for p in range(N)}
    for k in range(len(word)):
        cfg_k = configs[k]
        mover = word[k]
        for p in range(N):
            lp = left(p); rp = right(p)
            ctx = (cfg_k[lp], cfg_k[p], cfg_k[rp])
            if p == mover:
                rule[p][ctx] = (cfg_k[p] + 1) % ms[p]
            else:
                if ctx not in rule[p]:
                    rule[p][ctx] = cfg_k[p]
    return rule, configs

def get_priv(rule, cfg):
    privs = []
    for p in range(N):
        lp = left(p); rp = right(p)
        ctx = (cfg[lp], cfg[p], cfg[rp])
        if ctx in rule[p] and rule[p][ctx] != cfg[p]:
            privs.append(p)
    return privs

def step_with(rule, cfg, p):
    lp = left(p); rp = right(p)
    ctx = (cfg[lp], cfg[p], cfg[rp])
    new = list(cfg)
    new[p] = rule[p][ctx]
    return tuple(new)

# Find a bad cycle via deterministic DFS from several candidate starts.
def find_bad_cycle_det(rule, gc_set, starts, max_len=50):
    for start in starts:
        if start in gc_set: continue
        cur = start
        path = []
        seen_idx = {}
        good = True
        while cur not in seen_idx:
            if cur in gc_set:
                good = False; break
            seen_idx[cur] = len(path)
            privs = get_priv(rule, cur)
            if not privs:
                good = False; break
            non_zero = [p for p in privs if p != 0]
            pp = non_zero[0] if non_zero else privs[0]
            path.append((cur, pp))
            cur = step_with(rule, cur, pp)
            if len(path) > max_len:
                good = False; break
        if not good: continue
        cycle_start = seen_idx[cur]
        cycle = path[cycle_start:]
        return cycle
    return None

def enumerate_residual(ms, n, cl, cap):
    fire_target = list(ms)
    results = []

    def winding_diff(word):
        CL_ = len(word)
        cw = sum(1 for k in range(CL_) if word[(k+1)%CL_] == right(word[k]))
        ccw = sum(1 for k in range(CL_) if word[(k+1)%CL_] == left(word[k]))
        return abs(cw - ccw)

    def has_provider_interval(word, ms, n):
        CL_ = len(word)
        fc = [0] * n
        for m in word: fc[m] += 1
        for i in range(n):
            if fc[i] < 2: continue
            li = left(i); ri = right(i)
            if ms[li] != 2 and ms[ri] != 2: continue
            fs = [k for k in range(CL_) if word[k] == i]
            for idx in range(len(fs)):
                a1 = fs[idx]
                a2 = fs[(idx+1) % len(fs)]
                if a2 <= a1: a2 += CL_
                if a2 - a1 < 2: continue
                lc = 0; rc = 0
                for k_raw in range(a2 - 1, a1, -1):
                    k = k_raw % CL_
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
            lp = left(p); rp = right(p)
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
        for nxt in (left(last), last, right(last)):
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

print("Enumerating residual samples...")
samples = enumerate_residual(MS, N, 24, cap=40)
print(f"Found {len(samples)} residual samples\n")

def analyze_shift(gc_configs, bad_configs, pivot):
    """For each shift delta, how many bad configs match gc (mod pivot)?"""
    best = None
    for delta in range(len(gc_configs)):
        clean = 0
        patch_lens = []
        in_patch = False
        cur_patch = 0
        for k in range(len(bad_configs)):
            bk = bad_configs[k]
            gk = gc_configs[(k + delta) % len(gc_configs)]
            diffs = [p for p in range(N) if bk[p] != gk[p]]
            if diffs == [pivot] or (len(diffs)==0):
                clean += 1
                if in_patch:
                    patch_lens.append(cur_patch); cur_patch = 0; in_patch = False
            else:
                in_patch = True; cur_patch += 1
        if in_patch:
            patch_lens.append(cur_patch)
        info = (clean, len(patch_lens), max(patch_lens) if patch_lens else 0, delta)
        if best is None or (info[0], -info[2], -info[1]) > (best[0], -best[2], -best[1]):
            best = info
    return best  # (clean, num_patches, max_patch_len, best_delta)

pass_count = 0
pivot_stats = Counter()
for idx, w in enumerate(samples):
    rule, gc_configs = build_rule_and_configs(list(w), MS)
    gc_set = set(gc_configs)
    starts = []
    for p in range(N):
        for v in range(1, MS[p]):
            c = [0]*N; c[p] = v
            starts.append(tuple(c))
    cycle = find_bad_cycle_det(rule, gc_set, starts)
    if cycle is None:
        print(f"sample {idx}: no bad cycle")
        continue
    bad_configs = [c for c, _ in cycle]
    # Try each pivot, find best
    best_overall = None
    best_pivot = None
    for pivot in range(N):
        a = analyze_shift(gc_configs, bad_configs, pivot)
        if best_overall is None or a[0] > best_overall[0]:
            best_overall = a
            best_pivot = pivot
    clean, npatches, max_plen, delta = best_overall
    print(f"sample {idx}: pivot={best_pivot}, delta={delta}, clean={clean}/{len(bad_configs)}, patches={npatches}, max_plen={max_plen}")
    pivot_stats[best_pivot] += 1
    if clean == len(bad_configs):
        pass_count += 1

print(f"\n{pass_count}/{len(samples)} clean (no patches)")
print(f"pivot distribution: {pivot_stats}")
