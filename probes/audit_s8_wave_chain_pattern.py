"""Exploration 9: Does the 'wave chain' bad cycle formula hold deterministically?

For multiple residual cycles in all-odd-gap (2,3,3,2,3,3,2,3,3) at n=9,
find the bad cycle under the default rule extension and check:
  - Is it always length 24 (same as gc)?
  - Does it always start at a 'wave-like' config?
  - Does the mover word follow a consistent structure?
  - Is there a FORMULA mapping gc's structure to the bad cycle's structure?

If the bad cycle is deterministic (given a starting config), we have a
canonical witness for Lean. If not, we need a more flexible existence proof.
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

def get_priv(rule, cfg, n):
    privs = []
    for p in range(n):
        lp = left(p, n); rp = right(p, n)
        ctx = (cfg[lp], cfg[p], cfg[rp])
        if ctx in rule[p] and rule[p][ctx] != cfg[p]:
            privs.append(p)
    return privs

def step_with(rule, cfg, p, n):
    lp = left(p, n); rp = right(p, n)
    ctx = (cfg[lp], cfg[p], cfg[rp])
    new = list(cfg)
    new[p] = rule[p][ctx]
    return tuple(new)

def find_bad_cycle_deterministic(rule, gc_set, start, n, max_len=50):
    """Walk from start, always pick the lowest-numbered privileged proc,
    return the cycle if found, else None."""
    cur = start
    path = []
    seen_idx = {}
    while cur not in seen_idx:
        if cur in gc_set:
            return None
        seen_idx[cur] = len(path)
        privs = get_priv(rule, cur, n)
        if not privs:
            return None
        # Prefer non-sweepStartProc (proc 0) privs to avoid fc mismatch
        non_zero = [p for p in privs if p != 0]
        p = non_zero[0] if non_zero else privs[0]
        path.append((cur, p))
        cur = step_with(rule, cur, p, n)
        if len(path) > max_len:
            return None
    cycle_start = seen_idx[cur]
    return path[cycle_start:]

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

print("Enumerating residual samples...")
samples = enumerate_residual(MS, N, 24, cap=20)
print(f"Found {len(samples)} residual samples\n")

# For each sample, find the bad cycle (deterministic DFS) and report
results = []
for s_idx, w in enumerate(samples):
    rule, gc_configs = build_rule(list(w), MS, N)
    gc_set = set(gc_configs)
    # Try multiple starting configs
    starts_to_try = []
    for p in range(N):
        for v in range(1, MS[p]):
            c = [0]*N
            c[p] = v
            starts_to_try.append(tuple(c))

    found = None
    for start in starts_to_try:
        if start in gc_set: continue
        cycle = find_bad_cycle_deterministic(rule, gc_set, start, N)
        if cycle is not None:
            found = cycle
            break

    if found is None:
        print(f"Sample {s_idx+1}: NO bad cycle found via deterministic DFS")
    else:
        bad_word = tuple(p for _, p in found)
        bad_start = found[0][0]
        results.append((s_idx, len(found), bad_start, bad_word))
        print(f"Sample {s_idx+1}: bad cycle length {len(found)}, start={bad_start}, word={bad_word}")

# Analyze patterns
print(f"\n{len(results)}/{len(samples)} samples had deterministic bad cycle")
if results:
    from collections import Counter
    lengths = Counter(r[1] for r in results)
    print(f"Lengths: {dict(lengths)}")
