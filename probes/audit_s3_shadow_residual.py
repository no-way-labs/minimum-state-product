"""Session 3 audit: does the shadow-cycle permutation (CIC Expl 11/12) produce
a valid bad cycle for the 3% EC-free odd-winding residual?

Shadow σ for n=9 (from memory):
  σ(0)=5, σ(1)=8, σ(2)=0, σ(3)=1, σ(4)=2, σ(5)=3, σ(6)=4, σ(7)=7, σ(8)=6

Shadow of a good cycle word W is σ(W) — apply σ to each mover. This is
specifically for sweep cycles. For odd-winding, test whether the resulting
configs form a valid closed orbit (even if not via the sweep mirror).

Sample cycle (EC-free, from Session 2):
  ms=[2,3,3,2,3,3,2,3,3]
  word=(0,8,7,6,5,4,3,2,1,0,8,7,8,7,6,5,4,5,4,3,2,1,2,1)
"""
from collections import Counter

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]

def left(p, n=N): return (p - 1) % n
def right(p, n=N): return (p + 1) % n

def build_configs(word, ms, n):
    cfg = [0]*n
    configs = [tuple(cfg)]
    for m in word:
        cfg[m] = (cfg[m] + 1) % ms[m]
        configs.append(tuple(cfg))
    return configs[:-1]

SIGMA = {0:5, 1:8, 2:0, 3:1, 4:2, 5:3, 6:4, 7:7, 8:6}

def apply_sigma(word):
    return [SIGMA[w] for w in word]

def validate_trajectory(word, ms, n):
    """Is the word a valid closed good-cycle-like trajectory?
    Check: fc divisibility, locality, state return, config uniqueness."""
    CL = len(word)
    fc = [0]*n
    for m in word: fc[m] += 1
    if not all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
        return "fc_divisibility"
    for k in range(CL):
        a, b = word[k], word[(k+1)%CL]
        if b not in (a, left(a, n), right(a, n)):
            return "locality"
    cfg = [0]*n
    configs = [tuple(cfg)]
    for m in word:
        cfg[m] = (cfg[m] + 1) % ms[m]
        configs.append(tuple(cfg))
    if configs[-1] != configs[0]:
        return "state_not_returned"
    if len(set(configs[:CL])) != CL:
        return "configs_not_unique"
    return "ok"

# Sample EC-free residual
sample_word = (0,8,7,6,5,4,3,2,1,0,8,7,8,7,6,5,4,5,4,3,2,1,2,1)
print(f"Sample: {sample_word}")
print(f"Validation: {validate_trajectory(list(sample_word), MS, N)}")

# Shadow = apply sigma
shadow_word = apply_sigma(sample_word)
print(f"\nShadow: {tuple(shadow_word)}")
print(f"Validation: {validate_trajectory(shadow_word, MS, N)}")

# Check disjointness: shadow configs should be disjoint from original configs
orig_configs = set(build_configs(list(sample_word), MS, N))
shadow_configs = set(build_configs(shadow_word, MS, N))
print(f"\nOriginal configs: {len(orig_configs)}")
print(f"Shadow configs:   {len(shadow_configs)}")
print(f"Intersection:     {len(orig_configs & shadow_configs)}")

# Do ANY of the configs along the shadow match a good cycle config?
# If not, the shadow is a valid "bad cycle" disjoint from gc → BadCycleData applies.

# Iterate: for each EC-free residual, check if shadow gives a disjoint closed orbit
# that doesn't hit the good cycle.

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

def winding(word, n):
    CL = len(word)
    cw = sum(1 for k in range(CL) if word[(k+1)%CL] == right(word[k], n))
    ccw = sum(1 for k in range(CL) if word[(k+1)%CL] == left(word[k], n))
    if ccw == 0 and cw > 0: return "sweep-cw"
    if cw == 0 and ccw > 0: return "sweep-ccw"
    if cw == ccw: return "zw-cw0" if cw == 0 else "zw-cwpos"
    return "odd-winding"

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

# Enumerate, find EC-free residual, check shadow
print("\n\n=== Bulk test on all EC-free residual cycles ===")
print("Enumerating all-odd-gap cycles at CL=24...")
cycles = enumerate_gc(MS, N, 24, cap=500000)

ec_free_residual = []
for w in cycles:
    if winding(w, N) != "odd-winding": continue
    if has_provider_interval(w, MS, N): continue
    configs = build_configs(list(w), MS, N)
    if not has_any_ec(list(w), configs, N):
        ec_free_residual.append(w)

print(f"EC-free residual: {len(ec_free_residual)}")

# For each, compute shadow and check
valid_shadow = 0
shadow_disjoint = 0
shadow_equal = 0
shadow_fail_validation = 0
shadow_intersect = 0
for w in ec_free_residual:
    shadow = apply_sigma(w)
    v = validate_trajectory(shadow, MS, N)
    if v != "ok":
        shadow_fail_validation += 1
        continue
    valid_shadow += 1
    orig_cfgs = set(build_configs(list(w), MS, N))
    shadow_cfgs = set(build_configs(shadow, MS, N))
    if orig_cfgs == shadow_cfgs:
        shadow_equal += 1
    elif orig_cfgs & shadow_cfgs:
        shadow_intersect += 1
    else:
        shadow_disjoint += 1

print(f"  Shadow valid trajectory:     {valid_shadow}")
print(f"  Shadow == original:          {shadow_equal}")
print(f"  Shadow disjoint from orig:   {shadow_disjoint}")
print(f"  Shadow intersects orig:      {shadow_intersect}")
print(f"  Shadow failed validation:    {shadow_fail_validation}")
