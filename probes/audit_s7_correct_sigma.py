"""Session 7: Search for a shadow σ that works on the 3% residual.

Findings so far:
- Residual has |cw-ccw| = 18 = 2*n at n=9 → IS a sweep per Lean's def.
- σ from memory (for binary at 0,1,2) doesn't apply to residual (binary at 0,3,6).
- Period-3 symmetries (rot by 3, reflect, time reverse) all give overlapping shadows.

Try: brute force all permutations σ of {0..8} that fix {0,3,6} setwise
(6 permutations, since binary stays binary). For each, check if applying σ
to a residual mover-word gives a valid trajectory disjoint from the original.
"""
from itertools import permutations
from collections import Counter

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
BINARY = {0, 3, 6}

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

def validate_word(word, ms, n):
    CL = len(word)
    fc = [0]*n
    for m in word: fc[m] += 1
    if not all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
        return False
    for k in range(CL):
        a, b = word[k], word[(k+1)%CL]
        if b not in (a, left(a, n), right(a, n)):
            return False
    cfg = [0]*n
    configs = [tuple(cfg)]
    for m in word:
        cfg[m] = (cfg[m] + 1) % ms[m]
        configs.append(tuple(cfg))
    if configs[-1] != configs[0]:
        return False
    if len(set(configs[:CL])) != CL:
        return False
    return True

# Generate all permutations σ of {0..8} that map ms[p] → ms[σ(p)] (preserving structure)
# Equivalently: σ(binary) ⊆ binary.
print("Finding ms-preserving permutations of {0..8}...")
valid_perms = []
for perm in permutations(range(N)):
    if all(MS[perm[p]] == MS[p] for p in range(N)):
        valid_perms.append(perm)
print(f"Found {len(valid_perms)} ms-preserving permutations")

# Filter to ring-locality-preserving:
# For permutations to give locality-valid mover words, we need σ to be a ring
# automorphism (rotation or reflection). Let's just try them all.

print("\nEnumerating residual cycles...")
cycles = enumerate_gc(MS, N, 24, cap=500000)
residual = []
for w in cycles:
    if abs(winding_diff(w, N)) != 18: continue  # only |winding|=2 = sweep
    if has_provider_interval(w, MS, N): continue
    configs = build_configs(list(w), MS, N)
    if has_any_ec(list(w), configs, N): continue
    residual.append(w)
print(f"Sweep EC-free residual: {len(residual)}")

# For each permutation, check disjoint shadow rate on a sample
print("\nTesting each permutation as a shadow construction:")
sample = residual[:200]
results = []
for perm in valid_perms:
    valid_count = 0
    disjoint_count = 0
    for w in sample:
        shadow = [perm[p] for p in w]
        if validate_word(shadow, MS, N):
            valid_count += 1
            orig_cfgs = set(build_configs(list(w), MS, N))
            sh_cfgs = set(build_configs(shadow, MS, N))
            if not (orig_cfgs & sh_cfgs):
                disjoint_count += 1
    results.append((perm, valid_count, disjoint_count))

# Sort by disjoint count
results.sort(key=lambda x: -x[2])
for perm, vc, dc in results[:10]:
    is_id = perm == tuple(range(N))
    print(f"  σ={perm} valid={vc:3d} disjoint={dc:3d}{' (identity)' if is_id else ''}")
