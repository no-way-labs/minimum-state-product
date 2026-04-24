"""Session 7: try alternative shadow constructions on the 3% EC-free residual.

Session 3 showed the sweep σ from memory fails for 100% of the 3,648
EC-free odd-winding cycles at (2,3,3,2,3,3,2,3,3) n=9.

Try:
  (1) Rotation shadows: σ_k(p) = (p + k) % n for k = 1..n-1
  (2) Reflection shadows: σ_r(p) = (n - 1 - p) % n
  (3) Mover-word reversal (time-reverse the walker)
  (4) Cycle-doubled shadow (double each step)

Goal: find any permutation / transformation that produces a valid trajectory
disjoint from the original for the residual.
"""
from collections import Counter

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]

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

def winding(word, n):
    CL = len(word)
    cw = sum(1 for k in range(CL) if word[(k+1)%CL] == right(word[k], n))
    ccw = sum(1 for k in range(CL) if word[(k+1)%CL] == left(word[k], n))
    if ccw == 0 and cw > 0: return "sweep-cw"
    if cw == 0 and ccw > 0: return "sweep-ccw"
    if cw == ccw: return "zw-cw0" if cw == 0 else "zw-cwpos"
    return "odd-winding"

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

def validate_word(word, ms, n):
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
        return "not_closed"
    if len(set(configs[:CL])) != CL:
        return "not_unique"
    return "ok"

print("Enumerating cycles and extracting EC-free residual...")
cycles = enumerate_gc(MS, N, 24, cap=500000)
residual = []
for w in cycles:
    if winding(w, N) != "odd-winding": continue
    if has_provider_interval(w, MS, N): continue
    configs = build_configs(list(w), MS, N)
    if not has_any_ec(list(w), configs, N):
        residual.append(w)
print(f"EC-free residual: {len(residual)}")

# Transformation 1: rotation shadows. Since ms is symmetric under rotation
# by 3 (periodic pattern [2,3,3]), rotation by 3 preserves ms — same system.
# Rotations by 1 or 2 give different ms, so they'd be invalid for this system.
print("\n=== Transformation 1: rotation by 3 (preserves ms period) ===")
def rotate(word, k, n):
    return [(p + k) % n for p in word]

rot_valid = 0
rot_disjoint = 0
for w in residual[:500]:
    for k in [3, 6]:
        rot = rotate(w, k, N)
        v = validate_word(rot, MS, N)
        if v == "ok":
            rot_valid += 1
            orig_cfgs = set(build_configs(list(w), MS, N))
            rot_cfgs = set(build_configs(rot, MS, N))
            if not (orig_cfgs & rot_cfgs):
                rot_disjoint += 1
            break
print(f"  Valid shadows from rotation: {rot_valid}/500 tested")
print(f"  Disjoint shadows:            {rot_disjoint}/500")

# Transformation 2: reflection
print("\n=== Transformation 2: reflection σ(p) = (n - p) % n ===")
def reflect(word, n):
    return [(n - p) % n for p in word]

ref_valid = 0
ref_disjoint = 0
for w in residual[:500]:
    ref = reflect(w, N)
    v = validate_word(ref, MS, N)
    if v == "ok":
        ref_valid += 1
        orig_cfgs = set(build_configs(list(w), MS, N))
        ref_cfgs = set(build_configs(ref, MS, N))
        if not (orig_cfgs & ref_cfgs):
            ref_disjoint += 1
print(f"  Valid shadows:    {ref_valid}/500")
print(f"  Disjoint shadows: {ref_disjoint}/500")

# Transformation 3: time reversal
print("\n=== Transformation 3: time reversal ===")
def reverse_time(word):
    return list(reversed(word))

rev_valid = 0
rev_disjoint = 0
for w in residual[:500]:
    rev = reverse_time(list(w))
    v = validate_word(rev, MS, N)
    if v == "ok":
        rev_valid += 1
        orig_cfgs = set(build_configs(list(w), MS, N))
        rev_cfgs = set(build_configs(rev, MS, N))
        if not (orig_cfgs & rev_cfgs):
            rev_disjoint += 1
print(f"  Valid shadows:    {rev_valid}/500")
print(f"  Disjoint shadows: {rev_disjoint}/500")

# Transformation 4: rotate + reflect combined (dihedral action)
print("\n=== Transformation 4: rotate (k=3) + reflect ===")
rr_valid = 0
rr_disjoint = 0
for w in residual[:500]:
    for k in [3, 6]:
        transformed = rotate(reflect(list(w), N), k, N)
        v = validate_word(transformed, MS, N)
        if v == "ok":
            rr_valid += 1
            orig_cfgs = set(build_configs(list(w), MS, N))
            t_cfgs = set(build_configs(transformed, MS, N))
            if not (orig_cfgs & t_cfgs):
                rr_disjoint += 1
            break
print(f"  Valid shadows:    {rr_valid}/500")
print(f"  Disjoint shadows: {rr_disjoint}/500")
