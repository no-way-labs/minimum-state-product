"""Session 7: structural characterization of the 3% EC-free residual.

What's special about the 3,648 EC-free odd-winding cycles at
(2,3,3,2,3,3,2,3,3) n=9 that distinguishes them from the 92% covered
by clustering?

Check:
  (1) Fire count distribution: are they all at min fc, or do some have excess?
  (2) Winding count (cw - ccw): narrow range? bimodal?
  (3) Stay step count: anomalously high?
  (4) Max consecutive same-mover count: do they have long runs?
  (5) Symmetry orbit size (invariant under rotation by 3)
  (6) Mover pattern prefix: is there a canonical starting structure?
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
    if ccw == 0 and cw > 0: return "sweep-cw", cw, ccw
    if cw == 0 and ccw > 0: return "sweep-ccw", cw, ccw
    if cw == ccw: return ("zw-cw0" if cw == 0 else "zw-cwpos"), cw, ccw
    return "odd-winding", cw, ccw

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

print("Enumerating cycles and classifying residual...")
cycles = enumerate_gc(MS, N, 24, cap=500000)
residual = []
covered = []
for w in cycles:
    cls, cw, ccw = winding(w, N)
    if cls != "odd-winding": continue
    if has_provider_interval(w, MS, N):
        covered.append((w, cw, ccw))
        continue
    configs = build_configs(list(w), MS, N)
    if not has_any_ec(list(w), configs, N):
        residual.append((w, cw, ccw))

print(f"Covered by clustering:  {len(covered)}")
print(f"EC-free residual:       {len(residual)}")
print()

# (1) Fire count distribution — since we enumerated at min CL=24 all should be at min fc
fc_shapes_res = Counter(tuple(sum(1 for x in w if x == p) for p in range(N)) for w, _, _ in residual)
fc_shapes_cov = Counter(tuple(sum(1 for x in w if x == p) for p in range(N)) for w, _, _ in covered[:5000])
print(f"(1) Fire count shapes (residual): {len(fc_shapes_res)} distinct")
print(f"    Top: {fc_shapes_res.most_common(3)}")
print(f"    Fire count shapes (covered sample): {len(fc_shapes_cov)} distinct")
print()

# (2) Winding counts
print("(2) Winding count (cw - ccw) distribution")
res_widings = Counter((cw, ccw) for _, cw, ccw in residual)
cov_widings = Counter((cw, ccw) for _, cw, ccw in covered)
print(f"    Residual (cw, ccw) modes: {res_widings.most_common(5)}")
print(f"    Covered  (cw, ccw) modes: {cov_widings.most_common(5)}")
print()

# (3) Stay step count
print("(3) Stay step count")
def stay_count(w, n):
    return sum(1 for k in range(len(w)) if w[(k+1) % len(w)] == w[k])
res_stay = Counter(stay_count(w, N) for w, _, _ in residual)
cov_stay = Counter(stay_count(w, N) for w, _, _ in covered[:5000])
print(f"    Residual stays: {dict(res_stay)}")
print(f"    Covered stays:  {dict(cov_stay)}")
print()

# (4) Max consecutive same-mover
def max_run(w):
    ell = len(w)
    best = 1
    cur = 1
    for k in range(1, 2 * ell):
        if w[k % ell] == w[(k - 1) % ell]:
            cur += 1
            best = max(best, cur)
        else:
            cur = 1
    return best
res_run = Counter(max_run(w) for w, _, _ in residual)
cov_run = Counter(max_run(w) for w, _, _ in covered[:5000])
print("(4) Max consecutive same-mover run")
print(f"    Residual: {dict(res_run)}")
print(f"    Covered : {dict(cov_run)}")
print()

# (5) Symmetry orbit under rotation by 3
print("(5) Rotation-by-3 orbit size")
def orbit_under_rot3(w, n):
    ws = [tuple(w)]
    for _ in range(2):
        ws.append(tuple((p + 3) % n for p in ws[-1]))
    return len(set(ws))
res_orb = Counter(orbit_under_rot3(w, N) for w, _, _ in residual)
cov_orb = Counter(orbit_under_rot3(w, N) for w, _, _ in covered[:5000])
print(f"    Residual: {dict(res_orb)}")
print(f"    Covered : {dict(cov_orb)}")
print()

# (6) Fire patterns at binaries (are they clustered or spread?)
print("(6) Max gap between binary fires (among binaries at 0, 3, 6)")
def max_binary_gap(w, binaries, n):
    ell = len(w)
    max_gap = 0
    for b in binaries:
        fs = sorted(k for k in range(ell) if w[k] == b)
        if len(fs) < 2: continue
        # cyclic gaps
        gaps = [(fs[(i+1) % len(fs)] - fs[i]) % ell for i in range(len(fs))]
        max_gap = max(max_gap, max(gaps))
    return max_gap
binaries = [0, 3, 6]
res_gap = Counter(max_binary_gap(w, binaries, N) for w, _, _ in residual)
cov_gap = Counter(max_binary_gap(w, binaries, N) for w, _, _ in covered[:5000])
print(f"    Residual max-binary-gap distribution: {dict(sorted(res_gap.items()))}")
print(f"    Covered  max-binary-gap distribution: {dict(sorted(cov_gap.items()))}")
