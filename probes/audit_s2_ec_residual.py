"""Session 2 audit: are clustering-failing odd-winding cycles actually
EC-free, or do they have ECs via other mechanisms?

Reuses the enumeration from audit_fc2_nopivot but splits by winding class
and, for each clustering-failing cycle, brute-force checks:
  1. Does any proc have an entry conflict (mover context ∩ non-mover context)?
  2. If yes → unrealizable under any rule function → theorem vacuously True.
  3. If no → potentially realizable → real Session 2 gap.

Output: for each multiset, count how many clustering-failing odd-winding
cycles are {has-EC, no-EC}.
"""
from collections import Counter

N = 9

def left(p, n=N): return (p - 1) % n
def right(p, n=N): return (p + 1) % n

def enumerate_gc(ms, n, cl, cap=500000):
    fire_target = list(ms)
    results = []

    def dfs(word, fc, config, start_config):
        if len(results) >= cap:
            return
        if len(word) == cl:
            if config != start_config:
                return
            if fc != fire_target:
                return
            cfg = list(start_config)
            seen = {tuple(cfg)}
            for m in word:
                cfg[m] = (cfg[m] + 1) % ms[m]
                t = tuple(cfg)
                if t in seen and t != start_config:
                    return
                seen.add(t)
            if tuple(cfg) != start_config:
                return
            results.append(tuple(word))
            return
        remaining = cl - len(word)
        needed = sum(max(0, fire_target[p] - fc[p]) for p in range(n))
        if needed > remaining:
            return
        last = word[-1]
        for nxt in (left(last, n), last, right(last, n)):
            if fc[nxt] + 1 > fire_target[nxt]:
                continue
            new_config = list(config)
            new_config[nxt] = (new_config[nxt] + 1) % ms[nxt]
            word.append(nxt)
            fc[nxt] += 1
            dfs(word, fc, tuple(new_config), start_config)
            word.pop()
            fc[nxt] -= 1

    start = tuple([0] * n)
    for p_start in range(n):
        c = list(start)
        c[p_start] = (c[p_start] + 1) % ms[p_start]
        fc = [0] * n
        fc[p_start] = 1
        dfs([p_start], fc, tuple(c), start)
    return results

def build_configs(word, ms, n):
    """Return the config at each step. configs[k] = state AT step k (before firing)."""
    cfg = [0] * n
    configs = [tuple(cfg)]
    for m in word:
        cfg[m] = (cfg[m] + 1) % ms[m]
        configs.append(tuple(cfg))
    return configs[:-1]  # index k = state before mover at k

def winding_class(word, n):
    CL = len(word)
    cw = sum(1 for k in range(CL) if word[(k + 1) % CL] == right(word[k], n))
    ccw = sum(1 for k in range(CL) if word[(k + 1) % CL] == left(word[k], n))
    if ccw == 0 and cw > 0: return "sweep-cw"
    if cw == 0 and ccw > 0: return "sweep-ccw"
    if cw == ccw: return "zw-cw0" if cw == 0 else "zw-cwpos"
    return "odd-winding"

def has_provider_interval(word, ms, n):
    """Same as audit_clustering_oddwinding.py — 0/2 provider check."""
    CL = len(word)
    fc = [0] * n
    for m in word:
        fc[m] += 1
    for i in range(n):
        if fc[i] < 2: continue
        li = left(i, n); ri = right(i, n)
        if ms[li] != 2 and ms[ri] != 2: continue
        fire_steps = [k for k in range(CL) if word[k] == i]
        for idx in range(len(fire_steps)):
            a1 = fire_steps[idx]
            a2_raw = fire_steps[(idx + 1) % len(fire_steps)]
            if a2_raw <= a1: a2_raw += CL
            if a2_raw - a1 < 2: continue
            li_count = 0; ri_count = 0
            for k_raw in range(a2_raw - 1, a1, -1):
                k = k_raw % CL
                m = word[k]
                if m == i: continue
                if m == li: li_count += 1
                if m == ri: ri_count += 1
                li_ok = (li_count == 0) or (ms[li] == 2 and li_count % 2 == 0 and li_count >= 2)
                ri_ok = (ri_count == 0) or (ms[ri] == 2 and ri_count % 2 == 0 and ri_count >= 2)
                if li_ok and ri_ok and m != i:
                    if li_count > 0 or ri_count > 0:
                        return True
    return False

def has_any_ec(word, configs, n):
    """Brute force: does any proc have mover context ∩ non-mover context?
    EC triple = (L, S, R) where proc's left-state, self-state, right-state.
    If a triple appears as mover at some k1 and as non-mover at some k2
    for the same proc, that proc has EC and the cycle is unrealizable.
    """
    CL = len(word)
    for p in range(n):
        mover_ctxs = set()
        nonmover_ctxs = set()
        lp = left(p, n); rp = right(p, n)
        for k in range(CL):
            cfg = configs[k]
            ctx = (cfg[lp], cfg[p], cfg[rp])
            if word[k] == p:
                mover_ctxs.add(ctx)
            else:
                nonmover_ctxs.add(ctx)
        if mover_ctxs & nonmover_ctxs:
            return True
    return False

MULTISETS = [
    ("all-odd-gap",       [2, 3, 3, 2, 3, 3, 2, 3, 3]),
    ("pivot-layout",      [2, 2, 3, 2, 3, 3, 3, 3, 3]),
    ("3-all-spaced",      [2, 3, 3, 3, 2, 3, 3, 3, 2]),
]

print("Are clustering-failing odd-winding cycles unrealizable (EC-positive)?")
print("Cap 500k cycles per multiset.\n")

for label, ms in MULTISETS:
    print(f"--- {label}: ms={ms} ---")
    cycles = enumerate_gc(ms, N, sum(ms), cap=500000)

    # Filter to odd-winding + clustering-failing
    residual = []
    for w in cycles:
        if winding_class(w, N) != "odd-winding": continue
        if has_provider_interval(w, ms, N): continue
        residual.append(w)

    print(f"  {len(residual)} clustering-failing odd-winding cycles")

    ec_positive = 0
    ec_free = 0
    ec_free_samples = []
    for w in residual:
        configs = build_configs(list(w), ms, N)
        if has_any_ec(list(w), configs, N):
            ec_positive += 1
        else:
            ec_free += 1
            if len(ec_free_samples) < 3:
                ec_free_samples.append(w)

    print(f"    has EC (vacuous):     {ec_positive}")
    print(f"    EC-free (real gap):   {ec_free}")
    if ec_free_samples:
        print(f"    First EC-free sample: {ec_free_samples[0]}")
    print()
