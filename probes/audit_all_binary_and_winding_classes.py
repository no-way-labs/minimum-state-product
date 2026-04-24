"""Session 1 audit: classify which winding classes require which theorem.

For each multiset at n=9 sub-threshold, enumerate good cycles at minimum CL
and classify by winding class (sweep / ZW cw>0 / odd winding).

Goal: figure out if the clustering lemma (Theorem A) covers all winding classes
or only ZW cw>0.
"""
from collections import Counter

N = 9

def left(p, n=N): return (p - 1) % n
def right(p, n=N): return (p + 1) % n

def enumerate_gc_at_cl(ms, n, cl, max_results=50000):
    """Enumerate distinct valid good cycles at fixed CL."""
    fire_target = [cl // n if (cl // n) * n == cl else None] * n
    # Actually, fire counts need to satisfy: fc % ms[p] == 0 and sum = cl
    # For min-cl: fc[p] = ms[p] when ms[p]==2 (so 2), ms[p] when ms[p]==3 (so 3).
    # Not general. Let's enumerate by computing min fc distribution.
    # For general cl, could have fc[p] in {ms[p], 2*ms[p], ...}
    results = []

    def dfs(word, fc, config, start_config):
        if len(results) >= max_results:
            return
        if len(word) == cl:
            if config != start_config:
                return
            # Check fc divisibility for each proc
            if not all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                return
            # Uniqueness of intermediate configs
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
        last = word[-1]
        for nxt in (left(last, n), last, right(last, n)):
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

def classify_cycle(word, n):
    """Return ('sweep-cw', 'sweep-ccw', 'zw-cw0', 'zw-cwpos', 'odd') based on winding."""
    CL = len(word)
    cw = sum(1 for k in range(CL) if word[(k + 1) % CL] == right(word[k], n))
    ccw = sum(1 for k in range(CL) if word[(k + 1) % CL] == left(word[k], n))
    stay = CL - cw - ccw
    if cw == CL or ccw == CL:
        return f"pure-sweep-{'cw' if cw==CL else 'ccw'}", cw, ccw, stay
    if ccw == 0 and cw > 0:
        return "sweep-cw", cw, ccw, stay
    if cw == 0 and ccw > 0:
        return "sweep-ccw", cw, ccw, stay
    if cw == ccw:
        return ("zw-cw0" if cw == 0 else "zw-cwpos"), cw, ccw, stay
    return "odd-winding", cw, ccw, stay

MULTISETS = [
    ("3CB mixed",       [2, 2, 2, 3, 3, 3, 3, 3, 3]),
    ("pivot layout",    [2, 3, 2, 3, 3, 3, 3, 3, 3]),
    ("all-odd-gap",     [2, 3, 3, 2, 3, 3, 2, 3, 3]),
    ("all-binary",      [2, 2, 2, 2, 2, 2, 2, 2, 2]),
]

for label, ms in MULTISETS:
    product = 1
    for m in ms:
        product *= m
    # Min CL: sum of ms
    min_cl = sum(ms)
    print(f"\n{'='*70}")
    print(f"{label}: ms={ms}, product={product}, min CL={min_cl}")
    print('=' * 70)
    gcs = enumerate_gc_at_cl(ms, N, min_cl, max_results=200000)
    if not gcs:
        print(f"  No good cycles at CL={min_cl}")
        # Try 2× min
        gcs2 = enumerate_gc_at_cl(ms, N, 2 * min_cl, max_results=5000)
        print(f"  At CL={2*min_cl}: {len(gcs2)} cycles (capped at 5000)")
        continue

    print(f"  {len(gcs)} good cycles found at CL={min_cl}")
    classes = Counter()
    for w in gcs:
        cls, _, _, _ = classify_cycle(w, N)
        classes[cls] += 1
    for cls, cnt in classes.most_common():
        print(f"    {cls:20s}: {cnt}")
