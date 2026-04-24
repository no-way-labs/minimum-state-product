"""Does the 0/2 provider interval structure hold for odd-winding good cycles?

If YES: one uniform Theorem A covers both ZW cw>0 and odd winding non-3CB cases,
        the rewrite plan simplifies, odd winding non-3CB is handled.
If NO: odd winding needs a different mechanism.
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

def winding_class(word, n):
    CL = len(word)
    cw = sum(1 for k in range(CL) if word[(k + 1) % CL] == right(word[k], n))
    ccw = sum(1 for k in range(CL) if word[(k + 1) % CL] == left(word[k], n))
    if ccw == 0 and cw > 0: return "sweep-cw"
    if cw == 0 and ccw > 0: return "sweep-ccw"
    if cw == ccw: return "zw-cw0" if cw == 0 else "zw-cwpos"
    return "odd-winding"

def has_provider_interval(word, ms, n):
    """Check whether there exist i, a1 < a2, k2 with:
       - moverAt a1 = i, moverAt a2 = i, no i-fire in (a1, a2)
       - k2 in (a1, a2), moverAt k2 != i
       - (L=0 and R∈{0 or binary-even}) or (R=0 and L∈{0 or binary-even})
         in [k2, a2), with the nonzero side binary.
       Matches pa_zw_provider_definitive.py's 'exact 0/2' form.
    """
    CL = len(word)
    fc = [0] * n
    for m in word:
        fc[m] += 1

    for i in range(n):
        if fc[i] < 2:
            continue
        li = left(i, n)
        ri = right(i, n)
        if ms[li] != 2 and ms[ri] != 2:
            continue
        fire_steps = [k for k in range(CL) if word[k] == i]
        for idx in range(len(fire_steps)):
            a1 = fire_steps[idx]
            a2_raw = fire_steps[(idx + 1) % len(fire_steps)]
            if a2_raw <= a1:
                a2_raw += CL
            if a2_raw - a1 < 2:
                continue
            # scan backward from a2 - 1 inward
            li_count = 0
            ri_count = 0
            for k_raw in range(a2_raw - 1, a1, -1):
                k = k_raw % CL
                m = word[k]
                if m == i:
                    continue
                if m == li: li_count += 1
                if m == ri: ri_count += 1
                # Accept if one side silent and the other binary-even (≥2)
                li_ok = (li_count == 0) or (ms[li] == 2 and li_count % 2 == 0 and li_count >= 2)
                ri_ok = (ri_count == 0) or (ms[ri] == 2 and ri_count % 2 == 0 and ri_count >= 2)
                if li_ok and ri_ok and m != i:
                    # also require at least one side to have a fire
                    if li_count > 0 or ri_count > 0:
                        return True
    return False

MULTISETS = [
    ("all-odd-gap",       [2, 3, 3, 2, 3, 3, 2, 3, 3]),
    ("pivot-layout",      [2, 2, 3, 2, 3, 3, 3, 3, 3]),
    ("3-all-spaced",      [2, 3, 3, 3, 2, 3, 3, 3, 2]),
]

print("Does clustering (0/2 provider) hold for ODD WINDING cycles too?")
print("Cap per multiset: 500k cycles, split by class\n")

for label, ms in MULTISETS:
    print(f"--- {label}: ms={ms} ---")
    cycles = enumerate_gc(ms, N, sum(ms), cap=500000)
    by_class = {"zw-cwpos": [], "odd-winding": [], "sweep-cw": [], "sweep-ccw": []}
    for w in cycles:
        cls = winding_class(w, N)
        if cls in by_class:
            by_class[cls].append(w)
    for cls, words in by_class.items():
        if not words:
            continue
        pass_count = sum(1 for w in words if has_provider_interval(w, ms, N))
        fail_count = len(words) - pass_count
        verdict = "PASS" if fail_count == 0 else f"FAIL ({fail_count}/{len(words)})"
        print(f"  {cls:15s}: {len(words):6d} cycles, {pass_count:6d} pass  [{verdict}]")
    print()
