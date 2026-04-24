#!/usr/bin/env python3
"""
MAP THE FULL TERRAIN. For every sorry, identify:
1. Exactly which cycles it needs to handle
2. Whether those cycles have EC
3. If not EC: are they uniform-direction sweeps (shadow applies)?
4. If not: what ARE they?

Goal: find a LOW RISK path for every single sorry.
"""
from itertools import product as iproduct
from collections import Counter
import time

def full_analysis(n, ms, max_len, label):
    start = tuple(0 for _ in range(n))
    ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}
    has_3consec = any(ms[i]==2 and ms[(i+1)%n]==2 and ms[(i+2)%n]==2 for i in range(n))
    is_alternating = all(ms[i]==2 if i%2==0 else ms[i]==3 for i in range(n)) or \
                     all(ms[i]==3 if i%2==0 else ms[i]==2 for i in range(n))

    results = []
    def dfs(word, fc, config):
        if len(word) > max_len: return
        if len(word) >= 2*n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
                if len(results) >= 1000: return
            return
        if len(results) >= 1000: return
        remaining = max_len - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining: return
        last = word[-1]
        for nxt in ring_adj[last]:
            if len(results) >= 1000: return
            word.append(nxt)
            nf = list(fc); nf[nxt] += 1
            nc = list(config); nc[nxt] = (nc[nxt]+1) % ms[nxt]
            dfs(word, nf, tuple(nc))
            word.pop()

    t0 = time.time()
    for p in range(n):
        if len(results) >= 1000: break
        first = list(start); first[p] = (first[p]+1) % ms[p]
        dfs([p], [1 if i==p else 0 for i in range(n)], tuple(first))

    def winding(word):
        w = 0
        for i in range(len(word)):
            d = (word[(i+1)%len(word)] - word[i]) % n
            if d == 1: w += 1
            elif d == n-1: w -= 1
        return w

    def is_uniform_dir(word):
        ell = len(word)
        cw = sum(1 for i in range(ell) if (word[(i+1)%ell] - word[i]) % n == 1)
        ccw = sum(1 for i in range(ell) if (word[(i+1)%ell] - word[i]) % n == n-1)
        return cw == 0 or ccw == 0

    def has_ec(word):
        ell = len(word)
        cfgs = [list(start)]
        for i in range(ell):
            c = list(cfgs[-1]); c[word[i]] = (c[word[i]]+1) % ms[word[i]]
            cfgs.append(c)
        for p in range(n):
            m_ctx, n_ctx = set(), set()
            for s in range(ell):
                ctx = (cfgs[s][(p-1)%n], cfgs[s][p], cfgs[s][(p+1)%n])
                if word[s] == p:
                    if ctx in n_ctx: return True
                    m_ctx.add(ctx)
                else:
                    if ctx in m_ctx: return True
                    n_ctx.add(ctx)
        return False

    print(f"\n{'='*60}")
    print(f"{label}: n={n}, ms={ms}")
    print(f"  3consec={has_3consec}, alternating={is_alternating}")
    print(f"  Cycles: {len(results)} in {time.time()-t0:.1f}s")

    # Full classification
    for word in results:
        w = winding(word)
        ec = has_ec(word)
        uniform = is_uniform_dir(word)

        if w == 0: wtype = 'ZW'
        elif abs(w) >= 2*n: wtype = 'SWEEP'
        elif abs(w) == n: wtype = 'ODD'
        else: wtype = 'OTHER_NZ'

        key = (wtype, ec, uniform)
        if key not in full_analysis.counts:
            full_analysis.counts[key] = 0
        full_analysis.counts[key] += 1

    # Print results grouped by sorry-relevance
    print(f"\n  Winding | EC? | Uniform? | Count | Sorry | Approach")
    print(f"  --------|-----|----------|-------|-------|--------")
    for (wtype, ec, uniform), count in sorted(full_analysis.counts.items()):
        ec_str = "EC" if ec else "noEC"
        uni_str = "uniform" if uniform else "non-uni"

        # Determine which sorry and approach
        if ec:
            approach = "✅ Mechanisms (proved)"
            sorry = "Track B"
        elif wtype == 'SWEEP' and uniform:
            approach = "✅ Shadow Mirror (proved)"
            sorry = "Track A"
        elif wtype == 'SWEEP' and not uniform:
            approach = "⚠️ Wiggle shadow? Or convergence?"
            sorry = "Track A/C"
        else:
            approach = "❓ Unknown"
            sorry = "???"

        print(f"  {wtype:8} | {ec_str:4} | {uni_str:8} | {count:5} | {sorry:7} | {approach}")

    result = dict(full_analysis.counts)
    full_analysis.counts = {}
    return result

full_analysis.counts = {}

# Test all relevant configurations
full_analysis(5, [2,2,2,3,3], 16, "n=5 consecutive")
full_analysis.counts = {}
full_analysis(5, [2,3,2,3,2], 16, "n=5 alternating non-consec")
full_analysis.counts = {}
full_analysis(7, [2,2,2,3,3,3,3], 20, "n=7 consecutive")
full_analysis.counts = {}
full_analysis(7, [2,3,2,3,2,3,2], 20, "n=7 alternating non-consec")
full_analysis.counts = {}
full_analysis(7, [2,3,3,2,3,3,3], 22, "n=7 non-alternating non-consec")
full_analysis.counts = {}
full_analysis(9, [2,3,3,2,3,3,2,3,3], 26, "n=9 non-alternating non-consec")
full_analysis.counts = {}

print("\n" + "="*60)
print("SUMMARY: Which cells have no proven approach?")
print("="*60)
print("Only SWEEP+noEC+non-uniform needs a new argument.")
print("Everything else is handled by mechanisms (EC) or shadow (uniform sweep).")
