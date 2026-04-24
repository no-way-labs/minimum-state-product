#!/usr/bin/env python3
"""
FLUSH ALL UNKNOWNS. For each sorry, test the EXACT computational claim.

UNKNOWN 1: Do CaseObstructions:796 (sweep+non-consec) cycles all have EC?
  Need to check at n=7 and n=9 with non-consecutive binary.

UNKNOWN 2: Do CaseObstructions:824 (oddWinding non-uniform) cycles all have EC?
  Need to check at n=7 and n=9.

UNKNOWN 3: For non-alternating rings, does "EC-free → bad 2-cycle in any
  completion" hold universally? Check at n=9 with multiple layouts.

UNKNOWN 4: For alternating zero-winding, does the Phase A mechanism
  dispatch work at n=7 too? (We only checked n=5.)

UNKNOWN 5: Sweep+consecutive — do these ALWAYS lack EC? (Confirming
  wiggle shadow is the only path.) Check n=5 and n=7.
"""
from itertools import product as iproduct
from collections import Counter
import time

def run_checks(n, ms, label, max_len):
    start = tuple(0 for _ in range(n))
    ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}

    has_3consec = any(ms[i]==2 and ms[(i+1)%n]==2 and ms[(i+2)%n]==2 for i in range(n))

    results = []
    def dfs(word, fc, config):
        if len(word) > max_len: return
        if len(word) >= 2*n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
                if len(results) >= 500: return
            return
        if len(results) >= 500: return
        remaining = max_len - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining: return
        last = word[-1]
        for nxt in ring_adj[last]:
            if len(results) >= 500: return
            word.append(nxt)
            nf = list(fc); nf[nxt] += 1
            nc = list(config); nc[nxt] = (nc[nxt]+1) % ms[nxt]
            dfs(word, nf, tuple(nc))
            word.pop()

    t0 = time.time()
    for p in range(n):
        if len(results) >= 500: break
        first = list(start); first[p] = (first[p]+1) % ms[p]
        dfs([p], [1 if i==p else 0 for i in range(n)], tuple(first))
    elapsed = time.time() - t0

    def winding(word):
        w = 0
        for i in range(len(word)):
            d = (word[(i+1)%len(word)] - word[i]) % n
            if d == 1: w += 1
            elif d == n-1: w -= 1
        return w

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

    # Classify
    cats = {}
    for word in results:
        w = winding(word)
        if w == 0: cat = 'zero_wind'
        elif abs(w) >= 2*n: cat = 'sweep'
        elif abs(w) == n: cat = 'odd_wind'
        else: cat = 'other_nonzero'

        if cat not in cats: cats[cat] = {'total': 0, 'ec': 0, 'no_ec': 0}
        cats[cat]['total'] += 1
        if has_ec(word):
            cats[cat]['ec'] += 1
        else:
            cats[cat]['no_ec'] += 1

    print(f"\n{label}: n={n}, ms={ms}, 3consec={has_3consec}")
    print(f"  Cycles found: {len(results)} in {elapsed:.1f}s")
    for cat in sorted(cats):
        c = cats[cat]
        pct = 100*c['ec']/c['total'] if c['total'] > 0 else 0
        status = "✅ ALL EC" if c['no_ec'] == 0 else f"⚠️ {c['no_ec']} NO EC"
        print(f"  {cat}: {c['total']} cycles, EC={c['ec']} ({pct:.0f}%), {status}")

# UNKNOWN 1+2: Non-consecutive at various n
print("=" * 60)
print("UNKNOWNS 1+2: Non-consecutive EC coverage by winding type")
print("=" * 60)
run_checks(5, [2,3,2,3,2], "n=5 alternating", 16)
run_checks(7, [2,3,2,3,2,3,2], "n=7 alternating", 20)

# UNKNOWN 3: Non-alternating
print("\n" + "=" * 60)
print("UNKNOWN 3: Non-alternating layouts")
print("=" * 60)
run_checks(9, [2,3,3,2,3,3,2,3,3], "n=9 [2,3,3]^3", 26)
run_checks(7, [2,3,3,2,3,3,3], "n=7 [2,3,3,2,3,3,3]", 22)
run_checks(6, [2,3,2,3,3,3], "n=6 non-alt", 18)

# UNKNOWN 4: Phase A at n=7
# Already covered by n=7 alternating above

# UNKNOWN 5: Sweep+consecutive
print("\n" + "=" * 60)
print("UNKNOWN 5: Consecutive binary — sweep vs non-sweep EC")
print("=" * 60)
run_checks(5, [2,2,2,3,3], "n=5 consecutive", 16)
run_checks(7, [2,2,2,3,3,3,3], "n=7 consecutive", 20)
