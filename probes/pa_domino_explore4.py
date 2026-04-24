#!/usr/bin/env python3
"""
PA Domino Exploration 4: Find where EC actually comes from in real cycles.

The parity obstruction kills EC at t (the middle binary).
We need to find EC at some other processor — likely at i or right²(i)
(the boundary binary procs with one ternary neighbor).

Strategy: Use the verifier infrastructure to enumerate actual sweep cycles
at n=9 with 3 consecutive binary, and trace where EC occurs.
"""
import sys
sys.path.insert(0, './claude')

# Actually let me work with small n first to understand.
# At n=5 with ms=(2,2,2,3,3), let's enumerate sweep cycles and find EC.

from itertools import product as iproduct
from collections import Counter

def enumerate_good_cycles(n, ms, max_len=None, max_count=10000):
    """Enumerate good cycles via DFS on mover words."""
    if max_len is None:
        max_len = 4 * sum(ms)  # generous bound

    start = tuple(0 for _ in range(n))
    results = []

    def dfs(word, fc, config):
        if len(results) >= max_count: return
        if len(word) > max_len: return
        if len(word) >= n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
                return
        remaining = max_len - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining: return
        for nxt in range(n):
            if abs(nxt - word[-1]) % n not in [1, n-1]: continue
            if len(results) >= max_count: return
            word.append(nxt)
            nf = list(fc); nf[nxt] += 1
            nc = list(config); nc[nxt] = (nc[nxt]+1) % ms[nxt]
            dfs(word, nf, tuple(nc))
            word.pop()

    for p in range(n):
        if len(results) >= max_count: break
        first = list(start); first[p] = (first[p]+1) % ms[p]
        dfs([p], [1 if i==p else 0 for i in range(n)], tuple(first))

    return results

def find_ec(n, ms, word):
    """Find all EC processors and return details."""
    ell = len(word)
    start = tuple(0 for _ in range(n))
    cfgs = [list(start)]
    for i in range(ell):
        c = list(cfgs[-1])
        c[word[i]] = (c[word[i]] + 1) % ms[word[i]]
        cfgs.append(c)

    ec_details = {}
    for p in range(n):
        mover_ctxs = {}  # ctx -> first step
        nonmover_ctxs = {}  # ctx -> first step
        found = None
        for s in range(ell):
            ctx = (cfgs[s][(p-1)%n], cfgs[s][p], cfgs[s][(p+1)%n])
            if word[s] == p:
                if ctx in nonmover_ctxs:
                    found = ('mover_hits_nonmover', s, nonmover_ctxs[ctx], ctx)
                    break
                if ctx not in mover_ctxs:
                    mover_ctxs[ctx] = s
            else:
                if ctx in mover_ctxs:
                    found = ('nonmover_hits_mover', s, mover_ctxs[ctx], ctx)
                    break
                if ctx not in nonmover_ctxs:
                    nonmover_ctxs[ctx] = s
        if found:
            ec_details[p] = found

    return ec_details

def winding(word, n):
    w = 0
    for i in range(len(word)):
        d = (word[(i+1)%len(word)] - word[i]) % n
        if d == 1: w += 1
        elif d == n-1: w -= 1
    return w

def is_sweep(word, n):
    """Check if word is a uniform sweep."""
    w = winding(word, n)
    return w == 0

def analyze_phases(word, n, t):
    """Analyze phases at processor t."""
    ell = len(word)
    t_steps = [s for s in range(ell) if word[s] == t]
    if len(t_steps) < 2:
        return None

    left_t = (t - 1) % n
    right_t = (t + 1) % n

    phases = []
    for idx in range(len(t_steps)):
        a = t_steps[idx]
        b = t_steps[(idx + 1) % len(t_steps)]
        if b <= a: b += ell
        J = sum(1 for s in range(a+1, b) if word[s % ell] == left_t)
        K = sum(1 for s in range(a+1, b) if word[s % ell] == right_t)
        phases.append((J, K))

    return phases

# Test at n=5
n = 5
ms = [2, 2, 2, 3, 3]
print(f"n={n}, ms={ms}, product={eval('*'.join(map(str, ms)))}")
print(f"Enumerating good cycles...")

cycles = enumerate_good_cycles(n, ms, max_len=20, max_count=10000)
print(f"Total cycles: {len(cycles)}")

zw = [w for w in cycles if winding(w, n) == 0]
print(f"Zero-winding: {len(zw)}")

# 3 consecutive binary: positions 0,1,2
# t = 1 (middle), i = 0, right²(i) = 2
t = 1; i_pos = 0; r2_pos = 2

# Find cycles where t has isolated firings and normalForm phases (J+K ≤ 1)
residual_cycles = []
for word in zw:
    ell = len(word)
    fc = Counter(word)
    if fc[t] < 2: continue

    # Check isolated
    t_steps = [s for s in range(ell) if word[s] == t]
    isolated = True
    for s in t_steps:
        if word[(s+1) % ell] == t or word[(s-1) % ell] == t:
            isolated = False
            break
    if not isolated: continue

    # Check phases
    phases = analyze_phases(word, n, t)
    if phases is None: continue

    # Check all phases have J+K ≤ 1 (normalForm residual: dispatch failed)
    all_nf = all(J + K <= 1 for J, K in phases)
    if not all_nf: continue

    residual_cycles.append(word)

print(f"\nNormalForm residual cycles (J+K ≤ 1 at t={t}): {len(residual_cycles)}")

# For those that exist, find where EC occurs
for word in residual_cycles[:20]:
    ec = find_ec(n, ms, word)
    phases = analyze_phases(word, n, t)
    fc = Counter(word)
    print(f"\n  word={word}, len={len(word)}, fc={dict(fc)}")
    print(f"  phases at t={t}: {phases}")
    print(f"  EC at procs: {list(ec.keys())}")
    for p, detail in ec.items():
        print(f"    proc {p} (m={ms[p]}): {detail[0]} ctx={detail[3]} at steps {detail[1]},{detail[2]}")

if not residual_cycles:
    print("No residual cycles found. Let me try without the isolated + parity conditions.")
    print("\nAll zero-winding cycles with J+K ≤ 1 at some phase of t:")

    count = 0
    for word in zw[:500]:
        ell = len(word)
        fc = Counter(word)
        if fc[t] < 2: continue

        phases = analyze_phases(word, n, t)
        if phases is None: continue

        # Check if ANY phase has J+K ≤ 1
        has_sparse = any(J + K <= 1 for J, K in phases)
        # Check if ALL phases have J+K ≤ 1
        all_sparse = all(J + K <= 1 for J, K in phases)

        if all_sparse:
            ec = find_ec(n, ms, word)
            print(f"  word={word}, phases={phases}, fc_t={fc[t]}, EC@{list(ec.keys())}")
            count += 1
            if count >= 10: break

    if count == 0:
        print("  Still none. J+K ≤ 1 (all phases) is very rare at n=5.")
        print("\n  Checking J+K distribution:")
        for word in zw[:200]:
            phases = analyze_phases(word, n, t)
            if phases:
                for J, K in phases:
                    if J + K <= 1:
                        print(f"    word={word[:10]}... phase=({J},{K})")

# Also try n=7, n=9 with more processors
print("\n" + "="*70)
print("Trying n=7, ms=(3,3,2,2,2,3,3)")
print("="*70)

n = 7
ms = [3, 3, 2, 2, 2, 3, 3]
t = 3  # middle of binary triple 2,3,4
print(f"Product: {eval('*'.join(map(str, ms)))}")

cycles7 = enumerate_good_cycles(n, ms, max_len=26, max_count=2000)
print(f"Total cycles: {len(cycles7)}")

zw7 = [w for w in cycles7 if winding(w, n) == 0]
print(f"Zero-winding: {len(zw7)}")

for word in zw7[:100]:
    phases = analyze_phases(word, n, t)
    if phases and all(J + K <= 1 for J, K in phases):
        fc = Counter(word)
        ec = find_ec(n, ms, word)
        print(f"  NF residual: word length={len(word)}, fc_t={fc[t]}, phases={phases}, EC@{list(ec.keys())}")
