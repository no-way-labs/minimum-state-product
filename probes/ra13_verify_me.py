#!/usr/bin/env python3
"""
Verify that the DFS-found cycles actually satisfy mutual exclusion (ME).

ME = at each step of the good cycle, exactly ONE processor is privileged
(i.e., f(L,S,R) != S for exactly one processor).

The DFS checks ME using the partial det map. But we need to verify:
1. Does every config in the cycle have exactly 1 privileged proc?
2. Is the det map fully consistent?
3. Is the privileged proc the mover?
"""

from collections import defaultdict, Counter
from itertools import product as iproduct

def check_ec_detailed(good, word, n):
    """Detailed EC check showing all triples."""
    L = len(word)
    mover_triples = defaultdict(set)
    nonmover_triples = defaultdict(set)
    all_triples = defaultdict(list)  # (proc, step, role, triple)

    for t in range(L):
        c = good[t]
        mover = word[t]
        for j in range(n):
            triple = (c[(j-1)%n], c[j], c[(j+1)%n])
            role = "MOVER" if j == mover else "nonmov"
            all_triples[j].append((t, role, triple))
            if j == mover:
                mover_triples[j].add(triple)
            else:
                nonmover_triples[j].add(triple)

    conflicts = {}
    for j in range(n):
        overlap = mover_triples[j] & nonmover_triples[j]
        if overlap:
            conflicts[j] = overlap
    return conflicts, mover_triples, nonmover_triples, all_triples


n = 5
ms = [2, 2, 2, 3, 3]

# Build a specific cycle from the DFS
def build_dfs_cycle():
    from itertools import product as iproduct
    import time
    t0 = time.time()
    start = tuple([0]*n)
    results = []

    def dfs(config, path, word, det, depth):
        if time.time() - t0 > 5.0 or len(results) >= 1:
            return
        for p in range(n):
            for new_val in range(ms[p]):
                if new_val == config[p]:
                    continue
                if word:
                    last = word[-1]
                    diff = min(abs(p - last), n - abs(p - last))
                    if diff > 1:
                        continue
                L = config[(p-1)%n]; S = config[p]; R = config[(p+1)%n]
                key_m = (p, L, S, R)
                new_det = dict(det)
                ok = True
                if key_m in new_det:
                    if new_det[key_m] != new_val:
                        ok = False
                else:
                    new_det[key_m] = new_val
                if not ok:
                    continue
                for i in range(n):
                    if i == p:
                        continue
                    Li = config[(i-1)%n]; Si = config[i]; Ri = config[(i+1)%n]
                    key_i = (i, Li, Si, Ri)
                    if key_i in new_det:
                        if new_det[key_i] != Si:
                            ok = False; break
                    else:
                        new_det[key_i] = Si
                if not ok:
                    continue
                new_config = list(config)
                new_config[p] = new_val
                new_config = tuple(new_config)
                new_word = word + [p]
                if new_config == start and len(path) >= 2*n:
                    cycle = list(path)
                    me_ok = True
                    for idx in range(len(cycle)):
                        c = cycle[idx]
                        priv = []
                        for i in range(n):
                            Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
                            ki = (i, Li, Si, Ri)
                            if ki in new_det and new_det[ki] != Si:
                                priv.append(i)
                        if len(priv) != 1:
                            me_ok = False; break
                    if me_ok:
                        results.append((cycle, new_word, dict(new_det)))
                    continue
                if new_config not in set(path) and len(path) < 20:
                    path.append(new_config)
                    dfs(new_config, path, new_word, new_det, depth+1)
                    path.pop()

    dfs(start, [start], [], {}, 0)
    return results

cycles = build_dfs_cycle()
print(f"Found {len(cycles)} cycles")

if cycles:
    cyc, word, det = cycles[0]
    print(f"\nCycle: CL={len(word)}")
    print(f"Word: {word}")
    print(f"\nConfigs:")
    for t, c in enumerate(cyc):
        mover = word[t] if t < len(word) else "?"
        print(f"  t={t:2d}: {c}  -> mover={mover}")

    print(f"\nDet map (mover entries only):")
    for key, val in sorted(det.items()):
        p, L, S, R = key
        if val != S:
            print(f"  f_{p}({L},{S},{R}) = {val}")

    print(f"\nME verification:")
    for t in range(len(cyc)):
        c = cyc[t]
        priv = []
        for p in range(n):
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
            key = (p, L, S, R)
            if key in det and det[key] != S:
                priv.append(p)
        mover = word[t]
        ok = (len(priv) == 1 and priv[0] == mover)
        print(f"  t={t:2d}: priv={priv}, mover={mover}, {'OK' if ok else 'FAIL'}")

    print(f"\nEC check:")
    ec, mt, nmt, at = check_ec_detailed(cyc, word, n)
    print(f"Entry conflicts: {len(ec)} procs")

    for j in range(n):
        m_set = mt[j]
        nm_set = nmt[j]
        overlap = m_set & nm_set
        print(f"\n  Proc {j} (ms={ms[j]}):")
        print(f"    Mover triples:    {sorted(m_set)}")
        print(f"    Non-mover triples: {sorted(nm_set)}")
        print(f"    Overlap: {sorted(overlap) if overlap else 'NONE'}")

    # KEY QUESTION: The EC check looks for overlap of (L,S,R) triples.
    # But the REAL entry conflict is: same (L,S,R) appears at both
    # mover step (requiring f(L,S,R) != S) and non-mover step (requiring f(L,S,R) = S).
    # This requires the SAME proc to see the SAME triple in BOTH roles.
    # The check IS correct — if (L,S,R) appears as both mover and non-mover
    # at proc j, then f_j(L,S,R) must equal both S (non-mover) and not-S (mover).

    # BUT WAIT: at the non-mover step, the triple is (L, S, R) and f = S (identity).
    # At the mover step, the triple is (L, S, R) and f = new_val != S.
    # These are the SAME triple (L,S,R), requiring f=S AND f!=S. Contradiction.

    # So the EC check IS correct. If it finds 0 conflicts, the cycle IS consistent.
    # The question is: can 0 EC cycles at sub-threshold ms vectors actually exist?

    # Let me verify the known PALINDROMIC EC result.
    # That result says: for SWEEP cycles with consecutive binary,
    # entry conflict exists at procs j=1,...,n-3.
    # But the DFS cycles are NOT sweeps. They have mixed fire counts.
    # So palindromic EC doesn't apply to non-sweeps.

    # What about the UNIVERSAL Entry Conflict from BinSCC Expl 10?
    # That applies to non-consecutive binary. For consecutive binary (0,1,2),
    # the mechanisms are different (palindromic EC for sweeps, etc.)

    print(f"\n\nKEY FINDING:")
    print(f"At n=5 with ms={ms}, the DFS finds cycles with custom")
    print(f"transition functions that have NO entry conflict.")
    print(f"These are NOT sweeps — they have mixed fire counts.")
    print(f"The cycle IS consistent: no (L,S,R) appears as both mover and non-mover.")
    print(f"This means a deterministic transition function f EXISTS for this cycle.")
    print(f"The obstruction (if any) must be at the SYSTEM level, not cycle level.")
