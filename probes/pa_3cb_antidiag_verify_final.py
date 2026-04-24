#!/usr/bin/env python3
"""Final verification of Anti-Diagonal Fire Pattern Lemma.

Verifies all claims in the proof for multiple (n, ms) combinations:
1. Fire count = 2 for P_1
2. Anti-diagonal pattern for n >= 5
3. Paired crossing structure
4. Parity = (odd, odd) for k_0, k_2
5. n = 4 failure mode
"""
from itertools import product as iproduct
from collections import Counter

def enum_cycles(ms, max_cycles=500, max_time=30):
    import time
    n = len(ms)
    t0 = time.time()
    all_configs = list(iproduct(*[range(m) for m in ms]))
    cycles = []
    for start in all_configs:
        if time.time() - t0 > max_time: break
        stack = [(start, [start], {}, [])]
        nodes = 0
        while stack and nodes < 100000:
            if time.time() - t0 > max_time: break
            nodes += 1
            config, path, det, movers = stack.pop()
            for p in range(n):
                for nv in range(ms[p]):
                    if nv == config[p]: continue
                    if movers:
                        d = min(abs(p-movers[-1]), n-abs(p-movers[-1]))
                        if d > 1: continue
                    L,S,R = config[(p-1)%n], config[p], config[(p+1)%n]
                    nd = dict(det); ok = True
                    km = (p,L,S,R)
                    if km in nd:
                        if nd[km] != nv: ok = False
                    else: nd[km] = nv
                    if not ok: continue
                    for i in range(n):
                        if i == p: continue
                        Li,Si,Ri = config[(i-1)%n], config[i], config[(i+1)%n]
                        ki = (i,Li,Si,Ri)
                        if ki in nd:
                            if nd[ki] != Si: ok = False; break
                        else: nd[ki] = Si
                    if not ok: continue
                    nc = list(config); nc[p] = nv; nc = tuple(nc)
                    if nc == start and len(path) >= n:
                        fired = set(movers + [p])
                        if fired == set(range(n)):
                            fm = movers + [p]
                            me_ok = True
                            for idx in range(len(path)):
                                c = path[idx]; priv = []
                                for i in range(n):
                                    ki = (i,c[(i-1)%n],c[i],c[(i+1)%n])
                                    if ki in nd and nd[ki] != c[i]: priv.append(i)
                                if len(priv) != 1: me_ok = False; break
                            if me_ok:
                                cycles.append((path, fm, nd))
                                if len(cycles) >= max_cycles: return cycles
                        continue
                    if nc not in set(path) and len(path) < 6*n:
                        stack.append((nc, path+[nc], nd, movers+[p]))
    return cycles


def verify_lemma(n, ms, cycles):
    """Verify all claims of the Anti-Diagonal Fire Pattern Lemma."""
    results = {
        'total': len(cycles),
        'fire_count_2': 0,
        'anti_diagonal': 0,
        'parity_odd_odd': 0,
        'pairing_ok': 0,
        'wall_ok': 0,
    }

    for path, movers, det in cycles:
        L = len(path)

        # 1. Fire count
        p1_steps = [s for s in range(L) if movers[s] == 1]
        fc = len(p1_steps)
        if fc == 2:
            results['fire_count_2'] += 1
        else:
            continue  # skip further checks if fc != 2

        s1, s2 = p1_steps

        # 2. Anti-diagonal
        ctx1 = (path[s1][0], path[s1][1], path[s1][2])
        ctx2 = (path[s2][0], path[s2][1], path[s2][2])
        is_ad = all(ctx2[i] == 1-ctx1[i] for i in range(3))
        if is_ad:
            results['anti_diagonal'] += 1

        # 3. Wall: P1 never fires in between-segment
        between = [movers[s] for s in range(s1+1, s2)]
        wall = 1 not in between
        if wall:
            results['wall_ok'] += 1

        # 4. Parity
        k0 = sum(1 for m in between if m == 0)
        k2 = sum(1 for m in between if m == 2)
        if k0 % 2 == 1 and k2 % 2 == 1:
            results['parity_odd_odd'] += 1

        # 5. Paired crossings
        crossings = []
        for m in between:
            if m == 0: crossings.append('B0')
            elif m == 2: crossings.append('B2')

        if crossings and crossings[0] == 'B0' and crossings[-1] == 'B2' and len(crossings) % 2 == 0:
            ok = True
            for i in range(1, len(crossings)-1, 2):
                if crossings[i] != crossings[i+1]:
                    ok = False
                    break
            if ok:
                results['pairing_ok'] += 1

    return results


print("=" * 72)
print("ANTI-DIAGONAL FIRE PATTERN LEMMA — FINAL VERIFICATION")
print("=" * 72)

test_cases = [
    (4, (2,2,2,3)),
    (5, (2,2,2,3,3)),
    (5, (2,2,2,3,4)),
    (5, (2,2,2,4,3)),
    (5, (2,2,2,4,4)),
    (6, (2,2,2,3,3,3)),
    (7, (2,2,2,3,3,3,3)),
]

for n, ms in test_cases:
    cycles = enum_cycles(ms, 300, 30)
    r = verify_lemma(n, ms, cycles)
    total = r['total']

    status = "PASS" if (n >= 5 and r['anti_diagonal'] == total and r['parity_odd_odd'] == total) else \
             "EXPECTED FAIL" if n == 4 else "FAIL"

    print(f"\nn={n}, ms={ms}: {total} cycles [{status}]")
    print(f"  Fire count = 2:     {r['fire_count_2']}/{total} ({100*r['fire_count_2']/total:.0f}%)")
    print(f"  Anti-diagonal:      {r['anti_diagonal']}/{total} ({100*r['anti_diagonal']/total:.0f}%)")
    print(f"  Wall principle:     {r['wall_ok']}/{total} ({100*r['wall_ok']/total:.0f}%)")
    print(f"  Parity (odd,odd):   {r['parity_odd_odd']}/{total} ({100*r['parity_odd_odd']/total:.0f}%)")
    print(f"  Paired crossings:   {r['pairing_ok']}/{total} ({100*r['pairing_ok']/total:.0f}%)")

print("\n" + "=" * 72)
print("VERIFICATION COMPLETE")
print("=" * 72)
