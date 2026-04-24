"""
Quick check: max simultaneous turnarounds at n=5,7 (exhaustive).
"""
from itertools import combinations

def neighbors(p, n):
    return [(p-1)%n, (p+1)%n]

def enum_cycles(n, ms):
    L = sum(ms)
    rem = list(ms)
    results = []
    def dfs(path):
        if len(path) == L:
            if path[0] in neighbors(path[-1], n):
                results.append(tuple(path))
            return
        last = path[-1]
        for nb in neighbors(last, n):
            if rem[nb] > 0:
                rem[nb] -= 1
                path.append(nb)
                dfs(path)
                path.pop()
                rem[nb] += 1
    for s in range(n):
        if rem[s] > 0:
            rem[s] -= 1
            dfs([s])
            rem[s] += 1
    unique = set()
    for c in results:
        rots = [c[i:]+c[:i] for i in range(len(c))]
        unique.add(min(rots))
    return [list(c) for c in unique]

def classify(mw, b, n):
    L = len(mw)
    fires = [i for i in range(L) if mw[i] == b]
    if len(fires) != 2: return 'bad'
    fi = []
    for idx in fires:
        prev = mw[(idx-1)%L]
        nxt = mw[(idx+1)%L]
        a = 'L' if prev == (b-1)%n else 'R'
        d = 'L' if nxt == (b-1)%n else 'R'
        fi.append((a,d))
    if all(a==d for a,d in fi):
        sides = [f[0] for f in fi]
        return 'same' if sides[0]==sides[1] else 'mixed'
    return 'pt'

for n in [5, 7]:
    threshold = 4 * 3**(n-2)
    overall_max = 0
    total_checked = 0

    for bp in combinations(range(n), 3):
        ms = [3]*n
        for b in bp: ms[b] = 2
        prod = 1
        for m in ms: prod *= m
        if prod >= threshold: continue

        cycles = enum_cycles(n, ms)
        for cyc in cycles:
            net = 0; cw = 0
            for i in range(len(cyc)):
                c, nx = cyc[i], cyc[(i+1)%len(cyc)]
                if nx == (c+1)%n: net += 1; cw += 1
                elif nx == (c-1)%n: net -= 1
            if net//n != 0: continue
            if cw == 0: continue
            f = [0]*n
            for p in cyc: f[p] += 1
            if any(x < 2 for x in f): continue
            total_checked += 1

            ta = sum(1 for b in bp if classify(cyc, b, n) in ('same','mixed'))
            if ta > overall_max:
                overall_max = ta
                types = [classify(cyc, b, n) for b in bp]
                print(f"  n={n}, bp={bp}: {ta} TA, types={types}")

    print(f"n={n}: max TA = {overall_max}, checked {total_checked} cycles")
