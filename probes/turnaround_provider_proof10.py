"""
Turnaround Provider Proof - Part 10: Understanding the max=2 case
=================================================================
When 2 binary are same-side turnaround, what forces the 3rd to be passthrough?
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

def classify_full(mw, b, n):
    L = len(mw)
    fires = [i for i in range(L) if mw[i] == b]
    if len(fires) != 2: return 'bad', None
    fi = []
    for idx in fires:
        prev = mw[(idx-1)%L]
        nxt = mw[(idx+1)%L]
        a = 'L' if prev == (b-1)%n else 'R'
        d = 'L' if nxt == (b-1)%n else 'R'
        fi.append((a,d))
    if all(a==d for a,d in fi):
        sides = [f[0] for f in fi]
        if sides[0] == sides[1]:
            return f'same_{sides[0]}', fi
        return 'mixed', fi
    return 'pt', fi

def dead_edge(b, turnaround_side, n):
    """Dead edge for same-side turnaround."""
    if turnaround_side == 'L':
        return (b, (b+1)%n)  # right edge is dead
    else:
        return ((b-1)%n, b)  # left edge is dead

# Analyze the 2-TA cases at n=5
n = 5
for bp in combinations(range(n), 3):
    ms = [3]*n
    for b in bp: ms[b] = 2
    prod = 1
    for m in ms: prod *= m
    if prod >= 4*3**(n-2): continue

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

        types_info = [(b, *classify_full(cyc, b, n)) for b in bp]
        ta_count = sum(1 for _, t, _ in types_info if t not in ('pt','bad'))

        if ta_count == 2:
            print(f"bp={bp}, cycle={cyc}")
            for b, t, fi in types_info:
                print(f"  b={b}: {t}, fire_info={fi}")
                if t.startswith('same_'):
                    side = t.split('_')[1]
                    de = dead_edge(b, side, n)
                    print(f"    dead edge: {de}")
            print()

# Same for n=7
print("="*60)
print("n=7:")
print("="*60)
n = 7
for bp in combinations(range(n), 3):
    ms = [3]*n
    for b in bp: ms[b] = 2
    prod = 1
    for m in ms: prod *= m
    if prod >= 4*3**(n-2): continue

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

        types_info = [(b, *classify_full(cyc, b, n)) for b in bp]
        ta_count = sum(1 for _, t, _ in types_info if t not in ('pt','bad'))

        if ta_count == 2:
            fc = f
            print(f"bp={bp}, cycle={cyc}, fc={fc}")
            dead_edges = []
            for b, t, fi in types_info:
                print(f"  b={b}: {t}, fire_info={fi}")
                if t.startswith('same_'):
                    side = t.split('_')[1]
                    de = dead_edge(b, side, n)
                    dead_edges.append(de)
                    print(f"    dead edge: {de}")
            if len(dead_edges) == 2:
                if dead_edges[0] == dead_edges[1]:
                    print(f"  Dead edges OVERLAP: {dead_edges[0]}")
                else:
                    print(f"  Dead edges DISTINCT: {dead_edges}")
            print()
