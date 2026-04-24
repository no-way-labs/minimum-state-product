"""Analyze the structure of PhiFull-achieving SA-reachable configs.
What makes them SA-reachable? What's special about them?"""

import sys; sys.setrecursionlimit(200000)

def cup2OutVal(n, j, L, S, R):
    if j == 0: return (S + 1) % 2
    if j == 1:
        tbl = {(0,0):1,(0,1):0,(0,2):0,(1,0):1,(1,1):0,(1,2):2,(2,0):0,(2,1):2,(2,2):1}
        return tbl.get((S, R), S)
    if j + 2 == n:
        tbl = {(0,0,0):1,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):1,
               (1,0,0):1,(1,0,1):1,(1,1,0):0,(1,1,1):2,(1,2,0):1,(1,2,1):1,
               (2,0,0):2,(2,0,1):2,(2,1,0):2,(2,1,1):0,(2,2,0):0,(2,2,1):2}
        return tbl.get((L, S, R), S)
    if j + 1 == n: return (S + 1) % 2
    TMid = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):0,(0,1,2):0,
            (0,2,0):0,(0,2,1):0,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,
            (1,1,0):1,(1,1,1):1,(1,1,2):1,(1,2,0):1,(1,2,1):1,(1,2,2):1,
            (2,0,0):2,(2,0,1):2,(2,0,2):2,(2,1,0):1,(2,1,1):0,(2,1,2):2,
            (2,2,0):0,(2,2,1):2,(2,2,2):2}
    return TMid.get((L, S, R), S)

def fb(a, b): return 1 if a != b else 0
def fc(c): return sum(fb(c[j], c[(j+1) % len(c)]) for j in range(len(c)))

def move(c, j):
    n = len(c)
    L, S, R = c[(j-1)%n], c[j], c[(j+1)%n]
    out = cup2OutVal(n, j, L, S, R)
    if out == S: return None
    return tuple(c[i] if i != j else out for i in range(n))

for n, k in [(11, 5), (12, 5)]:
    seam = {k-1, k, k+1}
    for start in range(3):
        c = [0]*n; c[0] = 0; c[n-1] = 0
        for j in range(1, n-1): c[j] = (start + j) % 3
        c = tuple(c)
        ok = all(c[j] != c[j-1] and c[j] != c[j+1] for j in range(4, n-3))
        if not ok: continue
        if c[k-1] == c[k+1]: continue

        # TP and SA reachable
        tp = {c}; q = [c]
        while q:
            cfg = q.pop(0)
            for j in range(n):
                d = move(cfg, j)
                if d is not None and d not in tp: tp.add(d); q.append(d)
        sa = {c}; q = [c]
        while q:
            cfg = q.pop(0)
            for j in range(n):
                if j in seam: continue
                d = move(cfg, j)
                if d is not None and d not in sa: sa.add(d); q.append(d)

        phi = max(fc(w) for w in tp)
        achievers = [w for w in tp if fc(w) == phi]
        sa_achievers = [w for w in achievers if w in sa]

        print(f"\nn={n} k={k} c={c}")
        print(f"  PhiFull={phi}, |SA achievers|={len(sa_achievers)}")
        for w in sa_achievers[:3]:
            print(f"  SA achiever: {w}")
            print(f"    fc={fc(w)}, deep[{k-1}:{k+2}]={w[k-1:k+2]}")
            # Check: does the achiever have noDeepCopyPair?
            ncp = all(w[j] != w[j-1] and w[j] != w[j+1] for j in range(4, n-3))
            print(f"    noDeepCopyPair: {ncp}")
            # Check: how do seam values compare to c's?
            print(f"    seam vals: w={w[k-1:k+2]} vs c={c[k-1:k+2]}")
            # Check: how do boundary vals compare?
            print(f"    boundary: w[0:4]={w[0:4]}, w[{n-4}:{n}]={w[n-4:n]}")
            print(f"    boundary: c[0:4]={c[0:4]}, c[{n-4}:{n}]={c[n-4:n]}")

        # Key question: is fc = n always? (fc = n means all adjacent pairs distinct)
        print(f"  fc = n? {phi == n}")
        # Check: are ALL achievers "all-distinct" configs?
        all_distinct = all(all(w[j] != w[(j+1)%n] for j in range(n)) for w in achievers)
        print(f"  All achievers are all-distinct: {all_distinct}")
