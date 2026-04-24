"""Check: is the PhiFull-achieving config always SA-reachable from c?
If yes: max_SA >= PhiFull trivially."""

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

for n, k in [(11, 5), (12, 5), (12, 6), (13, 5)]:
    if k + 6 > n: continue
    seam = {k-1, k, k+1}

    for start in range(3):
        c = [0]*n; c[0] = 0; c[n-1] = 0
        for j in range(1, n-1): c[j] = (start + j) % 3
        c = tuple(c)
        ok = all(c[j] != c[j-1] and c[j] != c[j+1] for j in range(4, n-3))
        if not ok: continue
        if c[k-1] == c[k+1]: continue

        # TP-reachable
        tp = {c}; queue = [c]
        while queue:
            cfg = queue.pop(0)
            for j in range(n):
                d = move(cfg, j)
                if d is not None and d not in tp:
                    tp.add(d); queue.append(d)

        # SA-reachable
        sa = {c}; queue = [c]
        while queue:
            cfg = queue.pop(0)
            for j in range(n):
                if j in seam: continue
                d = move(cfg, j)
                if d is not None and d not in sa:
                    sa.add(d); queue.append(d)

        phi = max(fc(w) for w in tp)
        msa = max(fc(w) for w in sa)

        # Find ALL PhiFull achievers
        achievers = [w for w in tp if fc(w) == phi]
        sa_achievers = [w for w in achievers if w in sa]

        print(f"n={n} k={k} c[4:7]={c[4:7]}: PhiFull={phi} max_SA={msa} "
              f"|achievers|={len(achievers)} |sa_achievers|={len(sa_achievers)} "
              f"{'✓' if sa_achievers else '✗ NO SA ACHIEVER'}")
