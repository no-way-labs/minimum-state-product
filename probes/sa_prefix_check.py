"""For each w TP-reachable from c: is there an SA-reachable a with fc(a) >= fc(w)?
This is seam_pruning_le_far. Already verified at n=10,11 earlier. Now check n=11 k=5."""

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

def reachable(c, excluded=set()):
    visited = {c}; queue = [c]
    while queue:
        cfg = queue.pop(0)
        for j in range(len(cfg)):
            if j in excluded: continue
            d = move(cfg, j)
            if d is not None and d not in visited:
                visited.add(d); queue.append(d)
    return visited

# Check n=11, k=5, k+6=11<=n
n, k = 11, 5
seam = {k-1, k, k+1}
for start in range(3):
    c = [0]*n; c[0] = 0; c[n-1] = 0
    for j in range(1, n-1): c[j] = (start + j) % 3
    c = tuple(c)
    ok = all(c[j] != c[j-1] and c[j] != c[j+1] for j in range(4, n-3))
    if not ok: continue
    if c[k-1] == c[k+1]: continue

    tp = reachable(c)
    sa = reachable(c, excluded=seam)
    max_sa = max(fc(w) for w in sa)

    # Check: for EVERY w in tp, fc(w) <= max_sa?
    for w in tp:
        if fc(w) > max_sa:
            print(f"VIOLATION: c={c}, w={w}, fc(w)={fc(w)}, max_sa={max_sa}")
            break
    else:
        print(f"OK: c={c}, max_sa={max_sa}, max_tp={max(fc(w) for w in tp)}, |tp|={len(tp)}, |sa|={len(sa)}")
