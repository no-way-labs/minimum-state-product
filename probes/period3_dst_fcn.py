"""For actual period3 dst configs (noDeepCopyPair + hasCyclingSite' + boundary-changing):
check if PhiFull = n (all-distinct achievable) and max_SA = n."""

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

def has_nocopy(c, n):
    return all(c[j] != c[j-1] and c[j] != c[j+1] for j in range(4, n-3))

def has_cycling(c, n):
    for k in range(5, n-4):
        if c[k-1] != c[k+1]: return True
    return False

def reachable(c, excluded=set()):
    n = len(c)
    visited = {c}; queue = [c]
    while queue:
        cfg = queue.pop(0)
        for j in range(n):
            if j in excluded: continue
            d = move(cfg, j)
            if d is not None and d not in visited:
                visited.add(d); queue.append(d)
    return visited

n = 11; k = 5; seam = {k-1, k, k+1}
# Collect unique dst configs with noDeepCopyPair + hasCyclingSite'
dst_configs = set()
for start in range(3):
    c0 = [0]*n; c0[0] = 0; c0[n-1] = 0
    for j in range(1, n-1): c0[j] = (start + j) % 3
    c0 = tuple(c0)
    tp = reachable(c0)
    for src in tp:
        for j in range(n):
            dst = move(src, j)
            if dst is None: continue
            if has_nocopy(dst, n) and has_cycling(dst, n):
                dst_configs.add(dst)

print(f"n={n}: {len(dst_configs)} unique period3 dst configs")

# For each: check PhiFull and max_SA
phi_fail = 0
sa_fail = 0
checked = 0
for dst in list(dst_configs)[:500]:  # sample
    checked += 1
    tp_dst = reachable(dst)
    sa_dst = reachable(dst, excluded=seam)
    phi = max(fc(w) for w in tp_dst)
    msa = max(fc(w) for w in sa_dst)
    if phi != n:
        phi_fail += 1
    if msa != n:
        sa_fail += 1
        if sa_fail <= 2:
            print(f"  SA FAIL: dst={dst}, PhiFull={phi}, max_SA={msa}")

print(f"Checked {checked}: PhiFull!=n: {phi_fail}, max_SA!=n: {sa_fail}")
