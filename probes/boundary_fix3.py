"""BFS: min number of boundary-only SA steps to reach fc=n."""

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

# Boundary positions: 0, 1, 2, 3, n-3, n-2, n-1
def boundary_bfs(c, k):
    n = len(c)
    seam = {k-1, k, k+1}
    bdry = {j for j in range(n) if j <= 3 or j >= n-3} - seam
    visited = {c}; queue = [(c, [])]
    while queue:
        cfg, path = queue.pop(0)
        if fc(cfg) == n:
            return cfg, path
        for j in sorted(bdry):
            d = move(cfg, j)
            if d is not None and d not in visited:
                visited.add(d)
                queue.append((d, path + [j]))
    return None, None

max_len = 0
for n in [10, 11, 12, 13, 14, 15]:
    for start in range(3):
        for v0 in range(2):
            for vn in range(2):
                c = [0]*n; c[0] = v0; c[n-1] = vn
                for j in range(1, n-1): c[j] = (start + j) % 3
                c = tuple(c)
                ok = all(c[j] != c[j-1] and c[j] != c[j+1] for j in range(4, n-3))
                if not ok: continue

                k = 5
                if k + 6 > n: continue

                w, path = boundary_bfs(c, k)
                if w is None:
                    print(f"NO PATH: n={n}, c={c}")
                else:
                    if len(path) > max_len:
                        max_len = len(path)
                        print(f"  New max: n={n}, start={start}, v0={v0}, vn={vn}, "
                              f"len={len(path)}, path={path}")

print(f"\nMax boundary path length to all-distinct: {max_len}")
