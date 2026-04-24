"""For each period-3 no-copy config c, find the minimal boundary step sequence
that makes all adjacent pairs distinct (fc = n).

c(0) has modulus 2 (values 0,1). c(n-1) has modulus 2 (values 0,1).
c(1)...c(n-2) have modulus 3 (values 0,1,2).

Deep strip c(3)...c(n-4) is period-3 cycling (all adjacent distinct).
Copy pairs can only be at:
  - edge (n-1, 0): fb(c(n-1), c(0))
  - edge (0, 1): fb(c(0), c(1))
  - edge (n-2, n-1): fb(c(n-2), c(n-1))
  - edge (1, 2): fb(c(1), c(2))  -- c(2) is ternary, might equal c(1)
  - edge (n-3, n-2): fb(c(n-3), c(n-2))  -- might have copy pair

Wait, noDeepCopyPair requires adjacent distinct at positions 4..n-4.
But positions 1, 2, 3 and n-3, n-2 are NOT covered by noDeepCopyPair.
So copy pairs CAN exist at edges (0,1), (1,2), (2,3), (n-3,n-2), (n-2,n-1), (n-1,0).
"""

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

n = 11
k = 5
seam = {k-1, k, k+1}

for start in range(3):
    c = [0]*n; c[0] = 0; c[n-1] = 0
    for j in range(1, n-1): c[j] = (start + j) % 3
    c = tuple(c)

    print(f"\nc = {c}")
    print(f"  fc = {fc(c)}, n = {n}")

    # Show which edges have fb = 0
    for j in range(n):
        if fb(c[j], c[(j+1)%n]) == 0:
            print(f"  edge ({j},{(j+1)%n}): c[{j}]={c[j]}, c[{(j+1)%n}]={c[(j+1)%n]} fb=0")

    # BFS: find shortest SA path to an all-distinct config
    sa = {c}; queue = [(c, [])]
    found = None
    while queue and not found:
        cfg, path = queue.pop(0)
        if fc(cfg) == n:
            found = (cfg, path)
            break
        for j in range(n):
            if j in seam: continue
            d = move(cfg, j)
            if d is not None and d not in sa:
                sa.add(d)
                queue.append((d, path + [j]))

    if found:
        w, path = found
        print(f"  SA path to all-distinct: {path} (length {len(path)})")
        print(f"  w = {w}, fc = {fc(w)}")
        # Check: only boundary positions used?
        only_boundary = all(p <= 3 or p >= n-3 for p in path)
        print(f"  Only boundary movers: {only_boundary}")
        print(f"  Mover positions: {path}")
