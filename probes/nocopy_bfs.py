"""For ALL noDeepCopyPair configs (not just period-3), check if boundary SA steps reach fc=n."""

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

from itertools import product

n = 10  # small enough to enumerate ALL configs
k = 5
seam = {k-1, k, k+1}
bdry = sorted({j for j in range(n) if j <= 3 or j >= n-3} - seam)

# Generate ALL noDeepCopyPair configs
count = 0
fail = 0
for vals in product(range(2), range(3), range(3), range(3), range(3), range(3), range(3), range(3), range(3), range(2)):
    c = vals
    # Check moduli
    if c[0] >= 2 or c[n-1] >= 2: continue
    if any(c[j] >= 3 for j in range(1, n-1)): continue
    # Check noDeepCopyPair: 4 <= k <= n-4, c(k) != c(k-1) and c(k) != c(k+1)
    ok = True
    for j in range(4, n-3):
        if c[j] == c[j-1] or c[j] == c[j+1]:
            ok = False; break
    if not ok: continue
    count += 1

    # BFS with boundary positions only
    visited = {c}; queue = [(c, 0)]
    found = False
    while queue:
        cfg, depth = queue.pop(0)
        if fc(cfg) == n:
            found = True; break
        if depth >= 8: continue
        for j in bdry:
            d = move(cfg, j)
            if d is not None and d not in visited:
                visited.add(d)
                queue.append((d, depth + 1))
    if not found:
        fail += 1
        if fail <= 3:
            print(f"FAIL: c={c}, fc={fc(c)}")
            # Show bad edges
            for j in range(n):
                if fb(c[j], c[(j+1)%n]) == 0:
                    print(f"  edge ({j},{(j+1)%n}): {c[j]}={c[(j+1)%n]}")

print(f"\nn={n}: checked {count} noDeepCopyPair configs, {fail} failures")
