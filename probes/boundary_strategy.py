"""Find a simple deterministic strategy for reaching fc=n.
Strategy: if c(0) equals any neighbor, flip c(0). Then if c(n-1) equals any neighbor, flip c(n-1).
Then check if fc=n. If not, try additional steps at positions 1 or 2."""

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

# Strategy: greedily flip binary endpoints that have copy pairs
def greedy_fix(c):
    n = len(c)
    path = []
    cfg = c
    # Step 1: if c(n-1) = c(n-2) or c(n-1) = c(0), flip c(n-1)
    if cfg[n-1] == cfg[n-2] or cfg[n-1] == cfg[0]:
        d = move(cfg, n-1)
        if d is not None:
            path.append(n-1)
            cfg = d
    # Step 2: if c(0) = c(1) or c(0) = c(n-1), flip c(0)
    if cfg[0] == cfg[1] or cfg[0] == cfg[n-1]:
        d = move(cfg, 0)
        if d is not None:
            path.append(0)
            cfg = d
    if fc(cfg) == n:
        return cfg, path
    # Step 3: try firing at position 1 (TLow)
    d = move(cfg, 1)
    if d is not None:
        path2 = path + [1]
        if fc(d) == n:
            return d, path2
        # Step 4: try firing at position 2 after 1
        e = move(d, 2)
        if e is not None:
            path3 = path2 + [2]
            if fc(e) == n:
                return e, path3
    # Try position 2 first
    d = move(cfg, 2)
    if d is not None:
        path2 = path + [2]
        if fc(d) == n:
            return d, path2
        e = move(d, 1)
        if e is not None:
            path3 = path2 + [1]
            if fc(e) == n:
                return e, path3
    return None, None

# Test
for n in range(10, 20):
    for start in range(3):
        for v0 in range(2):
            for vn in range(2):
                c = [0]*n; c[0] = v0; c[n-1] = vn
                for j in range(1, n-1): c[j] = (start + j) % 3
                c = tuple(c)
                ok = all(c[j] != c[j-1] and c[j] != c[j+1] for j in range(4, n-3))
                if not ok: continue
                w, path = greedy_fix(c)
                if w is None:
                    print(f"FAILED: n={n}, c={c[:5]}...{c[-3:]}, fc={fc(c)}")
                elif len(path) > 0:
                    pass  # OK

print("Done. If no FAILED: greedy strategy works for all cases.")
