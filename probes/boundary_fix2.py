"""Universal check: can a single step at 0 or n-1 always reach fc=n?"""

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

for n in range(10, 20):
    for start in range(3):
        c = [0]*n; c[0] = 0; c[n-1] = 0
        for j in range(1, n-1): c[j] = (start + j) % 3
        c = tuple(c)
        ok = all(c[j] != c[j-1] and c[j] != c[j+1] for j in range(4, n-3))
        if not ok: continue

        if fc(c) == n:
            # Already all-distinct. Use c itself (0 steps).
            continue

        # Try single step at 0
        d0 = move(c, 0)
        # Try single step at n-1
        dn = move(c, n-1)
        # Try both
        found = False
        if d0 is not None and fc(d0) == n:
            found = True
        elif dn is not None and fc(dn) == n:
            found = True
        elif d0 is not None:
            d00 = move(d0, n-1)
            if d00 is not None and fc(d00) == n:
                found = True
        if not found and dn is not None:
            dn0 = move(dn, 0)
            if dn0 is not None and fc(dn0) == n:
                found = True

        if not found:
            print(f"FAILED: n={n}, c={c}, fc={fc(c)}")
        else:
            pass  # print(f"OK: n={n}, start={start}")

    # Also check c with c[n-1] = 1
    for start in range(3):
        c = [0]*n; c[0] = 0; c[n-1] = 1
        for j in range(1, n-1): c[j] = (start + j) % 3
        c = tuple(c)
        ok = all(c[j] != c[j-1] and c[j] != c[j+1] for j in range(4, n-3))
        if not ok: continue
        if fc(c) == n: continue
        d0 = move(c, 0)
        dn = move(c, n-1)
        found = False
        if d0 is not None and fc(d0) == n: found = True
        elif dn is not None and fc(dn) == n: found = True
        elif d0 is not None:
            d00 = move(d0, n-1)
            if d00 is not None and fc(d00) == n: found = True
        if not found and dn is not None:
            dn0 = move(dn, 0)
            if dn0 is not None and fc(dn0) == n: found = True
        if not found:
            print(f"FAILED: n={n}, c={c}, fc={fc(c)}")

print("Done. If no FAILED: ≤ 2 boundary steps at {0, n-1} always reach fc=n.")
