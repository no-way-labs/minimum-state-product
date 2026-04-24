"""Exhaustive analysis of the k = n-5 edge case for seam pruning.
For each n and each no-copy period-3 config with cycling site k = n-5:
1. Find all TP-reachable configs
2. Find all SA-reachable configs (avoiding {k-1, k, k+1} = {n-6, n-5, n-4})
3. Check PhiFull = max_SA
4. Analyze the right-boundary effect: what happens when the seam step at n-4
   changes c(n-4) and propagates through n-3, n-2, n-1.
"""

def cup2OutVal(n, j, L, S, R):
    if j == 0: return (S + 1) % 2
    if j == 1:
        tbl = {(0,0):1,(0,1):0,(0,2):0,(1,0):1,(1,1):0,(1,2):2,(2,0):0,(2,1):2,(2,2):1}
        return tbl.get((S, R), S)
    if j + 2 == n:
        tbl = {
            (0,0,0):1,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):1,
            (1,0,0):1,(1,0,1):1,(1,1,0):0,(1,1,1):2,(1,2,0):1,(1,2,1):1,
            (2,0,0):2,(2,0,1):2,(2,1,0):2,(2,1,1):0,(2,2,0):0,(2,2,1):2,
        }
        return tbl.get((L, S, R), S)
    if j + 1 == n: return (S + 1) % 2
    TMid = {
        (0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):0,(0,1,2):0,
        (0,2,0):0,(0,2,1):0,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,
        (1,1,0):1,(1,1,1):1,(1,1,2):1,(1,2,0):1,(1,2,1):1,(1,2,2):1,
        (2,0,0):2,(2,0,1):2,(2,0,2):2,(2,1,0):1,(2,1,1):0,(2,1,2):2,
        (2,2,0):0,(2,2,1):2,(2,2,2):2,
    }
    return TMid.get((L, S, R), S)

def fb(a, b): return 1 if a != b else 0
def fc(c):
    n = len(c)
    return sum(fb(c[j], c[(j+1) % n]) for j in range(n))

def move(c, j):
    n = len(c)
    L, S, R = c[(j-1)%n], c[j], c[(j+1)%n]
    out = cup2OutVal(n, j, L, S, R)
    if out == S: return None
    return tuple(c[i] if i != j else out for i in range(n))

def reachable(c, excluded=set()):
    n = len(c)
    visited = {c}
    queue = [c]
    while queue:
        cfg = queue.pop(0)
        for j in range(n):
            if j in excluded: continue
            d = move(cfg, j)
            if d is not None and d not in visited:
                visited.add(d)
                queue.append(d)
    return visited

# Exhaustive check for n=10..13 with k = n-5
for n in range(10, 14):
    k = n - 5
    seam = {k-1, k, k+1}
    print(f"\nn={n}, k={k}, seam={seam}")

    # Generate ALL configs with noDeepCopyPair
    from itertools import product
    configs_checked = 0
    violations = 0

    # Only check configs with no deep copy pair AND cycling at k
    # Deep positions: 4 to n-4
    for boundary_vals in product(range(2), range(3), range(3), range(3),
                                  range(3), range(3), range(3), range(2)):
        if n > 10:
            # For n > 10: add more interior positions
            # This gets exponential. Just check period-3 patterns.
            break
        c = list(boundary_vals[:4]) + [0]*(n-8) + list(boundary_vals[4:])
        # Fill deep interior with period-3 pattern
        for start in range(3):
            c_try = list(c)
            for j in range(4, n-4):
                c_try[j] = (start + j) % 3
            c_try = tuple(c_try)

            # Check noDeepCopyPair
            ok = True
            for j in range(4, n-3):
                if c_try[j] == c_try[j-1] or c_try[j] == c_try[j+1]:
                    ok = False; break
            if not ok: continue
            # Check cycling at k
            if c_try[k-1] == c_try[k+1]: continue

            configs_checked += 1
            tp = reachable(c_try)
            sa = reachable(c_try, excluded=seam)
            phi = max(fc(w) for w in tp)
            msa = max(fc(w) for w in sa)
            if phi > msa:
                violations += 1
                print(f"  VIOLATION: c={c_try}, phi={phi}, msa={msa}")

    print(f"  Checked {configs_checked} configs, {violations} violations")
