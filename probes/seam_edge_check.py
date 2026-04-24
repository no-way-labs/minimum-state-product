"""Check: for k = n-5 (seam touching right boundary),
   does removing a seam step at k+1 = n-4 ever produce a path with lower fc?

   For each n and no-copy period-3 config c at deep positions:
   1. Enumerate all TP-reachable w from c
   2. Check if max over SA-reachable ≥ max over all TP-reachable
"""

def cup2M(n, j):
    if j == 0: return 2
    if j == n-1: return 2
    return 3

def fb(a, b):
    return 1 if a != b else 0

def fc(c):
    n = len(c)
    return sum(fb(c[j], c[(j+1) % n]) for j in range(n))

def cup2OutVal(n, j, L, S, R):
    """CUP-2 output value."""
    if j == 0:
        return (S + 1) % 2  # TBot
    if j == 1:
        # TLow
        if S == 0 and R == 0: return 1
        if S == 0 and R == 1: return 0
        if S == 0 and R == 2: return 0
        if S == 1 and R == 0: return 1
        if S == 1 and R == 1: return 0
        if S == 1 and R == 2: return 2
        if S == 2 and R == 0: return 0
        if S == 2 and R == 1: return 2
        if S == 2 and R == 2: return 1
    if j + 2 == n:
        # THigh
        if L == 0 and S == 0: return 1 if R == 0 else 0
        if L == 0 and S == 1: return 0
        if L == 0 and S == 2: return 0 if R == 0 else 1
        if L == 1 and S == 0: return 1
        if L == 1 and S == 1: return 0 if R == 0 else 2
        if L == 1 and S == 2: return 1
        if L == 2 and S == 0: return 2
        if L == 2 and S == 1: return 2 if R == 0 else 0
        if L == 2 and S == 2: return 0 if R == 0 else 2
        return S  # fallback
    if j + 1 == n:
        # TTop
        return (S + 1) % 2
    # TMid
    from itertools import product
    # Use the actual TMidVal table
    TMid = {
        (0,0,0):0, (0,0,1):0, (0,0,2):0,
        (0,1,0):0, (0,1,1):0, (0,1,2):0,
        (0,2,0):0, (0,2,1):0, (0,2,2):0,
        (1,0,0):1, (1,0,1):1, (1,0,2):1,
        (1,1,0):1, (1,1,1):1, (1,1,2):1,
        (1,2,0):1, (1,2,1):1, (1,2,2):1,
        (2,0,0):2, (2,0,1):2, (2,0,2):2,
        (2,1,0):1, (2,1,1):0, (2,1,2):2,
        (2,2,0):0, (2,2,1):2, (2,2,2):2,
    }
    return TMid.get((L, S, R), S)

def move(c, j):
    n = len(c)
    L = c[(j-1) % n]
    S = c[j]
    R = c[(j+1) % n]
    out = cup2OutVal(n, j, L, S, R)
    if out == S:
        return None  # not privileged
    c2 = list(c)
    c2[j] = out
    return tuple(c2)

def tp_reachable(c):
    """BFS for TP-reachable configs (bad + TP-preserving)."""
    n = len(c)
    visited = {c}
    queue = [c]
    while queue:
        cfg = queue.pop(0)
        for j in range(n):
            d = move(cfg, j)
            if d is not None and d not in visited:
                visited.add(d)
                queue.append(d)
    return visited

def sa_reachable(c, k):
    """BFS for seam-avoiding reachable."""
    n = len(c)
    seam = {k-1, k, k+1}
    visited = {c}
    queue = [c]
    while queue:
        cfg = queue.pop(0)
        for j in range(n):
            if j in seam:
                continue
            d = move(cfg, j)
            if d is not None and d not in visited:
                visited.add(d)
                queue.append(d)
    return visited

# Check for n = 10, k = 5 (k = n-5 edge case)
n = 10
k = 5

# Generate no-copy period-3 configs
violations = 0
checked = 0
for seed in range(3):
    # Period-3 cycling: 0,1,2,0,1,2,...
    c = [0]*n
    c[0] = 0  # binary
    c[n-1] = 0  # binary
    for j in range(1, n-1):
        c[j] = (seed + j) % 3
    c = tuple(c)

    # Check noDeepCopyPair
    has_copy = False
    for j in range(4, n-3):
        if c[j] == c[j-1] or c[j] == c[j+1]:
            has_copy = True
            break
    if has_copy:
        continue

    # Check cycling at k
    if c[k-1] == c[k+1]:
        continue

    checked += 1
    tp = tp_reachable(c)
    sa = sa_reachable(c, k)

    phi_full = max(fc(w) for w in tp)
    max_sa = max(fc(w) for w in sa)

    if phi_full > max_sa:
        violations += 1
        print(f"VIOLATION: c={c}, PhiFull={phi_full}, max_SA={max_sa}")
    else:
        pass  # print(f"OK: c={c}, PhiFull={phi_full}, max_SA={max_sa}")

print(f"\nn={n}, k={k}: checked {checked} configs, {violations} violations")

# Also check n=11, k=6 (k = n-5 edge case)
n = 11
k = 6
violations2 = 0
checked2 = 0
for seed in range(3):
    c = [0]*n
    c[0] = 0
    c[n-1] = 0
    for j in range(1, n-1):
        c[j] = (seed + j) % 3
    c = tuple(c)
    has_copy = False
    for j in range(4, n-3):
        if c[j] == c[j-1] or c[j] == c[j+1]:
            has_copy = True; break
    if has_copy: continue
    if c[k-1] == c[k+1]: continue
    checked2 += 1
    tp = tp_reachable(c)
    sa = sa_reachable(c, k)
    phi_full = max(fc(w) for w in tp)
    max_sa = max(fc(w) for w in sa)
    if phi_full > max_sa:
        violations2 += 1
        print(f"VIOLATION: n={n}, c={c}, PhiFull={phi_full}, max_SA={max_sa}")

print(f"n={n}, k={k}: checked {checked2} configs, {violations2} violations")
