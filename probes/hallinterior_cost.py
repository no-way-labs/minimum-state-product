"""Check: does noDeepCopyPair + hasCyclingSite' imply hallInterior?
hallInterior: for all j with 1 <= j and j+1 < n: c(j) != c(j+1).
noDeepCopyPair: for all k with 4 <= k and k+4 <= n: c(k) != c(k-1) and c(k) != c(k+1).
hasCyclingSite': exists k with 5 <= k, k+5 <= n, c(k-1) != c(k+1).

The gap: noDeepCopyPair covers positions 4..n-4. hallInterior covers positions 1..n-2.
The uncovered positions: 1, 2, 3 and n-3.

For position 3: noDeepCopyPair at k=4 gives c(4) != c(3). So c(3) != c(4). ✓ for edge (3,4).
But edge (2,3): c(2) != c(3)? Not from noDeepCopyPair. k=3 needs 4 <= 3: FALSE.
Edge (1,2): c(1) != c(2)? k=2 needs 4 <= 2: FALSE.

For position n-3: noDeepCopyPair at k=n-4 gives c(n-4) != c(n-3). ✓ for edge (n-4, n-3).
But edge (n-3, n-2): c(n-3) != c(n-2)? k=n-3 needs (n-3)+4 <= n: 1 <= 0: FALSE for any n.

So: noDeepCopyPair does NOT cover edges (1,2), (2,3), (n-3,n-2).
hasCyclingSite' just gives one cycling site, not all-interior-distinct.

Question: in the actual configs that appear in period3_noCopy_nIndep, do edges (1,2), (2,3), (n-3,n-2) always have c(j) != c(j+1)?

Let's check: for configs reachable from period-3 starting configs via TP-bad steps,
are edges (1,2), (2,3), (n-3,n-2) always distinct?
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

def move(c, j):
    n = len(c)
    L, S, R = c[(j-1)%n], c[j], c[(j+1)%n]
    out = cup2OutVal(n, j, L, S, R)
    if out == S: return None
    return tuple(c[i] if i != j else out for i in range(n))

def has_nocopy(c, n):
    for j in range(4, n-3):
        if c[j] == c[j-1] or c[j] == c[j+1]:
            return False
    return True

def has_hallinterior(c, n):
    for j in range(1, n-1):
        if c[j] == c[(j+1) % n]:
            return False
    return True

# Check: among ALL TP-reachable configs from period-3 starts with noDeepCopyPair,
# how many violate hallInterior?
for n in [11, 12]:
    k = 5
    for start in range(3):
        c = [0]*n; c[0] = 0; c[n-1] = 0
        for j in range(1, n-1): c[j] = (start + j) % 3
        c = tuple(c)
        if not has_nocopy(c, n): continue

        # TP-reachable
        tp = {c}; queue = [c]
        while queue:
            cfg = queue.pop(0)
            for j in range(n):
                d = move(cfg, j)
                if d is not None and d not in tp:
                    tp.add(d); queue.append(d)

        # Check hallInterior for configs with noDeepCopyPair
        nocopy_count = 0
        nocopy_hall_fail = 0
        for w in tp:
            if has_nocopy(w, n):
                nocopy_count += 1
                if not has_hallinterior(w, n):
                    nocopy_hall_fail += 1
                    if nocopy_hall_fail <= 2:
                        bad_edges = [(j, j+1) for j in range(1, n-1) if w[j] == w[(j+1)%n]]
                        print(f"  n={n} FAIL: w={w}, bad_interior_edges={bad_edges}")

        print(f"n={n} start={start}: |TP|={len(tp)}, |noDeepCopyPair|={nocopy_count}, "
              f"|hallInterior fails|={nocopy_hall_fail}")
