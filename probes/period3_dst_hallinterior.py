"""Check: in the period3_noCopy_nIndep context, does dst satisfy hallInterior?
dst is the target of a TP-bad boundary-changing step from src.
Both have noDeepCopyPair. dst has a cycling site (hasCyclingSite').
Does dst always have all interior edges distinct?"""

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
        if c[k-1] != c[k+1]:
            return True
    return False

def has_hallinterior(c, n):
    return all(c[j] != c[(j+1)] for j in range(1, n-1))

def boundary6(c, n):
    return (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])

# For n=11: find all (src, dst) pairs that are TP-bad boundary-changing steps
# where dst has noDeepCopyPair and hasCyclingSite'
n = 11
from itertools import product

# Generate all configs (expensive for n=11, so just check period-3 starts)
for start in range(3):
    c0 = [0]*n; c0[0] = 0; c0[n-1] = 0
    for j in range(1, n-1): c0[j] = (start + j) % 3
    c0 = tuple(c0)

    # TP-reachable from c0
    tp = {c0}; queue = [c0]
    while queue:
        cfg = queue.pop(0)
        for j in range(n):
            d = move(cfg, j)
            if d is not None and d not in tp:
                tp.add(d); queue.append(d)

    # Find all TP-bad steps src -> dst where dst has noDeepCopyPair + hasCyclingSite'
    # and boundary changes (boundary6(dst) != boundary6(src))
    fail_count = 0
    check_count = 0
    for src in tp:
        for j in range(n):
            dst = move(src, j)
            if dst is None: continue
            if not has_nocopy(dst, n): continue
            if not has_cycling(dst, n): continue
            if boundary6(dst, n) == boundary6(src, n): continue  # boundary-changing
            check_count += 1
            if not has_hallinterior(dst, n):
                fail_count += 1
                if fail_count <= 2:
                    bad = [(j, j+1) for j in range(1, n-1) if dst[j] == dst[j+1]]
                    print(f"  FAIL: dst={dst}, bad={bad}, mover={j}")

    print(f"n={n} start={start}: checked {check_count} period3-dst steps, hallInterior fails: {fail_count}")
