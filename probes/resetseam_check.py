"""Check resetSeam_fc_ge: is fc(resetSeam(c,w)) >= fc(w) for all w TP-reachable from c?"""

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
def fc(c):
    n = len(c)
    return sum(fb(c[j], c[(j+1) % n]) for j in range(n))

def move(c, j):
    n = len(c)
    L, S, R = c[(j-1)%n], c[j], c[(j+1)%n]
    out = cup2OutVal(n, j, L, S, R)
    if out == S: return None
    return tuple(c[i] if i != j else out for i in range(n))

def tp_reachable(c):
    visited = {c}
    queue = [c]
    while queue:
        cfg = queue.pop(0)
        for j in range(len(cfg)):
            d = move(cfg, j)
            if d is not None and d not in visited:
                visited.add(d); queue.append(d)
    return visited

def resetSeam(c, w, k):
    n = len(c)
    seam = {k-1, k, k+1}
    return tuple(c[j] if j in seam else w[j] for j in range(n))

# Check for n=11, k=5 (far case: k+6=11 <= n)
n = 11
k = 5
from itertools import product
violations = 0
checked = 0
for start in range(3):
    c = [0]*n
    c[0] = 0; c[n-1] = 0
    for j in range(1, n-1):
        c[j] = (start + j) % 3
    c = tuple(c)
    # Check noDeepCopyPair
    ok = True
    for j in range(4, n-3):
        if c[j] == c[j-1] or c[j] == c[j+1]: ok = False; break
    if not ok: continue
    if c[k-1] == c[k+1]: continue
    checked += 1
    for w in tp_reachable(c):
        rw = resetSeam(c, w, k)
        if fc(rw) < fc(w):
            violations += 1
            if violations <= 3:
                print(f"VIOLATION: c={c}, w={w}, resetSeam={rw}, fc(rw)={fc(rw)}, fc(w)={fc(w)}")
                # Show which edges differ
                for j in range(n):
                    fb_rw = fb(rw[j], rw[(j+1)%n])
                    fb_w = fb(w[j], w[(j+1)%n])
                    if fb_rw != fb_w:
                        print(f"  edge {j}-{(j+1)%n}: rw fb={fb_rw} ({rw[j]},{rw[(j+1)%n]}), w fb={fb_w} ({w[j]},{w[(j+1)%n]})")

print(f"\nn={n}, k={k}: checked {checked} configs, {violations} total violations across all reachable")
