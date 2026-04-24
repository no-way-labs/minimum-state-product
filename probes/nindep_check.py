"""Check n-independence of boundary6 transitions for CUP-2 system.

For n=10,11,12: enumerate TP-reachable configs from period-3 starts,
find all boundary6 transitions where dst has noDeepCopyPair + hasCyclingSite'
and boundary6 changes."""

from collections import deque

# ── CUP-2 transition function ──────────────────────────────────────────

def cup2OutVal(n, j, L, S, R):
    if j == 0:
        return (S + 1) % 2
    if j == 1:
        tbl = {(0,0):1,(0,1):0,(0,2):0,(1,0):1,(1,1):0,(1,2):2,(2,0):0,(2,1):2,(2,2):1}
        return tbl.get((S, R), S)
    if j + 2 == n:
        tbl = {(0,0,0):1,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):1,
               (1,0,0):1,(1,0,1):1,(1,1,0):0,(1,1,1):2,(1,2,0):1,(1,2,1):1,
               (2,0,0):2,(2,0,1):2,(2,1,0):2,(2,1,1):0,(2,2,0):0,(2,2,1):2}
        return tbl.get((L, S, R), S)
    if j + 1 == n:
        return (S + 1) % 2
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
    if out == S:
        return None
    return tuple(c[i] if i != j else out for i in range(n))

def fb(a, b):
    return 1 if a != b else 0

def fc_val(c):
    n = len(c)
    return sum(fb(c[j], c[(j+1) % n]) for j in range(n))

# ── Predicates ──────────────────────────────────────────────────────────

def boundary6(c, n):
    return (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])

def noDeepCopyPair(c, n):
    """For all k with 4 <= k and k+4 <= n: c[k] != c[k-1] and c[k] != c[k+1]"""
    for k in range(4, n - 3):  # k+4 <= n means k <= n-4, but k+3 <= n-1 for c[k+1]
        if c[k] == c[k-1] or c[k] == c[k+1]:
            return False
    return True

def hasCyclingSite(c, n):
    """Exists k with 5 <= k and k+5 <= n and c[k-1] != c[k+1]"""
    for k in range(5, n - 4):  # k+5 <= n means k <= n-5
        if c[k-1] != c[k+1]:
            return True
    return False

# ── TP-preserving reachability ──────────────────────────────────────────

def tp_reachable(starts):
    """BFS from start configs, only following moves that don't decrease fc."""
    visited = set(starts)
    queue = deque(starts)
    while queue:
        cfg = queue.popleft()
        n = len(cfg)
        f0 = fc_val(cfg)
        for j in range(n):
            d = move(cfg, j)
            if d is not None and d not in visited:
                # TP-preserving: fc doesn't drop
                if fc_val(d) >= f0:
                    visited.add(d)
                    queue.append(d)
    return visited

def all_reachable(starts):
    """BFS from start configs, following ALL moves (no TP restriction)."""
    visited = set(starts)
    queue = deque(starts)
    while queue:
        cfg = queue.popleft()
        n = len(cfg)
        for j in range(n):
            d = move(cfg, j)
            if d is not None and d not in visited:
                visited.add(d)
                queue.append(d)
    return visited

# ── Period-3 starting configs ──────────────────────────────────────────

def period3_starts(n):
    starts = []
    for start in range(3):
        c = [0] * n
        c[0] = 0
        c[n-1] = 0
        for j in range(1, n-1):
            c[j] = (start + j) % 3
        starts.append(tuple(c))
    return starts

# ── Main analysis ──────────────────────────────────────────────────────

def analyze(n, use_tp=True):
    starts = period3_starts(n)
    print(f"\n{'='*60}")
    print(f"n={n}, {'TP-preserving' if use_tp else 'ALL reachable'}")
    print(f"Starting configs: {len(starts)}")
    for s in starts:
        print(f"  {s}  fc={fc_val(s)}")

    if use_tp:
        reached = tp_reachable(starts)
    else:
        reached = all_reachable(starts)
    print(f"Reachable configs: {len(reached)}")

    # Find boundary transitions
    bdry_transitions = set()
    dst_count = 0

    for src in reached:
        b_src = boundary6(src, n)
        for j in range(n):
            dst = move(src, j)
            if dst is None:
                continue
            if not noDeepCopyPair(dst, n):
                continue
            if not hasCyclingSite(dst, n):
                continue
            b_dst = boundary6(dst, n)
            if b_src == b_dst:
                continue
            bdry_transitions.add((b_src, b_dst))
            dst_count += 1

    print(f"Boundary-changing dst configs (noDeepCopy + hasCycling): {dst_count}")
    print(f"Unique boundary transitions: {len(bdry_transitions)}")

    if len(bdry_transitions) <= 200:
        for t in sorted(bdry_transitions):
            print(f"  {t[0]} -> {t[1]}")

    return bdry_transitions

# ── Run for n=10, 11, 12 ──────────────────────────────────────────────

results_tp = {}
results_all = {}

for n in [10, 11, 12]:
    results_tp[n] = analyze(n, use_tp=True)
    results_all[n] = analyze(n, use_tp=False)

# ── Comparison ──────────────────────────────────────────────────────────

print(f"\n{'='*60}")
print("COMPARISON (TP-preserving)")
print(f"n=10: {len(results_tp[10])} transitions")
print(f"n=11: {len(results_tp[11])} transitions")
print(f"n=12: {len(results_tp[12])} transitions")

s10 = results_tp[10]
s11 = results_tp[11]
s12 = results_tp[12]

print(f"\nn=11 subset of n=10? {s11.issubset(s10)}")
if not s11.issubset(s10):
    diff = s11 - s10
    print(f"  Extra in n=11: {len(diff)}")
    for t in sorted(diff)[:20]:
        print(f"    {t[0]} -> {t[1]}")

print(f"n=12 subset of n=10? {s12.issubset(s10)}")
if not s12.issubset(s10):
    diff = s12 - s10
    print(f"  Extra in n=12: {len(diff)}")
    for t in sorted(diff)[:20]:
        print(f"    {t[0]} -> {t[1]}")

print(f"\nn=10 == n=11? {s10 == s11}")
print(f"n=10 == n=12? {s10 == s12}")
print(f"n=11 == n=12? {s11 == s12}")

# Same for ALL reachable
print(f"\n{'='*60}")
print("COMPARISON (ALL reachable, no TP restriction)")
a10 = results_all[10]
a11 = results_all[11]
a12 = results_all[12]
print(f"n=10: {len(a10)} transitions")
print(f"n=11: {len(a11)} transitions")
print(f"n=12: {len(a12)} transitions")
print(f"n=10 == n=11? {a10 == a11}")
print(f"n=10 == n=12? {a10 == a12}")
print(f"n=11 == n=12? {a11 == a12}")

if not a11.issubset(a10):
    diff = a11 - a10
    print(f"  Extra in ALL n=11 vs n=10: {len(diff)}")
    for t in sorted(diff)[:20]:
        print(f"    {t[0]} -> {t[1]}")

# TP vs ALL comparison
print(f"\n{'='*60}")
print("TP vs ALL comparison")
for n in [10, 11, 12]:
    tp = results_tp[n]
    al = results_all[n]
    print(f"n={n}: TP={len(tp)}, ALL={len(al)}, TP==ALL? {tp == al}")
    if tp != al:
        print(f"  Extra in ALL: {len(al - tp)}")
        for t in sorted(al - tp)[:10]:
            print(f"    {t[0]} -> {t[1]}")
        print(f"  Extra in TP: {len(tp - al)}")
