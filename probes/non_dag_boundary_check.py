"""Check: does any boundary 6-tuple transition fall outside the 617-edge DAG?

If NO non-DAG transitions exist at any size, then PhiFull is scaffolding
for a case that never fires, and the proof simplifies dramatically.
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_final_verify import T_bot, T_low, T_mid, T_high, T_top
from itertools import product as cartesian

def build_system(n):
    ms = [2] + [3]*(n-2) + [2]
    tables = [None]*n
    tables[0] = T_bot
    tables[1] = T_low
    for i in range(2, n-2):
        tables[i] = T_mid
    tables[n-2] = T_high
    tables[n-1] = T_top
    return ms, tables

def move(ms, tables, c, i):
    n = len(ms)
    L, S, R = c[(i-1)%n], c[i], c[(i+1)%n]
    new = tables[i][(L,S,R)]
    if new == S:
        return None
    return c[:i] + (new,) + c[i+1:]

def boundary6(c, n):
    return (c[0], c[1], c[2], c[n-3], c[n-2], c[n-1])

def encode6(b):
    return b[0] + 2*b[1] + 6*b[2] + 18*b[3] + 54*b[4] + 162*b[5]

start = time.time()
all_edges = set()

for n in range(5, 16):
    ms, tables = build_system(n)
    edges_n = set()

    for c in cartesian(*[range(m) for m in ms]):
        for i in range(n):
            d = move(ms, tables, c, i)
            if d is None:
                continue
            bs = boundary6(c, n)
            bd = boundary6(d, n)
            if bs != bd:
                edges_n.add((encode6(bd), encode6(bs)))

    new = edges_n - all_edges
    all_edges |= edges_n
    print(f"n={n:2d}: {len(edges_n):4d} boundary edges, {len(new):3d} new, total={len(all_edges)}")

print(f"\nTotal unique boundary edges across n=5..15: {len(all_edges)}")
print(f"Is this exactly 617? {'YES' if len(all_edges) == 617 else 'NO — ' + str(len(all_edges))}")
print(f"Time: {time.time()-start:.1f}s")

# Now check: among BAD steps (both src and dst off good cycle), how many boundary edges?
print("\n--- Filtering to BAD steps only ---")

def build_good_cycle(n, ms, tables):
    def cup2_cycle_val(n, t, j):
        if t < n:
            return 0 if j <= t else (2 if j < n-1 else 1)
        elif t < 2*n-2:
            m = 2*n - 2 - t
            return 0 if j < m else (2 if j < n-1 else 1)
        elif t == 2*n-2:
            return 1 if j == 0 else (2 if j < n-1 else 1)
        else:
            k = t - (2*n-2)
            if k == 0:
                return 1 if j == 0 else (2 if j < n-1 else 1)
            return 0 if j < k else (2 if j < n-1 else 1)
    cycle_len = 3*n - 2
    return {tuple(cup2_cycle_val(n, t, j) for j in range(n)) for t in range(cycle_len)}

all_bad_edges = set()
the_617 = None

for n in range(8, 14):
    ms, tables = build_system(n)
    good = build_good_cycle(n, ms, tables)
    bad_edges_n = set()
    
    for c in cartesian(*[range(m) for m in ms]):
        if c in good:
            continue  # skip good-cycle configs
        for i in range(n):
            d = move(ms, tables, c, i)
            if d is None:
                continue
            if d in good:
                continue  # dst on good cycle = not a bad step
            bs = boundary6(c, n)
            bd = boundary6(d, n)
            if bs != bd:
                bad_edges_n.add((encode6(bd), encode6(bs)))
    
    new = bad_edges_n - all_bad_edges
    all_bad_edges |= bad_edges_n
    if n == 9 and the_617 is None:
        the_617 = bad_edges_n.copy()
    print(f"n={n:2d}: {len(bad_edges_n):4d} bad boundary edges, {len(new):3d} new, total={len(all_bad_edges)}")

print(f"\nTotal bad boundary edges n=8..13: {len(all_bad_edges)}")
if the_617:
    print(f"At n=9: {len(the_617)} bad boundary edges")
    extras = all_bad_edges - the_617
    print(f"Edges at n>9 not at n=9: {len(extras)}")
