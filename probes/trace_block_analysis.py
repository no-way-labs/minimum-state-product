"""Analyze the trace block: seam step + downstream non-seam steps until stabilization.

For a seam step at p in {k-1, k, k+1}:
- Changes c(p) to TMidVal(c(p-1), c(p), c(p+1)) = copies LEFT (for TpMidTriple no-copy)
- The changed c(p) is the LEFT input for position p+1
- If p+1 fires (TpMidTriple, privileged): copies LEFT = new c(p). Changes c(p+1).
- The changed c(p+1) is the LEFT input for p+2.
- Continue until stabilization: the cascade stops when the next position is not privileged
  (TMidVal(L,S,R) = S, i.e., LEFT = SELF or not TpMidTriple).

The TRACE BLOCK = {seam step at p, cascade at p+1, cascade at p+2, ...}
ends when the cascade stops.

For the SA replacement: skip all steps in the block. The outside-window state is unchanged.
The fc comparison: block fc vs original fc on the affected window.

Let me compute the trace block for each TpMidTriple seam step.
"""

TMid = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):0,(0,1,2):0,
        (0,2,0):0,(0,2,1):0,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,
        (1,1,0):1,(1,1,1):1,(1,1,2):1,(1,2,0):1,(1,2,1):1,(1,2,2):1,
        (2,0,0):2,(2,0,1):2,(2,0,2):2,(2,1,0):1,(2,1,1):0,(2,1,2):2,
        (2,2,0):0,(2,2,1):2,(2,2,2):2}
TpMidTriples = {(0,1,0),(0,1,2),(0,2,2),(1,0,0),(1,0,1),(1,0,2),(1,1,2)}

def TMidVal(L, S, R): return TMid[(L, S, R)]
def fb(a, b): return 1 if a != b else 0
def is_priv(L, S, R): return TMidVal(L, S, R) != S

# For a seam step at position p in a no-copy strip:
# Local window starts at p-1 (the LEFT of p) and extends rightward.
# We need values at p-1, p, p+1, p+2, p+3, ... until cascade stops.
# Constraint: consecutive values are distinct (no-copy strip).

print("=== Trace block analysis ===")
print("For each initial no-copy strip pattern, simulate the seam step + cascade.")
print("Then compare: fc of block endpoint vs fc of 'skip all' (original).\n")

# We need enough positions. Let's use 7 positions: p-1, p, p+1, p+2, p+3, p+4, p+5
# Values: v0, v1, v2, v3, v4, v5, v6 (all adjacent distinct)
# Seam step at position 1 (= p): triple (v0, v1, v2) must be TpMidTriple.

max_cascade_len = 0
all_ok = True

for v0 in range(3):
    for v1 in range(3):
        if v1 == v0: continue
        for v2 in range(3):
            if v2 == v1: continue
            for v3 in range(3):
                if v3 == v2: continue
                for v4 in range(3):
                    if v4 == v3: continue
                    for v5 in range(3):
                        if v5 == v4: continue
                        for v6 in range(3):
                            if v6 == v5: continue
                            if (v0, v1, v2) not in TpMidTriples:
                                continue

                            vals_orig = [v0, v1, v2, v3, v4, v5, v6]
                            vals = list(vals_orig)

                            # Seam step at position 1: output = TMidVal(v0, v1, v2)
                            out = TMidVal(v0, v1, v2)
                            vals[1] = out
                            cascade_len = 1  # the seam step itself

                            # Cascade: check p+1 = position 2
                            for pos in range(2, 6):
                                L, S, R = vals[pos-1], vals[pos], vals[pos+1]
                                if (L, S, R) in TpMidTriples and is_priv(L, S, R):
                                    vals[pos] = TMidVal(L, S, R)
                                    cascade_len += 1
                                else:
                                    break

                            max_cascade_len = max(max_cascade_len, cascade_len)

                            # fb on the AFFECTED window: positions 0 to cascade endpoint + 1
                            # affected positions: 1 to 1+cascade_len-1 (values changed)
                            # affected edges: 0 to 1+cascade_len-1 (edges reading changed values)
                            end_pos = min(1 + cascade_len, 6)

                            fb_orig = sum(fb(vals_orig[i], vals_orig[i+1]) for i in range(end_pos))
                            fb_after = sum(fb(vals[i], vals[i+1]) for i in range(end_pos))

                            # SA replacement: skip all. fb = fb_orig.
                            if fb_orig < fb_after:
                                all_ok = False
                                print(f"VIOLATION: orig={vals_orig}, after={vals}, "
                                      f"fb_orig={fb_orig}, fb_after={fb_after}, cascade={cascade_len}")

print(f"\nMax cascade length: {max_cascade_len}")
print(f"All OK (skip dominates): {all_ok}")

# Also check: what is the max cascade length? If bounded, the trace block is bounded.
print(f"\n--- Cascade length distribution ---")
cascade_dist = {}
for v0 in range(3):
    for v1 in range(3):
        if v1 == v0: continue
        for v2 in range(3):
            if v2 == v1: continue
            for v3 in range(3):
                if v3 == v2: continue
                for v4 in range(3):
                    if v4 == v3: continue
                    for v5 in range(3):
                        if v5 == v4: continue
                        for v6 in range(3):
                            if v6 == v5: continue
                            if (v0, v1, v2) not in TpMidTriples: continue
                            vals = [v0, v1, v2, v3, v4, v5, v6]
                            out = TMidVal(v0, v1, v2)
                            vals[1] = out
                            clen = 1
                            for pos in range(2, 6):
                                L, S, R = vals[pos-1], vals[pos], vals[pos+1]
                                if (L, S, R) in TpMidTriples and is_priv(L, S, R):
                                    vals[pos] = TMidVal(L, S, R)
                                    clen += 1
                                else: break
                            cascade_dist[clen] = cascade_dist.get(clen, 0) + 1
for k in sorted(cascade_dist):
    print(f"  cascade length {k}: {cascade_dist[k]} patterns")
