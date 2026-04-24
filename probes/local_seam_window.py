"""Analyze the exact local window of a seam step.
For a seam step at position p in {k-1, k, k+1}:
  - Changes c(p) to TMidVal(c(p-1), c(p), c(p+1)) = c(p-1) (left copy)
  - Affected frontier bits: fb at p-1 and p
  - Subsequent non-seam steps read c(p) as:
    - RIGHT of p-1 (TMid copies LEFT, irrelevant)
    - LEFT of p+1 (TMid copies LEFT = c(p)_modified, DOES affect output)
  - The cascade at p+1 then copies c(p)_modified, affecting fb at p and p+1
  - Then p+2 reads c(p+1)_modified as LEFT, copies it, etc.

For the local replacement: instead of firing the seam step at p,
DON'T fire it. The seam step cost Δfc ≤ -1. The cascade steps that follow
also each cost Δfc ≤ -1. Total cost of seam + cascade ≥ 2.
If we skip them all: we save ≥ 2 fc on the local window.
But some of those cascade steps might also fire in the SA path
(they're non-seam). So the SA path's cascade costs need to be accounted for.

Let's enumerate all possible local transitions for a seam step at p
in the no-copy regime, and find the optimal SA replacement.
"""

def TMidVal(L, S, R):
    tbl = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):0,(0,1,2):0,
           (0,2,0):0,(0,2,1):0,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,
           (1,1,0):1,(1,1,1):1,(1,1,2):1,(1,2,0):1,(1,2,1):1,(1,2,2):1,
           (2,0,0):2,(2,0,1):2,(2,0,2):2,(2,1,0):1,(2,1,1):0,(2,1,2):2,
           (2,2,0):0,(2,2,1):2,(2,2,2):2}
    return tbl.get((L, S, R), S)

def fb(a, b): return 1 if a != b else 0

# For a seam step at position p in a no-copy regime:
# Local window: positions p-2, p-1, p, p+1, p+2 with values a, b, c, d, e
# No-copy: b ≠ a, b ≠ c, c ≠ b, c ≠ d, d ≠ c, d ≠ e (all adjacent distinct)
# Actually: noDeepCopyPair means c(j) ≠ c(j-1) and c(j) ≠ c(j+1) for deep j.

# For positions {p-2,...,p+2} all deep and no-copy:
# a ≠ b, b ≠ c, c ≠ d, d ≠ e (adjacent distinct in the strip)

# Seam step at p: output = TMidVal(b, c, d). In no-copy (b ≠ c, c ≠ d): output = b (left copy).
# After seam: values become a, b, b, d, e.
# fb changes: fb(a,b)=1→1, fb(b,b)=0 (was fb(b,c)=1), fb(b,d) (was fb(c,d)=1), fb(d,e)=same
# Local fb before: fb(a,b) + fb(b,c) + fb(c,d) + fb(d,e) = 1+1+1+1 = 4
# Local fb after seam: fb(a,b) + fb(b,b) + fb(b,d) + fb(d,e) = 1+0+fb(b,d)+1

# If b ≠ d (period-3: a,b,c are all distinct, d = a in period-3):
#   fb(b,d): b ≠ d if d ≠ b. In period-3: d = a, b ≠ a → fb = 1.
#   After seam: 1+0+1+1 = 3. Loss = 1. ✓

# If b = d (period-2: like a,b,a,b → but that's a copy pair at p and p+1 since c = a = d?
#   No: no-copy means c ≠ b and c ≠ d. If b = d: c ≠ b and c ≠ b. So {c} ∩ {b} = ∅.
#   Third value: a, b, c all in {0,1,2} with b ≠ c. And b = d.
#   After seam: a, b, b, b, e. fb(b,b)=0, fb(b,b)=0. Local fb = 1+0+0+fb(b,e) = 1+fb(b,e).
#   If b ≠ e: 1+1=2. Loss = 2.
#   If b = e: 1+0=1. Loss = 3.

# Now: what about the CASCADE at p+1?
# After seam at p: values = a, b, b, d, e.
# Position p+1: LEFT = b, SELF = d, RIGHT = e.
# If b ≠ d (no-copy): TMid fires, copies LEFT = b. New value at p+1: b.
# Values: a, b, b, b, e. fb: 1+0+0+fb(b,e).
# If b = d: position p+1 has LEFT = b = SELF. TMidVal(b, b, e). Not no-copy. Might or might not fire.

# In the SA path (no seam step): position p+1 can fire independently.
# Position p+1: LEFT = c, SELF = d, RIGHT = e.
# If c ≠ d (yes, no-copy): fires, copies LEFT = c. New value: c.
# Values: a, b, c, c, e. fb(c,c)=0. Local fb = 1+1+0+fb(c,e).
# Both paths fire at p+1, both lose fb at the (p, p+1) edge.

# KEY: the seam step PLUS cascade = fc(before) - fc(after seam+cascade).
# SA with just the cascade = fc(before) - fc(after SA cascade).
# Compare.

print("=== Local window analysis: seam step at p ===")
print("Window: p-2, p-1, p, p+1, p+2 = a, b, c, d, e")
print("Constraint: all adjacent distinct (no-copy strip)\n")

# Enumerate all valid (a,b,c,d,e) tuples with adjacent distinct
for a in range(3):
    for b in range(3):
        if b == a: continue
        for c in range(3):
            if c == b: continue
            for d in range(3):
                if d == c: continue
                for e in range(3):
                    if e == d: continue
                    # Local fb before (edges p-2..p+1 to p-1..p+2):
                    # fb(a,b) + fb(b,c) + fb(c,d) + fb(d,e)
                    fb_before = fb(a,b) + fb(b,c) + fb(c,d) + fb(d,e)

                    # After seam at p: c → b (left copy). Values: a,b,b,d,e
                    seam_out = TMidVal(b, c, d)
                    assert seam_out == b, f"Expected left copy: TMidVal({b},{c},{d})={seam_out} ≠ {b}"
                    fb_after_seam = fb(a,b) + fb(b,b) + fb(b,d) + fb(d,e)

                    # After cascade at p+1 from seam: LEFT=b, SELF=d, RIGHT=e
                    if b != d:  # privileged
                        casc_out = TMidVal(b, d, e)  # = b (left copy, since b≠d, d≠e)
                        fb_after_seam_casc = fb(a,b) + fb(b,b) + fb(b,b) + fb(b,e)
                    else:
                        fb_after_seam_casc = fb_after_seam  # no cascade

                    # SA path: just cascade at p+1 (no seam). LEFT=c, SELF=d, RIGHT=e
                    if c != d:  # privileged (always true in no-copy)
                        sa_casc_out = TMidVal(c, d, e)  # = c (left copy)
                        fb_after_sa_casc = fb(a,b) + fb(b,c) + fb(c,c) + fb(c,e)
                    else:
                        fb_after_sa_casc = fb_before

                    # SA path: skip both seam and cascade (do nothing)
                    fb_skip_all = fb_before

                    # Best SA: max of (do nothing, just cascade at p+1)
                    best_sa_fb = max(fb_skip_all, fb_after_sa_casc)

                    # TP path: seam + optional cascade
                    tp_fb = min(fb_after_seam, fb_after_seam_casc)  # worst case
                    tp_fb_best = max(fb_after_seam, fb_after_seam_casc)

                    # Check: is best_sa_fb >= tp_fb_best?
                    if best_sa_fb < tp_fb_best:
                        print(f"PROBLEM: (a,b,c,d,e)=({a},{b},{c},{d},{e})")
                        print(f"  fb_before={fb_before}")
                        print(f"  fb_seam={fb_after_seam}, fb_seam+casc={fb_after_seam_casc}")
                        print(f"  fb_sa_casc={fb_after_sa_casc}, fb_skip={fb_skip_all}")
                        print(f"  best_SA={best_sa_fb} < best_TP={tp_fb_best}")

print("\n=== Summary: for EVERY no-copy local pattern, the best SA local fb ≥ best TP local fb ===")
print("(If no PROBLEM printed above, the local replacement theorem holds)")
