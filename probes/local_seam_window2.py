"""Local seam window analysis — correct version.
Only TpMidTriple positions fire. The seam step is a TpBadStep so it IS TpMidTriple."""

TMid = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):0,(0,1,2):0,
        (0,2,0):0,(0,2,1):0,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,
        (1,1,0):1,(1,1,1):1,(1,1,2):1,(1,2,0):1,(1,2,1):1,(1,2,2):1,
        (2,0,0):2,(2,0,1):2,(2,0,2):2,(2,1,0):1,(2,1,1):0,(2,1,2):2,
        (2,2,0):0,(2,2,1):2,(2,2,2):2}

# TpMidTriple: the 7 triples where TMid step is TP-preserving
TpMidTriples = {(0,1,0),(0,1,2),(0,2,2),(1,0,0),(1,0,1),(1,0,2),(1,1,2)}

def TMidVal(L, S, R): return TMid[(L,S,R)]
def fb(a, b): return 1 if a != b else 0
def is_privileged(L, S, R): return TMidVal(L, S, R) != S

# For a seam step at p: must be TpMidTriple (since it's TP-bad)
# Local window: a, b, c, d, e at positions p-2, p-1, p, p+1, p+2
# Seam step fires at p with triple (b, c, d) which must be TpMidTriple

print("=== Analysis of seam step at p, with TpMidTriple constraint ===\n")

# Track: for each valid local pattern (a,b,c,d,e) where (b,c,d) is TpMidTriple:
# What is the best TP path fc (seam + cascade)?
# What is the best SA path fc (no seam, cascade at p+1 optional)?
# Is best_SA >= best_TP always?

violations = 0
total = 0
for a in range(3):
    for b in range(3):
        if b == a: continue
        for c in range(3):
            if c == b: continue
            for d in range(3):
                if d == c: continue
                for e in range(3):
                    if e == d: continue
                    # Check: (b,c,d) is TpMidTriple? Seam step fires only if so.
                    if (b,c,d) not in TpMidTriples:
                        continue
                    total += 1

                    fb_before = fb(a,b) + fb(b,c) + fb(c,d) + fb(d,e)

                    # Seam step: output = TMidVal(b,c,d).
                    out_seam = TMidVal(b,c,d)
                    # After seam: a, b, out_seam, d, e
                    fb_after_seam = fb(a,b) + fb(b,out_seam) + fb(out_seam,d) + fb(d,e)

                    # Cascade at p+1 from seam state: (out_seam, d, e)
                    # Fires if TpMidTriple AND privileged
                    fb_after_seam_then_casc = fb_after_seam
                    if is_privileged(out_seam, d, e) and (out_seam, d, e) in TpMidTriples:
                        casc_out = TMidVal(out_seam, d, e)
                        fb_after_seam_then_casc = fb(a,b) + fb(b,out_seam) + fb(out_seam,casc_out) + fb(casc_out,e)

                    # TP best: seam only, or seam + cascade
                    tp_best = max(fb_after_seam, fb_after_seam_then_casc)

                    # SA options:
                    # 1. Do nothing: fb_before
                    sa_skip = fb_before

                    # 2. Fire at p+1 only (non-seam): triple (c, d, e)
                    sa_casc = fb_before
                    if is_privileged(c, d, e) and (c, d, e) in TpMidTriples:
                        out_sa = TMidVal(c, d, e)
                        sa_casc = fb(a,b) + fb(b,c) + fb(c,out_sa) + fb(out_sa,e)

                    sa_best = max(sa_skip, sa_casc)

                    if sa_best < tp_best:
                        violations += 1
                        print(f"VIOLATION: ({a},{b},{c},{d},{e})")
                        print(f"  fb_before={fb_before}")
                        print(f"  TP: seam={fb_after_seam}, seam+casc={fb_after_seam_then_casc}, best={tp_best}")
                        print(f"  SA: skip={sa_skip}, casc={sa_casc}, best={sa_best}")

print(f"\nTotal valid patterns: {total}, violations: {violations}")
if violations == 0:
    print("LOCAL SEAM REPLACEMENT HOLDS: for every TpMidTriple seam step,")
    print("the best SA local fb >= the best TP local fb on the 5-site window.")
