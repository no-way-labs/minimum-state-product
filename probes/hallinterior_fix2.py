"""For NO FIX cases: check if TLow at 1 or THigh at n-2 helps."""

TLow = {(0,0):1,(0,1):0,(0,2):0,(1,0):1,(1,1):0,(1,2):2,(2,0):0,(2,1):2,(2,2):1}
def fb(a, b): return 1 if a != b else 0

# NO FIX cases: (v0, v1, vnm2, vn) where flipping 0 and/or n-1 doesn't work
no_fix = [
    (0, 0, 0, 0), (0, 0, 0, 1),
    (0, 1, 1, 0), (0, 1, 1, 1),
    (1, 0, 0, 0), (1, 0, 0, 1),
    (1, 1, 1, 0), (1, 1, 1, 1),
]

for v0, v1, vnm2, vn in no_fix:
    # TLow at position 1: reads (c(0), c(1), c(2)). Output = TLow[c(1), c(2)].
    # We don't know c(2) exactly, but hallInterior says c(1) != c(2).
    # So c(2) in {0,1,2} \ {c(1)}.
    for v2 in range(3):
        if v2 == v1: continue  # hallInterior
        out1 = TLow.get((v1, v2))
        if out1 == v1: continue  # not privileged
        # After TLow at 1: c(1) -> out1
        # Check edges: (0, 1): fb(v0, out1), (1, 2): fb(out1, v2)
        # hallInterior gave c(1) != c(2) = v2. After TLow: out1 might equal v2 or v0.
        fb01_new = fb(v0, out1)
        fb12_new = fb(out1, v2)

        # Then flip 0 and/or n-1 if needed
        for flip0 in [False, True]:
            for flipn in [False, True]:
                v0f = 1 - v0 if flip0 else v0
                vnf = 1 - vn if flipn else vn
                all_ok = (fb(v0f, out1) == 1 and fb(vnf, v0f) == 1 and fb(vnm2, vnf) == 1 and fb(out1, v2) == 1)
                if all_ok:
                    steps = ["TLow@1"]
                    if flip0: steps.append("flip@0")
                    if flipn: steps.append("flip@n-1")
                    print(f"  ({v0},{v1},v2={v2},{vnm2},{vn}): fix={steps} ({len(steps)} steps)")
                    break
            else: continue
            break
        else:
            print(f"  ({v0},{v1},v2={v2},{vnm2},{vn}): STILL NO FIX after TLow@1")
