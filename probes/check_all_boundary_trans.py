#!/usr/bin/env python3
"""Check if ALL boundary-changing transitions produce sixTupleEdge or extendedBoundaryEdge."""

from check_boundary_edges import sixTupleEdgeVals, encode, decode
from gen_cup2_ranks import TBotVal, TLowVal, TMidVal, THighVal, TTopVal

edge_set = set(sixTupleEdgeVals)
b4_unsafe = {(4,5),(10,11),(16,17),(22,23),(28,29),(34,35),
             (40,41),(46,47),(52,53),(148,149),(154,155),(160,161)}
extended_set = edge_set | b4_unsafe

def check_position(name, table_fn, L_range, S_range, R_range,
                    L_idx, S_idx, R_idx, S_boundary_idx):
    """Check all transitions at a boundary position.
    L_idx, S_idx, R_idx: which 6-tuple position corresponds to L, S, R
    (None if interior)
    S_boundary_idx: which 6-tuple field changes
    """
    total = 0
    in_orig = 0
    in_extended = 0
    missing = []

    for c0 in range(2):
        for c1 in range(3):
            for c2 in range(3):
                for cN3 in range(3):
                    for cN2 in range(3):
                        for cN1 in range(2):
                            s = [c0, c1, c2, cN3, cN2, cN1]
                            L = s[L_idx] if L_idx is not None else None
                            S = s[S_idx]
                            R = s[R_idx] if R_idx is not None else None

                            if L is None or R is None:
                                # Interior neighbor: try all values
                                int_range = range(3)
                                for int_val in int_range:
                                    actual_L = int_val if L is None else L
                                    actual_R = int_val if R is None else R
                                    if actual_L not in range(L_range) or actual_R not in range(R_range):
                                        continue
                                    out = table_fn(actual_L, S, actual_R)
                                    if out != S and out < S_range:
                                        src = encode(*s)
                                        s2 = list(s)
                                        s2[S_idx] = out
                                        tgt = encode(*s2)
                                        total += 1
                                        if (src, tgt) in edge_set:
                                            in_orig += 1
                                        if (src, tgt) in extended_set:
                                            in_extended += 1
                                        else:
                                            missing.append((src, tgt, s, s2, actual_L, S, actual_R, out))
                            else:
                                if L not in range(L_range) or R not in range(R_range):
                                    continue
                                out = table_fn(L, S, R)
                                if out != S and out < S_range:
                                    src = encode(*s)
                                    s2 = list(s)
                                    s2[S_idx] = out
                                    tgt = encode(*s2)
                                    total += 1
                                    if (src, tgt) in edge_set:
                                        in_orig += 1
                                    if (src, tgt) in extended_set:
                                        in_extended += 1
                                    else:
                                        missing.append((src, tgt, s, s2, L, S, R, out))

    print(f"{name}: {in_orig}/{total} in sixTupleEdge, {in_extended}/{total} in extended")
    for src, tgt, s, s2, L, S, R, out in missing[:5]:
        print(f"  MISSING: ({src},{tgt}): {s}→{s2} via ({L},{S},{R})→{out}")
    return len(missing) == 0

# Position 0 (T_bot): L=cN1(idx5), S=c0(idx0), R=c1(idx1)
print("=== Position 0 (T_bot) ===")
check_position("P0", TBotVal, 2, 2, 3, 5, 0, 1, 0)

# Position 1 (T_low): L=c0(idx0), S=c1(idx1), R=c2(idx2)
print("\n=== Position 1 (T_low) ===")
check_position("P1", TLowVal, 2, 3, 3, 0, 1, 2, 1)

# Position 2 (T_mid): L=c1(idx1), S=c2(idx2), R=interior(None)
print("\n=== Position 2 (T_mid, left side) ===")
check_position("P2", TMidVal, 3, 3, 3, 1, 2, None, 2)

# Position n-3 (T_mid): L=interior(None), S=cN3(idx3), R=cN2(idx4)
print("\n=== Position n-3 (T_mid, right side) ===")
check_position("Pn-3", TMidVal, 3, 3, 3, None, 3, 4, 3)

# Position n-2 (T_high): L=cN3(idx3), S=cN2(idx4), R=cN1(idx5)
print("\n=== Position n-2 (T_high) ===")
check_position("Pn-2", THighVal, 3, 3, 2, 3, 4, 5, 4)

# Position n-1 (T_top): L=cN2(idx4), S=cN1(idx5), R=c0(idx0)
print("\n=== Position n-1 (T_top) ===")
check_position("Pn-1", TTopVal, 3, 2, 2, 4, 5, 0, 5)
