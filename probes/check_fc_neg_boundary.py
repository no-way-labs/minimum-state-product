#!/usr/bin/env python3
"""Check if ALL boundary-changing copy-neighbor transitions (including Δfc<0) produce
sixBoundaryEdge or sixBoundaryTpZeroCertStep transitions."""

from check_boundary_edges import sixTupleEdgeVals, encode, decode
from gen_cup2_ranks import TBotVal, TLowVal, TMidVal, THighVal, TTopVal

edge_set = set(sixTupleEdgeVals)

# sixBoundaryTpZeroNonedge from SixTuple.lean
nonedge_vals = [
    (6, 54), (7, 55), (8, 56), (9, 57), (168, 216), (169, 217), (170, 218), (171, 219),
    (6, 126), (7, 127), (8, 128), (9, 129), (168, 288), (169, 289), (170, 290), (171, 291)
]
nonedge_set = set(nonedge_vals)

cert_set = edge_set | nonedge_set  # sixBoundaryTpZeroCertStep = edge ∨ nonedge

def localFc(L, S, R):
    """Local frontier count: # of (L≠S, S≠R) transitions."""
    return (1 if L != S else 0) + (1 if S != R else 0)

def check_copy_boundary_transitions():
    """Check all copy-neighbor transitions at boundary positions."""
    tables = {
        'bot': (TBotVal, 2, 2, 3),    # P0: L∈Fin2(cN1), S∈Fin2(c0), R∈Fin3(c1)
        'low': (TLowVal, 2, 3, 3),    # P1: L∈Fin2(c0), S∈Fin3(c1), R∈Fin3(c2)
        'high': (THighVal, 3, 3, 2),  # Pn-2: L∈Fin3(cN3), S∈Fin3(cN2), R∈Fin2(cN1)
        'top': (TTopVal, 3, 2, 2),    # Pn-1: L∈Fin3(cN2), S∈Fin2(cN1), R∈Fin2(c0)
    }

    for pos_name, (table, Lmax, Smax, Rmax) in tables.items():
        total = 0
        copy_total = 0
        fc_neg_copy = 0
        fc_neg_in_cert = 0
        fc_neg_missing = []

        for L in range(Lmax):
            for S in range(Smax):
                for R in range(Rmax):
                    out = table(L, S, R)
                    if out == S:
                        continue  # not privileged
                    total += 1
                    is_copy = (out == L or out == R)
                    if not is_copy:
                        continue
                    copy_total += 1
                    dfc = localFc(L, out, R) - localFc(L, S, R)
                    if dfc >= 0:
                        continue  # Δfc≥0, handled by TP-zero infrastructure
                    fc_neg_copy += 1

                    # Check boundary change for all possible remaining boundary values
                    # and whether the boundary transition is in cert_set
                    found_missing = False
                    for c0 in range(2):
                        for c1 in range(3):
                            for c2 in range(3):
                                for cN3 in range(3):
                                    for cN2 in range(3):
                                        for cN1 in range(2):
                                            s = [c0, c1, c2, cN3, cN2, cN1]
                                            # Check if this boundary state matches the (L,S,R)
                                            if pos_name == 'bot' and (s[5] == L and s[0] == S and s[1] == R):
                                                src = encode(*s)
                                                s2 = list(s)
                                                s2[0] = out  # c0 changes
                                                tgt = encode(*s2)
                                                if (src, tgt) not in cert_set:
                                                    fc_neg_missing.append((src, tgt, pos_name, L, S, R, out, dfc))
                                                    found_missing = True
                                                else:
                                                    fc_neg_in_cert += 1
                                            elif pos_name == 'low' and (s[0] == L and s[1] == S and s[2] == R):
                                                src = encode(*s)
                                                s2 = list(s)
                                                s2[1] = out
                                                tgt = encode(*s2)
                                                if (src, tgt) not in cert_set:
                                                    fc_neg_missing.append((src, tgt, pos_name, L, S, R, out, dfc))
                                                    found_missing = True
                                                else:
                                                    fc_neg_in_cert += 1
                                            elif pos_name == 'high' and (s[3] == L and s[4] == S and s[5] == R):
                                                src = encode(*s)
                                                s2 = list(s)
                                                s2[4] = out  # cN2 changes
                                                tgt = encode(*s2)
                                                if (src, tgt) not in cert_set:
                                                    fc_neg_missing.append((src, tgt, pos_name, L, S, R, out, dfc))
                                                    found_missing = True
                                                else:
                                                    fc_neg_in_cert += 1
                                            elif pos_name == 'top' and (s[4] == L and s[5] == S and s[0] == R):
                                                src = encode(*s)
                                                s2 = list(s)
                                                s2[5] = out  # cN1 changes
                                                tgt = encode(*s2)
                                                if (src, tgt) not in cert_set:
                                                    fc_neg_missing.append((src, tgt, pos_name, L, S, R, out, dfc))
                                                    found_missing = True
                                                else:
                                                    fc_neg_in_cert += 1

        print(f"{pos_name}: {total} privileged, {copy_total} copy, {fc_neg_copy} Δfc<0 copy")
        print(f"  Δfc<0 in cert: {fc_neg_in_cert}, missing: {len(fc_neg_missing)}")
        for src, tgt, pn, L, S, R, out, dfc in fc_neg_missing[:3]:
            print(f"    ({src},{tgt}): {pn} ({L},{S},{R})→{out} Δfc={dfc}")

check_copy_boundary_transitions()
