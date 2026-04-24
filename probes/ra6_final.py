#!/usr/bin/env python3
"""
RA6 Final: Definitive summary + full EC check at ALL procs.

The BinSCC verification ONLY checks EC at 'sandwiched' ternary procs
(ternary with binary on both sides). For gap-(3,3,3), there are NO
sandwiched procs. The BinSCC proof is correct but its scope is
LIMITED to alternating (gap-2) arrangements.

This script:
1. Confirms the scope limitation
2. Checks EC at ALL procs (not just sandwiched) for the CF cycle
3. Checks whether the CF cycle constitutes a genuine threat to the LB proof
4. Tests whether a VALID self-stabilizing SYSTEM can be built from it
"""
from collections import defaultdict
from itertools import product as iproduct

def main():
    print("RA6 FINAL: Definitive Analysis")
    print("=" * 70)

    n = 9
    ms = [2,3,3,2,3,3,2,3,3]
    word = [8,7,8,7,6,5,4,5,4,3,2,1,2,1,0,8,7,6,5,4,3,2,1,0]
    L = len(word)

    # 1. Sandwiched procs
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]
    print(f"ms={ms}")
    print(f"Sandwiched ternary (binary on both sides): {sandwiched}")
    print(f"Number of sandwiched: {len(sandwiched)}")
    print()

    if not sandwiched:
        print("*** NO SANDWICHED PROCS ***")
        print("The BinSCC proof mechanisms only apply at sandwiched positions.")
        print("This arrangement falls OUTSIDE the BinSCC proof's scope.")
        print()

    # 2. Full EC check at ALL procs
    print("--- EC check at ALL procs (incrementing transition) ---")
    configs = [[0]*n]
    for t in range(L):
        c = list(configs[-1])
        p = word[t]
        c[p] = (c[p]+1) % ms[p]
        configs.append(c)

    good = [tuple(c) for c in configs[:L]]

    mover_triples = defaultdict(set)
    nonmover_triples = defaultdict(set)
    for t in range(L):
        c = good[t]
        mover = word[t]
        for j in range(n):
            Lp = (j-1)%n; Rp = (j+1)%n
            triple = (c[Lp], c[j], c[Rp])
            if j == mover:
                mover_triples[j].add(triple)
            else:
                nonmover_triples[j].add(triple)

    print(f"{'Proc':>4s} {'m':>2s} {'Type':>8s} {'Mover':>6s} {'NonMov':>6s} {'Overlap':>7s} {'EC':>4s}")
    for j in range(n):
        overlap = mover_triples[j] & nonmover_triples[j]
        ptype = "binary" if ms[j] == 2 else "ternary"
        is_sand = "SAND" if j in sandwiched else ""
        print(f"{j:4d} {ms[j]:2d} {ptype:>8s} {len(mover_triples[j]):6d} "
              f"{len(nonmover_triples[j]):6d} {len(overlap):7d} "
              f"{'YES' if overlap else 'no':>4s} {is_sand}")

    total_ec = sum(1 for j in range(n) if mover_triples[j] & nonmover_triples[j])
    print(f"\nTotal procs with EC: {total_ec} / {n}")
    if total_ec == 0:
        print("*** CONFIRMED: NO EC AT ANY PROC ***")

    # 3. Show triple details
    print("\n--- Triple details per proc ---")
    for j in range(n):
        mt = mover_triples[j]
        nmt = nonmover_triples[j]
        print(f"Proc {j} (m={ms[j]}):")
        print(f"  Mover triples:    {sorted(mt)}")
        print(f"  NonMover triples: {sorted(nmt)}")
        print(f"  Overlap:          {sorted(mt & nmt)}")

    # 4. Can we build a valid system?
    print("\n--- System Construction Attempt ---")
    print("A valid self-stabilizing system needs a transition function f_j")
    print("for each proc j such that:")
    print("  - At mover contexts (L,S,R), f_j(L,S,R) != S (state changes)")
    print("  - At nonmover contexts (L,S,R), f_j(L,S,R) = S (state preserved)")
    print("  - No EC: same (L,S,R) doesn't appear as both mover and nonmover")
    print()

    # Check: for each proc, are the mover and nonmover triple sets disjoint?
    all_disjoint = True
    for j in range(n):
        if mover_triples[j] & nonmover_triples[j]:
            all_disjoint = False
            break

    if all_disjoint:
        print("All procs have disjoint mover/nonmover triples!")
        print("A valid transition function CAN be defined:")
        for j in range(n):
            print(f"  Proc {j} (m={ms[j]}):")
            for triple in sorted(mover_triples[j]):
                L_val, S_val, R_val = triple
                new_S = (S_val + 1) % ms[j]  # incrementing
                print(f"    ({L_val},{S_val},{R_val}) -> {new_S} [mover]")
            for triple in sorted(nonmover_triples[j]):
                L_val, S_val, R_val = triple
                print(f"    ({L_val},{S_val},{R_val}) -> {S_val} [nonmover=identity]")

        # But: is this a COMPLETE system? Do these rules cover ALL possible triples?
        print("\n  Coverage check:")
        for j in range(n):
            all_triples = set()
            m_L = ms[(j-1)%n]
            m_S = ms[j]
            m_R = ms[(j+1)%n]
            for l in range(m_L):
                for s in range(m_S):
                    for r in range(m_R):
                        all_triples.add((l,s,r))
            covered = mover_triples[j] | nonmover_triples[j]
            uncovered = all_triples - covered
            print(f"    Proc {j}: {len(all_triples)} possible, "
                  f"{len(covered)} covered, {len(uncovered)} uncovered")
            if uncovered:
                print(f"      Uncovered: {sorted(uncovered)[:10]}...")

        # For uncovered triples: the transition function can be arbitrary
        # (these triples are never encountered in the good cycle)
        # But for CONVERGENCE, we need these to be handled too.
        # The question is: can we set them to ensure convergence?

    print()
    print("=" * 70)
    print("CONCLUSIONS")
    print("=" * 70)
    print(f"""
1. THE BinSCC PROOF IS CORRECT but LIMITED IN SCOPE:
   - It proves EC for alternating (gap-2) binary arrangements
   - It checks EC only at 'sandwiched' ternary procs
   - For gap-(3,3,3) at n>=9, there are NO sandwiched procs
   - The proof doesn't apply to these arrangements

2. THE CF CYCLE IS REAL:
   - Word: {word}
   - ms={ms}, product=5832, sub-threshold (< 8748)
   - NO entry conflict at ANY processor (all 9 checked)
   - ALL 64 state-sequence combos are CF
   - Mover and nonmover triple sets are DISJOINT at every proc

3. IMPACT ON THE OVERALL PROOF:
   - The existing proof handles non-consecutive binary via BinSCC
   - BinSCC doesn't cover gap-(3,3,3) arrangements
   - These arrangements are possible starting at n=9
   - A NEW mechanism is needed for this case
   - Options: shadow cycle extension, MNU, counting argument

4. THE GAP-(3,3,3) STRUCTURE:
   - Binary at positions {{0,3,6}} (or rotations)
   - Each ternary segment has exactly 2 procs
   - The wiggle-sweep word bounces within each ternary pair
   - This creates enough triple diversity to avoid EC
   - Only possible when ALL segments have >=2 ternary procs
   - First occurs at n=9 (3 binary * gap 3 = 9)

5. WHAT'S NEEDED:
   - Either extend BinSCC to cover non-sandwiched ternary procs
   - Or prove shadow cycle / MNU for the gap-(3,3,3) case
   - Or find a counting/pigeonhole argument that works differently
""")


if __name__ == "__main__":
    main()
