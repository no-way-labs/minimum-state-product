#!/usr/bin/env python3
"""
RA16i: Verify that a non-adjacent binary pair always exists
when we have >= 3 binary procs with no 3 consecutive on a ring of size n >= 5.

More precisely: we need a pair (b1, b2) of binary procs such that
NEITHER b1 is adjacent to b2 NOR are b1's neighbors binary NOR b2's neighbors binary.

Actually, re-reading the mechanism: we just need b1 and b2 to NOT be
adjacent to EACH OTHER. The shift is at {b1, b2}. The mechanism at b1
works if b1's neighbors are NOT in {b1, b2}. Since b2 is not adjacent
to b1, neither b1-1 nor b1+1 equals b2. Similarly for b2.

So the condition is simply: b1 and b2 are non-adjacent on the ring.

With >= 3 binary procs and no 3 consecutive:
- Binary procs form a subset B of Z_n, |B| >= 3, no 3 consecutive in B
- Need: exists b1, b2 in B with |b1 - b2| mod n >= 2 and |b2 - b1| mod n >= 2

Claim: this always exists for n >= 5.
Proof: If ALL pairs in B are adjacent, then B forms a single arc of
consecutive positions. With |B| >= 3, this gives 3 consecutive binary,
contradicting the hypothesis.

Wait, that's not quite right. On a ring, adjacency is distance 1.
If all pairs have distance <= 1, then B is a clique in the ring's
adjacency graph. On a ring of size n >= 5, a clique has at most 2
nodes (each node has exactly 2 neighbors). So |B| >= 3 means B
can't be a clique. Done.

Actually, more carefully: I need to show that among >= 3 binary procs,
at least one PAIR is non-adjacent. On a ring of n >= 5, each node has
exactly 2 neighbors. So the maximum clique size is 2 (a pair of adjacent
nodes). With 3+ nodes, by pigeonhole some pair must be non-adjacent.

But wait -- there's a subtlety. On a ring of size 3 or 4, there are
triangles/cliques of size 3. But we require n >= 5 (or n >= 7 for sweep
to exist). For n >= 5: max clique in C_n is 2 (since n >= 5 means no
triangle). So any 3+ subset has a non-adjacent pair.

Actually for n=4: C_4 has max clique = 2. For n=3: C_3 is K_3 (all adjacent).
Since we need n >= 5, max clique = floor(n/2) for C_n? No -- for cycle
graph C_n, max clique = 2 for n >= 4, and 3 for n = 3.

So for n >= 4, any subset of size >= 3 on C_n has a non-adjacent pair.

Let me verify computationally.
"""
from itertools import combinations


def check_pair_existence():
    print("Verify non-adjacent pair existence")
    print("="*50)

    for n in range(4, 15):
        for nb in range(3, n+1):
            found_counter = 0
            no_pair_counter = 0
            for bin_combo in combinations(range(n), nb):
                bins_set = set(bin_combo)
                # Check no 3 consecutive
                has_triple = False
                for i in range(n):
                    if i in bins_set and (i+1)%n in bins_set and (i+2)%n in bins_set:
                        has_triple = True
                        break
                if has_triple:
                    continue

                # Check: exists non-adjacent pair?
                has_nonadj = False
                for i in range(len(bin_combo)):
                    for j in range(i+1, len(bin_combo)):
                        b1, b2 = bin_combo[i], bin_combo[j]
                        if abs(b1-b2) % n not in (1, n-1):
                            has_nonadj = True
                            break
                    if has_nonadj:
                        break

                if has_nonadj:
                    found_counter += 1
                else:
                    no_pair_counter += 1
                    print(f"  NO PAIR: n={n}, nb={nb}, bins={bin_combo}")

            if found_counter > 0:
                total = found_counter + no_pair_counter
                # Only print if there were valid cases
                pass

    print("\nDone. Any 'NO PAIR' lines above indicate failure.")

    # Also verify the specific cases we checked
    print("\nVerification for sweep-relevant cases:")
    for n in [5, 7, 9, 11, 13]:
        all_ok = True
        count = 0
        for nb in range(3, n+1):
            for bin_combo in combinations(range(n), nb):
                bins_set = set(bin_combo)
                has_triple = False
                for i in range(n):
                    if i in bins_set and (i+1)%n in bins_set and (i+2)%n in bins_set:
                        has_triple = True
                        break
                if has_triple:
                    continue
                count += 1

                has_nonadj = False
                for i in range(len(bin_combo)):
                    for j in range(i+1, len(bin_combo)):
                        b1, b2 = bin_combo[i], bin_combo[j]
                        if abs(b1-b2) % n not in (1, n-1):
                            has_nonadj = True
                            break
                    if has_nonadj:
                        break
                if not has_nonadj:
                    all_ok = False

        status = "ALL HAVE NON-ADJ PAIR" if all_ok else "SOME LACK NON-ADJ PAIR"
        print(f"  n={n}: {count} valid placements, {status}")


check_pair_existence()
