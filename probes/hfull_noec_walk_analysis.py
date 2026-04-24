#!/usr/bin/env python3
"""Analyze the ring-adjacent walk constraint under ¬EC.

Under ¬EC, gap1_ec forces consecutive movers to be ring-adjacent.
So movers form a walk on the ring graph where each step moves ≤1
position along the ring.

Key questions:
1. Can a ring-adjacent walk visit ALL n processors?
   Yes, trivially (walk around the ring). But...
2. How many distinct boundary triples does this require?
   At a binary proc (m_i=2), there are at most m_{i-1}*2*m_{i+1} triples.
   ¬EC requires mover and non-mover triples to be disjoint.
3. What's the minimum CL for a covering walk, and does it exceed
   the maximum good-cycle length (sub-threshold)?

Also: binary fire count parity. In a good cycle on a ring, each proc
returns to its start value after firing. For binary (m=2), fire count
must be EVEN (toggle 0→1→0). For ternary, fire count must be ≡0 mod 3
if using inc transitions, but generally just ≡0 mod (order of the
permutation applied).

The key insight: a ring-adjacent walk that covers n processors needs
at least n steps (to traverse the ring). But binary procs have very
few triples — disjointness may be impossible.
"""
import random
from itertools import product as iterproduct
from collections import Counter, defaultdict

def ring_dist(a, b, n):
    return min((a - b) % n, (b - a) % n)

def count_boundary_triples(ms, n):
    """Count boundary triples per processor."""
    triples = []
    for p in range(n):
        lp = (p - 1) % n
        rp = (p + 1) % n
        t = ms[lp] * ms[p] * ms[rp]
        triples.append(t)
    return triples

def max_good_cycle_length(ms):
    """Product of ms = total configs. Good cycle uses distinct configs,
    so CL ≤ product."""
    p = 1
    for m in ms:
        p *= m
    return p

def analyze_walk_constraints(n, ms):
    """Analyze what a ring-adjacent covering walk requires."""
    print(f"\n{'='*60}")
    print(f"n={n}, ms={ms}")
    prod = 1
    for m in ms:
        prod *= m
    threshold = 4 * 3**(n-2)
    print(f"Product = {prod}, threshold = {threshold}, sub = {prod < threshold}")
    print(f"Max CL (product) = {prod}")

    triples = count_boundary_triples(ms, n)
    print(f"\nBoundary triples per proc: {triples}")

    # For ¬EC: mover triples ∩ non-mover triples = ∅
    # If proc p fires fc[p] times, it sees fc[p] mover triples
    # and CL - fc[p] non-mover triples. Disjointness needs:
    # fc[p] + (CL - fc[p]) ≤ triples[p]  ... NO, triples can repeat
    # Actually: |mover_set| + |nonmover_set| ≤ triples[p]
    # So triples[p] bounds the sum of distinct mover + non-mover triples.

    # For binary proc: triples[p] = m_{p-1} * 2 * m_{p+1}
    # Mover triples: the triple (L, S, R) appears at a step where p fires.
    #   After firing, S changes. So S is the "before" value.
    # Non-mover triples: triple appears when someone else fires.
    #   p's value S doesn't change at this step.

    print(f"\nBinary procs (m=2):")
    for p in range(n):
        if ms[p] == 2:
            lp, rp = (p-1)%n, (p+1)%n
            total = triples[p]
            # In a ¬EC cycle where p fires: each mover triple has S∈{0,1},
            # and cannot also appear as non-mover triple.
            # Binary fire count must be even (returns to start).
            print(f"  P{p}: {total} triples, L∈[0,{ms[lp]-1}], R∈[0,{ms[rp]-1}]")
            print(f"    If fc={2}: needs 2 mover + (CL-2) non-mover triples, all distinct")
            print(f"    Max distinct triples = {total}. So CL ≤ {total}.")

    print(f"\nTernary procs (m≥3):")
    for p in range(n):
        if ms[p] >= 3:
            lp, rp = (p-1)%n, (p+1)%n
            total = triples[p]
            print(f"  P{p}: {total} triples, L∈[0,{ms[lp]-1}], R∈[0,{ms[rp]-1}]")

    # Key constraint: CL ≤ min over ALL procs of triples[p]
    # because every proc sees CL triples total (with repetition allowed
    # but mover/nonmover sets must be disjoint).
    # Actually not quite — triples can repeat within mover set or within
    # nonmover set. The constraint is just disjointness of the two SETS.

    # But for a binary proc with fc=2 (fires twice with values 0→1, 1→0):
    # The two mover triples have S=0 and S=1 respectively.
    # So mover set has ≤ 2 triples.
    # Non-mover set: triples where p doesn't fire. Must avoid those 2.
    # Non-mover triples: (L, 0, R) and (L, 1, R) can appear freely
    # as long as they don't match any mover triple.

    # COVERING WALK analysis:
    # A ring-adjacent walk on n processors that visits all of them.
    # Minimum length: must traverse from one end to the other.
    # For a walk starting at position a, to reach the farthest proc
    # on a ring of n, you need at least n-1 steps.
    # But it's a cycle (last→first must also be adjacent).
    # So minimum covering walk length = n (visit each once = Hamiltonian).
    # But fire counts must be ≥1 for all, and binary must be even ≥2.

    binary_count = sum(1 for m in ms if m == 2)
    # Minimum total firings: binary procs fire ≥2 each, others ≥1 each
    # But wait: fc is the number of times a proc is the MOVER, not
    # just the number of times it changes. In a good cycle, each step
    # has exactly one mover. So CL = sum of all fire counts.
    min_CL_hfull = binary_count * 2 + (n - binary_count) * 1
    # Actually ternary needs fire count divisible by something? Not necessarily.
    # A ternary proc can fire once: 0→1 then cycle closes with value 1→...
    # Wait, in a good cycle, each proc must return to its starting value!
    # So fc(p) must be such that after fc(p) firings, p returns to start.
    # For binary: fc(p) must be even.
    # For ternary: depends on transition function. Could be 1→2→0→1 (3 fires)
    # or other patterns. But if transition is context-dependent, could be
    # 0→1→0 (2 fires) if the transition changes based on context.
    # Actually for ternary, the transition at each firing depends on the
    # full context (L, S, R), not just S. So fc(p) can be anything ≥ 1
    # as long as the VALUES cycle back. Minimum is... complex.

    # Conservative: binary needs ≥2, ternary needs ≥1. But ternary with
    # fc=1 means value changes 0→x and must return... but in a CYCLE,
    # the last config transitions to the first. So after all firings,
    # proc p must have the same value as at step 0. If p fires once and
    # changes v→v', then p never fires again, so p's value stays at v'
    # for the rest of the cycle. But at the end, we need value = v.
    # So v' must equal v, contradiction (firing means value changes).
    # Therefore fc(p) ≥ 2 for ALL procs in a good cycle!

    # Wait is that right? In a good cycle, each CONFIG is distinct.
    # The mover changes. After step k, the mover p changes from
    # config[k][p] to config[k+1][p] ≠ config[k][p].
    # The cycle is: config[0] → config[1] → ... → config[CL-1] → config[0].
    # For each proc p, the sequence of values p takes is:
    # v_0, v_1, ..., v_{CL-1}, and then v_0 again.
    # At non-mover steps: v stays the same.
    # At mover steps (where p fires): v changes.
    # Since we return to v_0 at the end, the number of VALUE CHANGES
    # at p must form a cycle: v_0 → v_a → v_b → ... → v_0.
    # Each firing changes the value, so fc(p) = number of value changes.
    # Minimum number of changes to return to start: 0 (never fires) or ≥2.
    # Can't be 1 (would change and never return).

    # So for hfull: fc(p) ≥ 2 for ALL p.
    # For binary: fc(p) even, so fc(p) ≥ 2.
    # For ternary: fc(p) ≥ 2.
    min_CL_hfull = n * 2  # at least 2 per proc
    print(f"\nMinimum CL for hfull: ≥ {min_CL_hfull} (each proc fires ≥2)")
    print(f"This is 2n = {2*n}")

    # Now: is CL = 2n achievable with a ring-adjacent walk + ¬EC?
    # The walk has 2n steps, visits each proc exactly 2 times as mover.
    # The walk is ring-adjacent: consecutive movers differ by ≤1.
    # A walk of length 2n on a ring of n, each node visited ≥2 times...
    # This is a walk that traverses the ring twice (back and forth) or
    # goes around twice.

    # Key bottleneck: binary procs.
    # A binary proc p with ms[p]=2 fires exactly 2 times.
    # It has m_{p-1}*2*m_{p+1} total triples.
    # With binary neighbors: 2*2*m_r or m_l*2*2 = small numbers.
    # If both neighbors are binary: 2*2*2 = 8 triples.
    # Need 2 mover + (2n-2) non-mover triples, all distinct.
    # So 2n ≤ 8 → n ≤ 4. IMPOSSIBLE for n ≥ 5 if binary has two binary neighbors!

    # But our setup has NON-CONSECUTIVE binary. So binary procs always
    # have at least one ternary neighbor.
    # If p is binary with one ternary neighbor: triples = 3*2*2 = 12 or 2*2*3 = 12.
    # Need 2n ≤ 12 → n ≤ 6.
    # If p is binary with two ternary neighbors: triples = 3*2*3 = 18.
    # Need 2n ≤ 18 → n ≤ 9. TIGHT at n=9!

    # But CL = 2n is minimum. Actual CL might be larger, making it worse.

    print(f"\n--- TRIPLE BUDGET ANALYSIS ---")
    for p in range(n):
        t = triples[p]
        # Under hfull + ¬EC:
        # mover triples (set) + non-mover triples (set) ≤ t
        # CL steps total. At each step, proc p sees some triple.
        # Distinct non-mover triples ≤ t - |mover_set|.
        # But non-mover steps = CL - fc[p], and they can repeat.
        # So no direct CL bound from this...
        # UNLESS we argue that non-mover triples must be distinct too.
        # They don't have to be distinct! Multiple non-mover steps can
        # see the same triple. That's fine for ¬EC (just needs mover∩nonmover=∅).

        # So the real constraint is: mover_set ⊆ T_p, nonmover_set ⊆ T_p \ mover_set.
        # |mover_set| ≤ fc[p] (each firing sees one triple, could repeat).
        # No direct CL bound from triple budget alone!
        pass

    print("Triple budget alone does NOT bound CL (non-mover triples can repeat).")
    print("The constraint is qualitative: mover_set ∩ nonmover_set = ∅.")

    # So what DOES prevent hfull + ¬EC?
    # Let's think about it differently.
    #
    # Under ¬EC, mover walk is ring-adjacent. For hfull, walk covers all n procs.
    # A ring-adjacent walk on a ring = a path that can go CW or CCW at each step.
    # Think of it as a 1D random walk on Z/nZ.
    #
    # For the walk to return to start (cycle), net displacement = 0 mod n.
    #
    # For coverage: must visit all n positions.
    #
    # The walk corresponds to the MOVER SEQUENCE. At each step, the mover
    # changes to an adjacent proc or stays (mover[k+1] = mover[k] ± 1 or mover[k]).
    #
    # Wait — "ring-adjacent" means ring_dist ≤ 1, so the mover can STAY.
    # mover[k+1] = mover[k] is allowed (same proc fires twice in a row).
    # But in a good cycle, configs are distinct, so if the same proc fires
    # twice in a row, the config must change between those two steps.

    # STAY moves: mover[k] = mover[k+1] = p. Then p fires at steps k and k+1.
    # Config changes: config[k] → config[k+1] → config[k+2].
    # At step k: p changes from v to v'. At step k+1: p changes from v' to v''.
    # These are two consecutive firings of p with potentially different contexts.

    # So a covering walk CAN stay at a proc (firing it multiple times).
    # The walk visits all n procs but with variable dwell times.

    # KEY STRUCTURAL RESULT:
    # For a ring-adjacent walk of length CL on n nodes to cover all nodes,
    # the walk must make at least n-1 "move" steps (changing position).
    # If it starts at position s and must visit all positions, it needs
    # to traverse a path of length ≥ n-1 on the ring (going one direction
    # then back counts). With STAY moves allowed, total length can be
    # larger without increasing coverage.

    # Let's think about what happens with n=9, ring-adjacent, all procs fire.
    # Minimum scenario: walk goes 0→1→2→...→8→7→6→...→0.
    # Length = 8 + 8 = 16 (sweep right then left). Each proc fires ≥2.
    # But binary procs fire exactly 2 (enter and leave, or enter from both
    # sides). Ternary procs fire varying amounts.

    # THIS IS THE KEY: does such a walk allow ¬EC?
    # The walk structure constrains the MOVER at each step.
    # The mover determines which proc fires.
    # ¬EC requires that at each proc p, the boundary triple at mover steps
    # is never repeated at non-mover steps.

    # For a proc in the middle of the walk (not at the turning point),
    # it fires twice: once on the way right, once on the way left.
    # The boundary triples at these two firings must both avoid appearing
    # at any other step.

    # But at non-mover steps, the triple at p is determined by the
    # global config. There are CL - 2 non-mover steps, each giving
    # a triple at p. The 2 mover triples must not appear in this set.

    # For a binary proc with 2 ternary neighbors: 18 possible triples.
    # 2 mover triples out of 18. 16 remaining for non-mover.
    # CL - 2 non-mover steps need triples from those 16.
    # No direct impossibility from counting alone if triples can repeat.

    # So what's the REAL obstruction?

    return triples

def main():
    for n, ms in [(5, [2,3,2,3,2]),
                  (7, [2,3,2,3,2,3,3]),
                  (9, [2,3,2,3,2,3,3,3,3]),
                  (9, [2,3,3,2,3,3,2,3,3]),
                  (11, [2,3,2,3,2,3,3,3,3,3,3])]:
        analyze_walk_constraints(n, ms)

    # Now: EMPIRICAL CHECK
    # At n=9, can a ring-adjacent walk of length ≥18 that covers all
    # 9 procs be realized as a good cycle with ¬EC?
    # Let's enumerate short covering walks and check feasibility.

    print(f"\n\n{'='*60}")
    print("WALK COVERAGE ANALYSIS")
    print(f"{'='*60}")

    for n in [5, 7, 9]:
        # Generate ring-adjacent walks that cover all n procs
        # Walk: sequence of positions, consecutive differ by ≤1 mod n
        # Must be a cycle (last → first adjacent)
        # Must cover all n positions
        # Each position appears ≥2 times

        # For small n, enumerate walks of length 2n
        CL = 2 * n
        print(f"\nn={n}, CL={CL}: counting ring-adjacent covering walks (cyclic)")

        count = count_covering_walks(n, CL)
        print(f"  Covering walks of length {CL}: {count}")

def count_covering_walks(n, CL, max_count=100000):
    """Count ring-adjacent cyclic walks of length CL covering all n procs."""
    # Use DFS with pruning
    count = [0]

    def dfs(pos, step, visited, walk):
        if count[0] >= max_count:
            return
        if step == CL:
            # Check: cyclic (last→first adjacent) and all visited
            if ring_dist(walk[-1], walk[0], n) <= 1 and len(visited) == n:
                count[0] += 1
            return
        # Remaining steps
        remaining = CL - step
        # Pruning: can't cover more than remaining + |visited| procs
        # (each new step can add at most 1 new proc)
        if len(visited) + remaining < n:
            return
        for delta in [-1, 0, 1]:
            next_pos = (pos + delta) % n
            new_visited = visited | {next_pos}
            dfs(next_pos, step + 1, new_visited, walk + [next_pos])

    for start in range(n):  # symmetry: divide by n later
        dfs(start, 1, {start}, [start])
        break  # just start=0, multiply by n/symmetry

    return count[0]

if __name__ == '__main__':
    main()
