#!/usr/bin/env python3
"""Analyze good cycle lengths and drainage capacity at n=7 vs n=8.

Key finding from n=7 valid system: good cycle has 75 configs (not 14!).
This gives 30 good configs at binary=(1,1,1), providing much more drainage.

At n=8: maximum possible good cycle length?
Each proc fires m_p times per good cycle (exactly once per state value).
Good cycle length = sum of fires = sum(m_p) = 2+2+2 + (n-4)*3 + 4 = 3n-2.
Wait, that's the formula for mixed-sweep. For general constructions it can be longer.

Actually: good cycle length is constrained by mutual exclusion:
each good config has EXACTLY one privileged proc.
So cycle = sequence of configs, each with unique mover.
Each proc fires some number of times. The total cycle length = sum of fire counts.

For proc p with m_p states: minimum fire count is m_p - 1 (visit all states
in a path) or m_p (visit all states in a cycle). But the good cycle IS a cycle,
so proc p must return to its starting state. If proc p fires k_p times, then
k_p >= m_p (must cycle through all values? No, just return to start).

Actually k_p can be as low as 2 (fire twice, ending back at start) for any m_p.
Or as high as needed.

For 3CB good cycle: P1 fires exactly 2 times (m_1=2, must fire 0->1 and 1->0).
Other procs fire at least 2 times each.

Good cycle length >= 2 * n (each proc fires at least 2).

At n=7: valid system has good cycle of 75. That's ~10.7 per proc on average.
At n=8: need good cycle of at least... what?

The drainage argument: need good configs at each binary triple to be sufficient.
At n=7: 30 good at (1,1,1) out of 108 = 27.8%.
At n=8: would need ~90 good at (1,1,1) out of 324 = 27.8% to match ratio.
Total good cycle: ~90 * 8 / (varies per triple) = very long.

But the anti-diagonal constraint limits P1 to fire at exactly 2 contexts.
P1 fires at (a,0,c) and (1-a,1,1-c). Each fire corresponds to product/8 configs.
Of those, only 1 per context is in the good cycle (mutual exclusion: at the
good config where P1 fires, P1 is the unique mover).

So: good cycle has exactly 2 configs where P1 fires.
At binary=(1,1,1): P1 fires at most 1 time (the 1->0 transition).
The config where P1 fires at (1-a, 1, 1-c): this has c0=1-a, c1=1, c2=1-c.
For binary=(1,1,1): need c0=1, c2=1. So 1-a=1 and 1-c=1, meaning a=0, c=0.
This happens only if the anti-diagonal pair includes the context (0,0,0)/(1,1,1).
If P1's S=0 mover is (0,0,0), then S=1 mover is (1,1,1). Binary=(1,1,1)
has (c0,c1,c2) where c0 and c2 can vary...

Wait. P1's context is (c0, c1, c2). At binary=(1,1,1): c0=1, c1=1, c2=1.
So P1's context is (1, 1, 1). P1 fires iff f1(1,1,1) != 1.
The anti-diagonal: S=1 mover context is (1-a, 1, 1-c).
If S=0 mover is (1,0,0): S=1 mover is (0,1,1). At (1,1,1): not (0,1,1). P1 stays.
If S=0 mover is (0,0,1): S=1 mover is (1,1,0). At (1,1,1): not (1,1,0). P1 stays.
If S=0 mover is (0,0,0): S=1 mover is (1,1,1). At (1,1,1): YES! P1 fires.
If S=0 mover is (1,0,1): S=1 mover is (0,1,0). At (1,1,1): not (0,1,0). P1 stays.

So P1 fires at binary=(1,1,1) only if S=0 mover is (0,0,0).
In the good cycle, this config (1,1,1,...) where P1 fires from state 1
is ONE good config at binary=(1,1,1).

For other mover choices: P1 does NOT fire at binary=(1,1,1).
P1 fires at some OTHER binary triple (e.g., (0,1,1) if S=1 mover is (0,1,1)).

So good configs at binary=(1,1,1) are determined by NON-P1 procs' firings.
P0, P2 each fire at binary=(1,1,1) at most once.
Non-binary procs can fire multiple times at binary=(1,1,1).

The n=7 valid system has 30 good at (1,1,1). This means many non-binary firings
happen while binary=(1,1,1).

Can n=8 achieve similar ratios? Let's compute the maximum possible good configs
at binary=(1,1,1).
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))

from itertools import product as cartesian
from collections import Counter


def max_good_at_binary(n, ms, binary_procs):
    """Upper bound on good configs at a specific binary triple.

    At binary=(1,1,1), good configs must each have exactly one privileged proc.
    The movers at these configs can be any proc.

    Each binary proc fires at most 1 time at binary=(1,1,1).
    That's 3 good configs from binary proc movers.

    Each non-binary proc p can fire at most ms[p]-1 times at binary=(1,1,1)
    (it must change state each time, and has ms[p] values).
    Actually, it can fire any number of times, as long as it cycles.
    But each fire uses a distinct (L,S,R) context (mutual exclusion).

    For proc p, the number of distinct contexts at binary=(1,1,1):
    ctx = (c[p-1], c[p], c[p+1]). With binary fixed:
    - If p-1 and p+1 are both non-binary: contexts = ms[p-1] * ms[p] * ms[p+1]
    - If one neighbor is binary: that coordinate is fixed at 1.
    """
    non_binary = [p for p in range(n) if ms[p] > 2]

    # At binary=(1,1,1), the non-binary state space has product/8 configs.
    # Each good config has exactly one mover. The movers at binary=(1,1,1) form
    # a sequence: each step fires one proc, changing one non-binary coordinate
    # (or changing a binary coordinate, which would leave binary=(1,1,1)).

    # Actually, firing a binary proc at (1,1,1) changes binary state.
    # So binary proc fires LEAVE binary=(1,1,1). Only non-binary fires STAY.

    # At binary=(1,1,1), the good cycle visits configs where:
    # 1. A non-binary proc fires (stays at binary=(1,1,1))
    # 2. A binary proc fires (leaves binary=(1,1,1))
    # Only (1) contribute to good configs AT binary=(1,1,1).
    # Plus the configs right BEFORE a binary proc fires (the binary proc is mover,
    # but the config is still at (1,1,1)).

    # So good configs at (1,1,1) = (non-binary fires at (1,1,1)) + (binary fires from (1,1,1))

    # The good cycle can enter binary=(1,1,1) multiple times (each time a binary
    # proc fires from some other triple to (1,1,1)).

    # Maximum: the good cycle spends as much time at (1,1,1) as possible.
    # Each visit starts with a binary fire INTO (1,1,1) and ends with a binary fire
    # OUT of (1,1,1). Between entries and exits: non-binary fires.

    # Number of entries = number of exits (cycle). Each entry is from an adjacent
    # binary triple. At most 3 entries per visit (one per binary proc).

    # For maximum good at (1,1,1): maximize the number of non-binary fire steps
    # between entries and exits.

    # Upper bound: product/8 (all configs at (1,1,1) are good).
    # But mutual exclusion: each good config has exactly one mover.
    # The good configs at (1,1,1) form a path (or collection of paths)
    # in the non-binary state space.

    non_bin_product = 1
    for p in non_binary:
        non_bin_product *= ms[p]

    print(f"\nn={n}, ms={ms}")
    print(f"Binary procs: {binary_procs}")
    print(f"Non-binary state space: {non_bin_product}")
    print(f"Theoretical max good at (1,1,1): {non_bin_product} (every config good)")

    # But the good cycle must also visit OTHER binary triples!
    # Total good cycle length = sum of good configs across all 8 binary triples.
    # With only P1 firing 2 times total, and P0, P2 firing 2 times total:
    # Number of binary triple transitions = 2 * 3 = 6 (each binary proc fires 2x).
    # Wait, each binary proc fires exactly 2 times total in the cycle.
    # Each fire changes the binary triple. So 6 binary-triple transitions total.
    # But transitions come in entry/exit pairs for each binary triple.

    # The good cycle visits multiple binary triples. At each, it can have a "stay"
    # of any length (non-binary fires).

    # Total cycle length = sum over all triples of (stay length + entry fires)
    # = sum of non-binary fires + 6 binary fires

    # Maximum good at (1,1,1) is limited by:
    # 1. Non-binary fire count at (1,1,1): bounded by non-binary contexts
    # 2. The good cycle must visit all procs (fairness)

    # For fairness: every proc must fire at least once.
    # This means every non-binary proc fires at least once somewhere.
    # If it fires at (1,1,1), that's fine. If not, it fires at another triple.

    print(f"Good cycle fires: 2 per binary proc (6 total), + non-binary fires")
    print(f"Non-binary procs: {len(non_binary)}, min fires each: 2")
    print(f"Min non-binary fires: {2 * len(non_binary)}")


def n7_vs_n8_comparison():
    """Compare the structural constraints at n=7 and n=8."""

    print("="*70)
    print("n=7 vs n=8 STRUCTURAL COMPARISON")
    print("="*70)

    # n=7: ms=(2,2,2,3,3,3,4) or rotations
    # Interior: 2 procs (P4, P5), 9 states
    # Border: P3(3), P6(4)
    # Non-binary configs: 3*3*3*4 = 108
    # Valid system has 75 good configs (69.4% of total!)

    # n=8: ms=(2,2,2,3,3,3,3,4)
    # Interior: 3 procs (P4,P5,P6), 27 states
    # Border: P3(3), P7(4)
    # Non-binary configs: 3*3*3*3*4 = 324
    # Best system has 16 good configs (0.6% of total)

    print("\nn=7:")
    print(f"  Non-binary configs: 108")
    print(f"  Valid system good cycle: 75")
    print(f"  Good/total ratio: {75/864:.1%}")
    print(f"  Good at (1,1,1): ~30")
    print(f"  Good fraction at (1,1,1): {30/108:.1%}")
    print(f"  Interior states: 9")
    print(f"  Boundary conditions: 12")
    print(f"  Interior * boundary: 108")

    print("\nn=8:")
    print(f"  Non-binary configs: 324")
    print(f"  Best system good cycle: 16 (mixed-sweep)")
    print(f"  Good/total ratio: {16/2592:.1%}")
    print(f"  Good at (1,1,1): ~6")
    print(f"  Good fraction at (1,1,1): {6/324:.1%}")
    print(f"  Interior states: 27")
    print(f"  Boundary conditions: 12")
    print(f"  Interior * boundary: 324")

    # The valid n=7 system achieves 27.8% good fraction at (1,1,1).
    # At n=8, to match this ratio: need 324 * 0.278 = 90 good configs at (1,1,1).
    # Total good cycle: at least 90 * 8 / weighted = very large.

    # But the total number of good configs is bounded by:
    # L = sum_p k_p where k_p is the fire count of proc p.
    # For binary procs: k_p = 2 (exactly). So 6 binary fires.
    # For non-binary procs: k_p >= 2.
    # Total L >= 6 + 2*(n-3).
    # At n=8: L >= 6 + 10 = 16. At n=7: L >= 6 + 8 = 14.

    # But the n=7 valid system has L=75! So non-binary procs fire many times.
    # Each non-binary proc fires k_p times. Average: (75-6)/4 = 17.25 fires per proc.
    # With ms[p]=3: 17 fires at 3-state proc means visiting each state ~6 times.
    # With ms[p]=4: might fire ~17 times too, visiting each state ~4 times.

    # At n=8: could non-binary procs fire enough times to get L=90?
    # Need (90-6)/5 = 16.8 fires per non-binary proc. Similar to n=7.
    # But each fire requires a unique context (mutual exclusion at good configs).
    # Proc p's context at good config: (c[p-1], c[p], c[p+1]).
    # Unique contexts: ms[p-1] * ms[p] * ms[p+1].
    # For interior proc P4: ctx = (c3, c4, c5), size = 3*3*3 = 27.
    # Can fire at most 27-1=26 times (must stay at some contexts).
    # Actually, can fire at most 27 times if all contexts are movers.
    # No: mutual exclusion means at the config where P4 fires, P4 is the UNIQUE mover.
    # Other procs must stay. This constrains THEIR tables too.

    # The key constraint: when P4 fires at context (c3, c4, c5), then
    # f4(c3, c4, c5) != c4. But also ALL other procs must stay.
    # In particular, P3 must stay at its context: f3(c2, c3, c4) = c3.
    # And P5 must stay: f5(c4, c5, c6) = c5.

    # This couples the tables of neighboring procs.
    # More fires = more constraints on neighboring tables.
    # At some point, too many constraints conflict -> can't extend the good cycle.

    print("\n" + "="*70)
    print("WHY n=8 GOOD CYCLE CAN'T BE LONG ENOUGH")
    print("="*70)

    # The key difference: at n=8, the interior has 3 procs (chain P4-P5-P6).
    # Each interior proc's context involves its neighbors.
    # The COUPLING between interior procs limits the good cycle length.

    # Specifically: when P4 fires, P5 must stay. P5's context includes c4.
    # So P5's table is constrained at (c4, c5, c6) = stay.
    # When P5 fires later, P4 and P6 must stay.
    # This back-and-forth constrains the tables increasingly.

    # At n=7: interior has only P4 and P5. The coupling is between 2 procs.
    # At n=8: interior has P4, P5, P6. The coupling is a chain of 3.
    # The chain of 3 has much tighter constraints than a chain of 2.

    # Quantitatively: at n=7, interior context space = 9.
    # P4 has 9 contexts, P5 has 12 contexts (P5 is adjacent to P6 which has 4 states).
    # At n=8: P4 has 27 contexts, P5 has 27, P6 has 36.
    # But the COUPLING constraints grow quadratically with context size.

    print("\nInterior coupling constraints:")
    print("n=7: 2 interior procs, 9 states, coupling = 2-chain")
    print("n=8: 3 interior procs, 27 states, coupling = 3-chain")
    print()

    # Actually the issue is simpler. At n=7 valid system:
    # ms = (3,2,2,2,3,4,3). Binary at 1,2,3. Non-binary: P0(3),P4(3),P5(4),P6(3).
    # Border: P4 and P0 (adjacent to binary procs 3 and 1).
    # Interior: P5 only! One interior proc.

    # At n=8 with binary at 0,1,2: border P3, P7. Interior P4,P5,P6.
    # 3 interior procs vs 1 interior proc.

    # With 1 interior proc: the interior dynamics are trivial.
    # P5 has 4 states, can fire at most 4 times per boundary condition.
    # 12 boundary conditions * 4 fires = 48 interior fires max.
    # Plus border and binary fires: 75 total good is achievable.

    # With 3 interior procs: P4,P5,P6 form a chain.
    # The chain dynamics are much more constrained.
    # At each boundary condition, the 3-chain must execute an acyclic sequence.
    # The chain's state space is 27. The max acyclic sequence through 27 states
    # is 27 steps. But the coupling constraints between P4-P5-P6 limit this
    # much further.

    print("n=7 rotated system: ms=(3,2,2,2,3,4,3)")
    print("  Binary: {1,2,3}, Border: {0,4}, Interior: {5} (ONE proc)")
    print("  Interior has 4 states (ms[5]=4)")
    print("  Much simpler interior dynamics!")
    print()
    print("n=8: Binary: {0,1,2}, Border: {3,7}, Interior: {4,5,6} (THREE procs)")
    print("  Interior state space: 27")
    print("  3-chain coupling: each fire of one proc constrains both neighbors")


def main():
    max_good_at_binary(7, (2,2,2,3,3,3,4), [0,1,2])
    max_good_at_binary(8, (2,2,2,3,3,3,3,4), [0,1,2])
    n7_vs_n8_comparison()


if __name__ == '__main__':
    main()
