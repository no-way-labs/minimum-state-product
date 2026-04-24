#!/usr/bin/env python3
"""The counting argument for cascade unavoidability.

The key is not just that the adversary CAN fire non-interior procs,
but that the adversary can construct an actual bad CYCLE.

Core argument:
The adversary constructs a bad cycle by showing the bad-config graph
has a cycle. In the bad-config graph, each node is a bad config and
edges go from config c to config c' where c' = apply_move(c, p) for
some privileged proc p, and c' is also bad.

For convergence to hold: the bad-config graph must be a DAG (no cycles).
We show: at n>=8, the bad-config graph MUST have a cycle.

The drainage argument:
- Total bad configs: product - good_cycle_len ≈ product - O(n)
- Each bad config has at least one outgoing edge (liveness).
- An edge c -> c' either:
  (a) c' is good: this "drains" c to good. But good cycle has ~O(n) configs.
    Each good config can receive at most O(n) edges (from each proc direction).
    So total drainage capacity: O(n^2).
  (b) c' is bad: edge within the bad-config graph.

- If there are more bad configs than drainage capacity, SOME bad configs
  must have ALL edges going to OTHER bad configs. These form cycles.

Let's compute:
  product = 8 * (product of non-binary m_i)
  good cycle = O(n)
  drainage capacity per good config = bounded by sum of in-degrees

Actually the drainage capacity argument is subtler. Let me think about it
differently.

The FIBER argument: P1 (middle binary) is the bottleneck.
P1 has 8 contexts: (L, S, R) with L,S,R in {0,1}. Only 2 are mover contexts.
P1's transition function maps ALL configs with the same (L,S,R) at P1 identically.
Each mover context at P1 corresponds to product/8 configs.

When P1 fires at mover context (L,0,R): ALL product/8 configs with (L,0,R) at P1
simultaneously change. Only 2 mover contexts -> 2*product/8 = product/4 configs
are affected by P1.

For drainage through P1: each P1 mover step moves product/8 configs from one
binary state to another. But only ~2 of those configs are good. The other
product/8 - 2 are still bad after the move.

So P1-mediated drainage per step: ~2 configs drained (land in good).
Total P1 drainage over the good cycle: ~4 configs (P1 fires twice).

For P0 and P2: similar analysis. Each has at most 2 mover contexts.
P0 ctx = (c7, 0, c1) or (c7, 1, c1). With ms[7]=4, c7 in {0,1,2,3}.
P0 has 4*2=8 S=0 contexts. Toggle constraint: at most 4 mover contexts at S=0.
But fire count = 2 means 2 mover contexts total (1 at S=0, 1 at S=1).

Hmm, P0 has m=2, fires twice per good cycle. Anti-diagonal says mover contexts
are a specific pair. But P0's contexts include non-binary neighbors, so more
variety.

Let me think about this differently. The TOPOLOGICAL argument:

Consider the binary subgraph: the 8 binary triples {0,1}^3 form a cube.
Each binary triple b has product/8 configs. The good cycle visits ~2 configs
at each binary triple.

A binary fire changes one coordinate of b. So the binary subgraph dynamics
follow edges of the cube {0,1}^3.

For convergence: every bad config must have an acyclic path to good.
The good cycle visits 8 binary triples, each with ~2 good configs.

From a bad config at binary triple b:
  - Interior/border fires stay at b (don't change binary state).
  - Binary fires move to adjacent triple b'.

So drainage from b to good can happen in two ways:
  (a) Path stays at b, reaches one of ~2 good configs at b.
  (b) Path leaves b via binary fire to b', then drains from b'.

For (a): the ~2 good configs at b can drain at most a bounded number of
configs (those reachable from them via reverse edges). But with product/8 = 324
bad configs at b, this is overwhelmed.

For (b): this just moves the problem to another binary triple.
Eventually some triple must drain via (a) or the paths cycle.

The TOTAL drainage capacity: 8 binary triples * ~2 good configs each = ~16.
Each good config receives at most O(n) reverse edges.
Total capacity: O(n * 16) = O(n).

Total bad configs: product - ~16 ≈ product.
For n >= 8: product ≈ 2592, capacity ≈ 128. Ratio: 2592/128 ≈ 20.

But this is a rough bound. Let me be more precise.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))

from itertools import product as cartesian


def precise_drainage_bound(n, ms):
    """Compute precise drainage capacity bounds.

    Each good config g can drain bad configs that have a (reverse) path to g
    in the bad graph. For a config c to be drained to g, there must be a path
    c -> c1 -> ... -> g where all intermediate configs are bad.

    But since each step is a single proc fire, and each proc changes only
    one coordinate by one value, the path length from c to g is bounded by
    the Hamming-like distance.

    More importantly: each STEP in the path requires the mover proc to be
    privileged at that config. The privilege depends on the transition table.
    The table entry is fixed. So the reachability from c to g is determined
    by the table.

    The key constraint: the transition table has a finite number of entries.
    Each entry controls the behavior at product/(contexts_at_proc) configs.
    """
    product = 1
    for m in ms:
        product *= m

    print(f"\nn={n}, ms={ms}, product={product}")

    # Good cycle visits O(n) configs. In mixed sweep: exactly 2n configs.
    gc_len = 2 * n

    # For each good config g, how many bad configs can reach g in one step?
    # A bad config c reaches g via proc p fire iff:
    #   1. p is privileged at c (f_p(L,S,R) != S)
    #   2. apply_move(c, p) = g
    # Condition 2 means c and g differ only at position p: c[p] != g[p], all else same.
    # So c is obtained from g by changing g[p] to some other value.
    # Number of such c: sum over p of (ms[p] - 1) = sum(ms) - n.

    one_step_reach = sum(ms) - n
    print(f"  Good cycle length: {gc_len}")
    print(f"  One-step predecessors per good config: {one_step_reach}")
    print(f"  Total one-step drainage: {gc_len * one_step_reach}")

    # But not all one-step predecessors are bad! Some might be other good configs.
    # In the good cycle, each good config has exactly 1 successor (another good config).
    # So at most 1 of the one-step predecessors is good. The rest are bad.

    # For each bad config c that can reach g in one step:
    # c must have p privileged. This requires f_p(L_c, S_c, R_c) != S_c.
    # The designer COULD set f_p(L_c, S_c, R_c) = S_c (no privilege), which would
    # prevent this drainage. But then c would be dead (if no other proc is privileged).
    # Actually, some other proc might be privileged at c.

    # The designer's dilemma: making more procs non-privileged at c reduces
    # drainage paths but risks creating dead configs.

    # Key: the designer must make EVERY config have at least one privileged proc
    # (liveness). And every bad config must have a path to good (convergence).
    # These two constraints together force enough privilege that drainage works.

    # But at n >= 8, the constraints are contradictory:
    # - Product/gc_len = 2592/16 = 162 bad configs per good config
    # - Each good config can drain O(sum(ms)) ≈ 28 configs in one step
    # - Multi-step drainage: path length is bounded, so total drainage per good
    #   config is bounded by a polynomial in ms.

    # More precisely: the bad-config graph under convergence must be a DAG.
    # The DAG has product - gc_len ≈ product nodes.
    # Each node has out-degree >= 1 (liveness, edge to another bad or good config).
    # The DAG has gc_len sinks (good configs).
    # Maximum depth of DAG: bounded by product (trivially), but typically O(n^2).

    # The number of nodes in a DAG with D sinks and max depth L:
    # At most D * (max_fan_in)^L. With fan-in up to sum(ms), and L = O(n^2),
    # the capacity is D * sum(ms)^(O(n^2)) which is enormous.

    # So the simple counting argument doesn't work for DAG depth > 1.
    # The cascade is NOT forced by simple counting. It requires structural analysis.

    print(f"  Bad configs: ~{product - gc_len}")
    print(f"  Bad per good: {(product - gc_len) / gc_len:.1f}")
    print(f"  Simple one-step drainage capacity: {gc_len * one_step_reach}")
    print(f"  Ratio bad/capacity: {(product - gc_len) / (gc_len * one_step_reach):.2f}")

    # At n=8: 2576 bad / (16 * 12) = 2576/192 = 13.4. Under 1-step: not drained.
    # At n=7: 850 bad / (14 * 11) = 850/154 = 5.5. Still > 1.
    # At n=6: 276 bad / (12 * 10) = 276/120 = 2.3. Still > 1.
    # At n=5: 86 bad / (10 * 8) = 86/80 = 1.075. Barely > 1, but valid system exists.

    # So 1-step counting doesn't distinguish n=7 from n=8.
    # We need the FIBER argument.


def fiber_argument(n, ms):
    """The fiber coupling argument.

    P1 (middle binary) fires at 2 contexts out of 8. Each fire moves
    ALL product/8 configs with that context identically.

    Key: when P1 fires at context (L, 0, R), it changes c1 from 0 to 1.
    This affects product/8 configs. Of those, at most ~1 is good (part of
    the good cycle). The other product/8 - 1 are BAD configs that ALL
    transition to BAD configs (since the destination is also product/8 configs
    at the new binary state, of which at most ~1 is good).

    So each P1 fire step has:
    - product/8 configs entering the step
    - ~1 lands in good, product/8 - 1 remain bad
    - Drainage per P1 fire: ~1 config

    Total P1 drainage: 2 fires * ~1 = ~2 configs drained.
    Total configs needing drainage: product - gc_len.

    Even adding P0 and P2 drainage: ~2 each, total ~6.
    Plus non-binary proc drainage. But non-binary fires don't change binary state,
    so they can only drain within the same binary triple.

    Within binary triple b:
    - product/8 = 324 configs total
    - ~2 good configs
    - 322 bad configs
    - Non-binary procs can drain bad configs to the 2 good configs at b,
      or move them to other binary triples via binary fires.
    - Non-binary drainage is bounded by the number of non-binary firing paths
      that reach good configs.
    """
    product = 1
    for m in ms:
        product *= m

    non_bin = product // 8
    gc_len = 2 * n
    good_per_triple = gc_len / 8  # ~2

    print(f"\nn={n}, ms={ms}")
    print(f"  product/8 = {non_bin}")
    print(f"  good per binary triple ≈ {good_per_triple:.1f}")
    print(f"  bad per binary triple ≈ {non_bin - good_per_triple:.1f}")

    # P1 fiber coupling factor: product/8
    # This is the number of configs that move identically when P1 fires.
    fiber_size = non_bin

    # Drainage through P1: each fire drains at most good_per_triple configs
    p1_drainage = 2 * good_per_triple

    # Drainage through all binary procs: upper bound
    # P0 has product/(ms[n-1]*2*ms[1]) contexts per binary value
    # But the coupling is at the context level, not the fiber level.

    # Actually, the fiber coupling for P1 is:
    # All configs with fixed (c0, c1, c2) at P1's neighbors agree.
    # Since c0, c2 are binary, there are 4 combinations per binary state of P1.
    # Each combination determines P1's action.
    # The fiber is: all configs with the same (c0, c1, c2).
    # Size: product / (2*2*2) = product/8.

    # But wait: P1's context is (c0, c1, c2). All 3 are binary.
    # So P1 has 8 contexts, 2 are movers.
    # Each mover context has product/8 configs.

    print(f"  P1 fiber size: {fiber_size}")
    print(f"  P1 drainage (2 fires): {p1_drainage:.1f}")
    print(f"  Total bad configs: {product - gc_len}")
    print(f"  Ratio: {(product - gc_len) / p1_drainage:.1f}")

    # The fiber argument says P1 is a bottleneck: it processes configs in
    # blocks of 324, but can only drain ~2 per fire.
    # With 2576 bad configs and P1 drainage of 4: ratio 644.
    # Even with all 8 procs contributing: each fires ~2 times per good cycle.
    # Total drainage: 8 * 2 * ~2 = ~32. Ratio: 2576/32 = 80.5 -- matches the
    # bottleneck ratio from context saturation data!

    total_drainage_upper = gc_len  # Each good cycle step drains at most 1 config
    print(f"  Upper bound on total drainage: {total_drainage_upper}")
    print(f"  Undrained bad configs: >= {product - 2*gc_len}")

    # The REAL drainage capacity: each good cycle step c_i -> c_{i+1}:
    # c_i is a good config. Some bad configs might reach c_i.
    # But c_i transitions to c_{i+1} (a good config). So c_i is not a "drain"
    # in the traditional sense. Rather, good configs are absorbing states
    # under the closure property: moves from good stay good.

    # For drainage: a bad config c moves to good config g iff
    # apply_move(c, p) = g for some privileged p, and c != g.
    # This requires c to be a "predecessor" of g.

    # For each g in good cycle: predecessors are configs differing at one position.
    # There are sum(ms) - n such predecessors. Some are good (the previous step
    # in the good cycle). The rest are bad.

    # Each bad predecessor can drain to g in 1 step.
    # Multi-step drainage: a bad config c drains via c -> c1 -> ... -> g.
    # But each intermediate c_i must be bad and have p privileged.
    # The designer can TRY to make the bad graph a DAG.
    # The DAG must accommodate product - gc_len nodes with gc_len exits.


def main():
    for nn in [5, 6, 7, 8, 9]:
        if nn == 5:
            mms = (2,2,2,3,4)
        elif nn == 6:
            mms = (2,2,2,3,3,4)
        elif nn == 7:
            mms = (2,2,2,3,3,3,4)
        elif nn == 8:
            mms = (2,2,2,3,3,3,3,4)
        elif nn == 9:
            mms = (2,2,2,3,3,3,3,3,4)
        precise_drainage_bound(nn, mms)

    print("\n" + "="*70)
    print("FIBER ARGUMENT")
    print("="*70)

    for nn in [5, 6, 7, 8, 9]:
        if nn == 5:
            mms = (2,2,2,3,4)
        elif nn == 6:
            mms = (2,2,2,3,3,4)
        elif nn == 7:
            mms = (2,2,2,3,3,3,4)
        elif nn == 8:
            mms = (2,2,2,3,3,3,3,4)
        elif nn == 9:
            mms = (2,2,2,3,3,3,3,3,4)
        fiber_argument(nn, mms)


if __name__ == '__main__':
    main()
