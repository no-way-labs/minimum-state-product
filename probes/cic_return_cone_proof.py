#!/usr/bin/env python3
"""
CIC Exploration 11: Return Cone kills Case 3c for all n, all lengths.

Tools from GLB:
  Tool 1 (Return Cone Lemma): interval [t,u) with contiguous segment S where
    every proc in S untouched before t and frozen after u => C_t = C_u, killing cycle.
  Tool 2 (Two-Singleton-Edge Theorem): >=2 ring edges traversed exactly once
    => nontrivial return cone exists.
  Tool 3 (Binary-Bounce Context Lemma): binary neighbor b of p moves exactly
    twice in [t,u) while p and other neighbor q don't move => determinism contradiction.

Goal: For any n>=5, any state vector with >=3 pairwise non-adjacent binary procs
and product < 4*3^(n-2), every fair adjacent mover word is killed by Tool 2 or Tool 3.

Approach: counting/pigeonhole on edge traversal vectors.
"""

import itertools
import math
from collections import Counter

def analyze_edge_constraints(n, k, gap_sizes):
    """
    Analyze edge traversal constraints for Case 3c.

    n: number of processors
    k: number of binary processors (>=3)
    gap_sizes: list of k gap sizes (non-binary procs between consecutive binary procs)
              sum(gap_sizes) = n - k, each gap_size >= 1 (pairwise non-adjacent)

    Ring layout: b_0, [gap_0 non-binary], b_1, [gap_1 non-binary], ..., b_{k-1}, [gap_{k-1} non-binary]

    Edge types:
    - "binary-adjacent" edges: edges incident to a binary processor
      Each binary proc has 2 such edges. Since binary procs are non-adjacent,
      these 2k edges are all distinct.
    - "interior" edges: edges between two non-binary processors within a gap
      Gap of size g has g-1 interior edges.

    Total edges: n (ring)
    Binary-adjacent edges: 2k
    Interior edges: sum(g-1 for g in gap_sizes) = (n-k) - k = n - 2k
    Check: 2k + (n-2k) = n ✓
    """
    print(f"\n{'='*70}")
    print(f"Case 3c edge analysis: n={n}, k={k} binary procs")
    print(f"Gap sizes: {gap_sizes}")
    print(f"Total ring edges: {n}")
    print(f"Binary-adjacent edges: {2*k}")
    print(f"Interior edges: {n - 2*k}")
    print(f"{'='*70}")

    # Key constraint: binary processor moves even number of times >= 2.
    # If binary proc b has edges e_L (to left neighbor) and e_R (to right neighbor),
    # then: moves(b) = traversals of e_L from left + traversals of e_R from right
    #      (more precisely, b moves when the mover transitions TO b)
    # Actually, edge traversal count = number of times mover crosses that edge.
    # For processor p, moves(p) = sum of times p is the mover.
    # The mover word is a walk on C_n. Edge e=(p,p+1) is traversed each time
    # the walk goes p->p+1 or p+1->p.

    # Better framing: processor p's move count = number of times p appears in mover word.
    # Edge (p, p+1) traversal count = number of times consecutive movers are (p, p+1) or (p+1, p).

    # Key relationship: for adjacent mover walk on C_n,
    # edge(p, p+1) = |{t : (w_t, w_{t+1}) = (p, p+1) or (p+1, p)}|
    #              = number of times the walk crosses edge (p, p+1)

    # L = total length = sum of all edge traversals
    # For processor p, moves(p) = (edge to left of p + edge to right of p) / ...
    # No wait. moves(p) = number of times p appears as mover in the word.
    # Each appearance of p (except possibly first/last in cyclic word) is preceded
    # and followed by p-1 or p+1. So each appearance of p contributes 1 to
    # one of its adjacent edges (the incoming edge) and 1 to the outgoing edge.
    # Actually for a cyclic word of length L: sum of edge traversals = L (each step crosses one edge).
    # And moves(p) = multiplicity of p in the word.
    # L = sum over p of moves(p).

    # For binary proc b: moves(b) is even, >= 2.
    # For any proc p: moves(p) >= 2 (fairness).

    # Now, what about singleton edges?
    # Edge e = (p, p+1) is singleton if edge_count(e) = 1.

    # Claim: edges adjacent to a binary processor CANNOT be singletons.
    # Reason: if b is binary with neighbors q_L, q_R, and edge (q_L, b) is singleton,
    # then the walk crosses that edge exactly once. But b moves >= 2 times.
    # The walk visits b at least twice. Each visit to b must enter and exit via
    # one of its two edges. In a cyclic walk, entries = exits for each vertex.
    # entries(b) = moves(b) (each time b appears in the mover word, the walk arrived at b).
    # Wait, not exactly. Let me think again.

    # In a cyclic adjacent mover word w_0, w_1, ..., w_{L-1}, w_0, ...
    # edge(p, p+1) counts how many times the pair (w_t, w_{t+1 mod L}) equals
    # (p, p+1) or (p+1, p).

    # For vertex b, the number of times b appears = moves(b).
    # Each appearance of b at position t means: w_{t-1} and w_{t+1} are neighbors of b.
    # The "incoming" edge is (w_{t-1}, b) and "outgoing" edge is (b, w_{t+1}).
    # But wait, w_{t-1} could equal b (self-loop)? No, adjacency means |w_{t+1} - w_t| = 1
    # and no self-loop since the mover changes each step.
    # Actually, does adjacency allow staying? The mover word has w_{t+1} = w_t ± 1.
    # So no self-loops. Good.

    # So each appearance of b contributes 1 to one of its two edges (incoming)
    # and 1 to one of its two edges (outgoing).
    # Over all moves(b) appearances:
    #   edge_L(b) + edge_R(b) = 2 * moves(b)
    # where edge_L counts traversals of (b's left neighbor, b) and
    #       edge_R counts traversals of (b, b's right neighbor).
    # Wait, that's wrong. Each appearance of b at position t gives:
    #   one incoming edge traversal (from w_{t-1} to b)
    #   one outgoing edge traversal (from b to w_{t+1})
    # So total edge traversals touching b = 2 * moves(b).
    # But edge_L + edge_R = 2 * moves(b).

    # Now, for the edge to be singleton (count 1), we need edge_L = 1 or edge_R = 1.
    # Since edge_L + edge_R = 2 * moves(b) >= 4 (binary, moves >= 2, even),
    # if edge_L = 1, then edge_R = 2*moves(b) - 1 >= 3.
    # This is POSSIBLE. An edge adjacent to binary CAN be singleton.

    # Hmm wait, let me reconsider. Does edge_L + edge_R = 2*moves(b)?
    # Each of the moves(b) appearances has one incoming and one outgoing.
    # Incoming could be from left or right. Outgoing could be to left or right.
    # So: incoming_from_left + incoming_from_right = moves(b)
    #     outgoing_to_left + outgoing_to_right = moves(b)
    # edge_L = incoming_from_left + outgoing_to_left (total crossings of left edge)
    # edge_R = incoming_from_right + outgoing_to_right
    # edge_L + edge_R = 2 * moves(b). YES.

    # So binary-adjacent edges are NOT automatically non-singleton.
    # But there's a PARITY constraint:
    # For a cyclic walk, the number of times we cross an edge from left to right
    # must equal the number from right to left (net flow = 0 on the cycle).
    # So edge_L has equal left-to-right and right-to-left: edge_L is EVEN.
    # Similarly edge_R is EVEN.
    # Therefore: edge_L >= 0 even, edge_R >= 0 even, edge_L + edge_R = 2*moves(b).
    # BOTH edges adjacent to binary are EVEN.
    # Singleton = 1 = odd. IMPOSSIBLE.

    print(f"\n*** KEY INSIGHT: Binary-adjacent edges have EVEN traversal count ***")
    print(f"Proof: For any edge (p,p+1) in a cyclic walk, left-to-right crossings")
    print(f"= right-to-left crossings (net flow = 0 on ring). So edge count is even.")
    print(f"Wait - this applies to ALL edges, not just binary-adjacent ones!")

    # WAIT. This is wrong. Let me reconsider.
    # In a cyclic walk on C_n, for each edge, the number of left-to-right crossings
    # need NOT equal right-to-left crossings. The walk can have a net winding number.
    # For a cyclic walk w_0, ..., w_{L-1}, w_0, the net displacement is 0 (returns to start).
    # Net displacement = sum of steps = sum of (w_{t+1} - w_t) = 0 (mod n for ring, but these
    # are actual integers on C_n with |step| = 1).
    # Actually wait, processor labels are on a ring C_n. The walk is on the path graph
    # underlying the ring? No, it's on the cycle graph C_n.
    #
    # For C_n: processor p has neighbors p-1 mod n and p+1 mod n.
    # The walk w_0, w_1, ..., w_{L-1} with w_L = w_0 (cyclic).
    # For edge (p, p+1 mod n):
    #   forward crossings = |{t : w_t = p, w_{t+1} = p+1}|
    #   backward crossings = |{t : w_t = p+1, w_{t+1} = p}|
    # Net flow through edge (p, p+1) = forward - backward.
    # By flow conservation at each vertex: net flow in = net flow out = 0 (cyclic walk returns).
    # But net flow through ALL edges in the same direction must be equal (it's a cycle).
    # Actually, the net flow around the ring = winding number * n edges.
    # For a cyclic walk on C_n returning to start: winding number is some integer W.
    # Net flow through each edge = W (same for all edges by symmetry of the ring).
    #
    # So: forward(e) - backward(e) = W for every edge e.
    # edge_count(e) = forward(e) + backward(e).
    # forward(e) = (edge_count(e) + W) / 2
    # backward(e) = (edge_count(e) - W) / 2
    # Both must be non-negative integers, so edge_count(e) >= |W| and
    # edge_count(e) ≡ W (mod 2).
    # ALL edges have the same parity (= parity of W).
    #
    # For binary proc b with moves(b) even:
    #   edge_L(b) + edge_R(b) = 2*moves(b) = even.
    #   Since edge_L and edge_R have the same parity (both ≡ W mod 2),
    #   their sum is even regardless. This is consistent but doesn't force them even.
    #   If W is odd, all edge counts are odd, including binary-adjacent ones.
    #   If W is even, all edge counts are even.

    # So the question is: can W be odd?
    # L = sum of all edge counts = sum of (forward(e) + backward(e)) for all edges
    # = sum of (2*forward(e) - W) + sum(W) ... let me just compute:
    # L = sum over edges of edge_count(e)
    # Each edge_count(e) ≡ W (mod 2), so L ≡ n*W (mod 2).
    # Also L = sum of moves(p) for all p.
    # Binary procs have even moves. Non-binary procs have moves >= 2 (no parity constraint).

    # Now, key question: is there an additional constraint forcing W even?
    #
    # For the SEEDED cycle (starting at all-zeros config), the walk represents
    # transitions on the good cycle. The walk is on C_n as a graph.
    # The winding number W can be any integer.
    # For a "bounce" cycle (go up then down), W = 0.
    # For a "sweep" cycle (go around), W = ±1.
    # In general, W can be anything.

    # Let me reconsider the problem.
    # When W is even: all edges have even counts >= 2 (if positive), so NO singletons.
    #   => Tool 2 applies vacuously? No, 0 singletons, Tool 2 needs >= 2.
    #   Actually if W=0 and all edges even, could have edges with count 0.
    #   But wait, fairness requires every proc moves >= 2, so every proc is visited.
    #   If proc p is visited, at least one of its edges has positive count.
    #   But could some edges have count 0? Yes, if the walk never crosses that edge.
    #   A connected walk on C_n that visits all vertices must cross all edges? No!
    #   Example: bounce walk 0,1,2,...,n-1,...,2,1,0 visits all vertices but
    #   never crosses edge (n-1, 0).

    # OK let me think about this more carefully with a concrete computation.
    print(f"\n*** REVISED: All edges have parity ≡ W (mod 2) where W = winding number ***")
    print(f"If W odd: all edge counts odd, so 0 or many singletons possible")
    print(f"If W even: all edge counts even, so 0 singletons (no edge count = 1)")

    return


def count_singleton_edges_general(n, k):
    """
    General analysis: how many singleton edges can a Case 3c mover word have?

    n processors, k >= 3 non-adjacent binary.
    All edges have same parity (winding number W mod 2).

    Case W even: all edge counts even => 0 singletons.
      Need to show binary-bounce (Tool 3) applies.

    Case W odd: all edge counts odd.
      Minimum edge count = 1 (singleton) or >= 3.
      L = sum of edge counts.
      With all odd: L ≡ n (mod 2) since sum of n odd numbers ≡ n mod 2.

      Binary proc b: edge_L + edge_R = 2*moves(b), both odd.
        2*moves(b) = odd + odd = even. Consistent.
        moves(b) = (edge_L + edge_R)/2. Since both >= 1: moves(b) >= 1.
        But moves(b) must be even >= 2 (binary parity + fairness).
        edge_L + edge_R = 2*moves(b) >= 4.
        Both odd, sum >= 4: minimum is (1,3) or (3,1).
        So each binary proc has >=1 edge with count >= 3.

      Non-binary proc p: edge_L + edge_R = 2*moves(p) >= 4 (fairness, moves >= 2).
        Both odd, so minimum (1,3).

      How many singletons can there be?
      If an edge has count 1, it contributes 1 to sum. If count >= 3, contributes >= 3.
      Let S = number of singleton edges, R = n - S non-singleton edges (each >= 3).
      L = S * 1 + sum(non-singleton counts) >= S + 3*(n-S) = 3n - 2S.
      So S >= (3n - L) / 2.
      Also L >= 2n (fairness: sum of moves >= 2n, and L = sum of moves).
      If L = 2n (minimum): S >= (3n - 2n)/2 = n/2.
      So at minimum length, at least n/2 edges are singletons. That's >= 2 for n >= 4.
      Tool 2 kills these!

      As L increases, S can decrease. S >= (3n - L)/2.
      S = 0 when L >= 3n. But S must be non-negative.
      For S <= 1: need L >= 3n - 2.
      For S = 0: need L >= 3n (but then W even since all edges >= 3 odd... wait,
        all edges odd and >= 3 is fine).
    """
    print(f"\n{'='*70}")
    print(f"Singleton edge counting: n={n}, k={k} binary procs")
    print(f"{'='*70}")

    print(f"\nCase W odd (all edge counts odd):")
    print(f"  L >= 2n = {2*n} (fairness)")
    print(f"  Let S = #singletons. Then L >= S + 3(n-S) = 3n - 2S")
    print(f"  => S >= (3n - L)/2")
    print(f"  For S <= 1: need L >= 3n - 2 = {3*n - 2}")
    print(f"  For S = 0: need L >= 3n = {3*n}")
    print(f"  At L = 2n: S >= n/2 = {n/2} => Tool 2 kills (>= 2 singletons)")

    # The critical regime is L >= 3n-2 where we might have <= 1 singleton.
    # For W odd: need L odd iff n odd (since L ≡ n mod 2 when all edges odd).

    print(f"\nCase W even (all edge counts even):")
    print(f"  All edges >= 2 (since even, positive => >= 2). 0 singletons.")
    print(f"  L >= 2n (fairness)")
    print(f"  Need to show binary-bounce (Tool 3) applies here.")

    # For W even: the issue is whether Tool 3 (binary-bounce) always applies.
    # Tool 3 needs: processor p, times t < u, p doesn't move in [t,u),
    # one neighbor q doesn't move in [t,u), other neighbor b is binary and
    # moves exactly twice in [t,u).

    # With 3 non-adjacent binary procs and even edge counts, can we always find
    # a binary-bounce witness?

    return


def product_budget_analysis(n, k):
    """
    Product budget: product < 4*3^(n-2).
    With k binary procs and (n-k) non-binary procs:
    product = 2^k * prod(m_i for non-binary i)
    < 4*3^(n-2) = 4 * 3^(n-2)

    So prod(m_i for non-binary) < 4 * 3^(n-2) / 2^k = 2^(2-k) * 3^(n-2)

    For k=3: prod(non-binary) < 3^(n-2) / 2
    For k=4: prod(non-binary) < 3^(n-2) / 4
    For k=5: prod(non-binary) < 3^(n-2) / 8

    Non-binary procs: each >= 3 (since they're not binary=2).
    Number of non-binary: n-k.
    Minimum product of n-k non-binary: 3^(n-k).

    Need: 3^(n-k) <= prod(non-binary) < 2^(2-k) * 3^(n-2)
    => 3^(n-k) < 2^(2-k) * 3^(n-2)
    => 3^(n-k-(n-2)) < 2^(2-k)
    => 3^(2-k) < 2^(2-k)
    => (3/2)^(2-k) < 1
    => 2-k < 0 (since 3/2 > 1)
    => k > 2. TRUE for k >= 3.

    So the budget is tight but satisfiable for k=3. All non-binary must be ternary (=3).
    For k >= 4: even tighter. Some non-binary could be >= 4 but budget very constrained.
    """
    print(f"\n{'='*70}")
    print(f"Product budget analysis: n={n}, k={k} binary procs")
    print(f"{'='*70}")

    threshold = 4 * 3**(n-2)
    binary_contribution = 2**k
    max_nonbinary_product = threshold / binary_contribution
    all_ternary_product = 3**(n-k)

    print(f"Threshold: 4*3^(n-2) = {threshold}")
    print(f"Binary contribution: 2^k = {binary_contribution}")
    print(f"Max non-binary product: {max_nonbinary_product:.1f}")
    print(f"All-ternary non-binary product: 3^(n-k) = {all_ternary_product}")
    print(f"Slack factor: {max_nonbinary_product / all_ternary_product:.4f}")

    if k == 3:
        # prod(non-binary) < 3^(n-2)/2
        # With n-3 non-binary procs, all ternary gives 3^(n-3).
        # 3^(n-3) < 3^(n-2)/2 = 3^(n-3) * 3/2. TRUE.
        # Can at most one be quaternary? 4*3^(n-4) < 3^(n-2)/2 = 3^(n-3)*3/2
        # 4*3^(n-4) vs 3^(n-2)/2: 4/3 vs 3/2: 4/3 < 3/2. So ONE quaternary allowed.
        # Can two be quaternary? 16*3^(n-5) vs 3^(n-2)/2: 16/9 vs 3/2: 16/9 > 3/2. NO.
        print(f"\nk=3: At most ONE non-binary can be quaternary (>=4).")
        print(f"  All-ternary: 3^{n-3} = {3**(n-3)} < {max_nonbinary_product:.1f} ✓")
        print(f"  One quaternary: 4*3^{n-4} = {4*3**(n-4)} < {max_nonbinary_product:.1f} {'✓' if 4*3**(n-4) < max_nonbinary_product else '✗'}")
        if n >= 5:
            print(f"  Two quaternary: {16*3**(n-5)} < {max_nonbinary_product:.1f} {'✓' if 16*3**(n-5) < max_nonbinary_product else '✗'}")

    if k >= 4:
        print(f"\nk={k}: All non-binary must be ternary.")
        print(f"  All-ternary: 3^{n-k} = {3**(n-k)} < {max_nonbinary_product:.1f} {'✓' if 3**(n-k) < max_nonbinary_product else '✗'}")
        if n > k:
            one_quat = 4 * 3**(n-k-1) if n-k >= 1 else float('inf')
            print(f"  One quaternary: {one_quat} < {max_nonbinary_product:.1f} {'✓' if one_quat < max_nonbinary_product else '✗'}")

    return max_nonbinary_product


def mover_count_constraints(n, k):
    """
    Analyze constraints on processor move counts.

    For a fair adjacent mover word:
    - moves(p) >= 2 for all p (fairness + no single-move from binary parity/determinism)
    - moves(b) is even for binary b (binary parity: start at 0, must return to 0)
    - L = sum of moves(p) for all p

    The mover word is a cyclic adjacent walk of length L on C_n.
    Winding number W = net number of clockwise traversals.
    All edges have count ≡ W (mod 2).
    """
    print(f"\n{'='*70}")
    print(f"Move count constraints: n={n}, k={k} binary procs")
    print(f"{'='*70}")

    # Minimum L:
    # All procs move exactly 2 times: L = 2n.
    # But adjacency constrains the walk. Can we always achieve L = 2n?
    # Bounce walk: 0,1,...,n-1,...,1,0 has length 2(n-1).
    # That visits endpoints once, not twice. Need fairness: each proc >= 2.
    # Actually bounce 0,1,...,n-1,...,1,0,1,...,n-1 = length 2(n-1) but not fair at 0.
    # Fair minimum: unclear, but L >= 2n is a lower bound.

    # For the singleton counting:
    # W odd case: S >= (3n - L)/2. Tool 2 kills when S >= 2, i.e., L <= 3n - 4.
    # For L >= 3n - 2: S <= 1, need Tool 3.
    # For L >= 3n: S = 0 (but still W odd possible with all counts >= 3 odd).

    # CRITICAL OBSERVATION for W odd, S <= 1:
    # Every edge has ODD count. Binary proc b has edge_L, edge_R both odd,
    # sum = 2*moves(b) >= 4. So at least one is >= 3.
    # If both >= 3: total >= 6, moves(b) >= 3. But moves(b) even, so moves(b) >= 4.
    # If one = 1 (singleton), other >= 3: moves(b) >= 2. moves(b) = 2 exactly
    # when edge_L=1, edge_R=3 or vice versa.

    print(f"\nW odd, L >= {3*n-2} (at most 1 singleton):")
    print(f"  Each binary proc: edge_L + edge_R = 2*moves(b), both odd")
    print(f"  If 0 singletons: all edges >= 3, L >= 3n = {3*n}")
    print(f"  If 1 singleton (at edge e*):")
    print(f"    e* touches two vertices. If e* is between procs p and p+1:")
    print(f"    One of p, p+1 has this as a 'light' edge.")

    # Now the key for Tool 3 (binary-bounce):
    # Need: binary proc b moves exactly 2 times in some interval [t,u),
    #        one neighbor of b doesn't move, other neighbor is the eventual mover.
    # Actually Tool 3 is more specific. Let me re-read.
    #
    # Tool 3: times t < u such that:
    #   - p is not the mover at time t
    #   - p IS the mover at time u
    #   - p doesn't move in [t,u)
    #   - one neighbor q doesn't move in [t,u)
    #   - other neighbor b is binary and moves exactly twice in [t,u)
    # => determinism contradiction (same context at t and u, different output).

    # So we need a TERNARY proc p adjacent to binary b, and in the interval [t,u)
    # where p and the other neighbor q are frozen, b bounces exactly twice.

    # When does this pattern arise?
    # If the walk visits b, then leaves to the other side, then comes back to b,
    # then comes back to p...

    # Actually, let me think about the W=0 (even, all edge counts even) case first.
    # This is the "bounce-like" regime.
    # All edge counts >= 2 (even, positive). No singletons.
    # The walk bounces back and forth. In a bounce walk, the binary-bounce
    # pattern is very natural.

    # For the W odd case with 0 singletons: all edges >= 3 (odd).
    # L >= 3n. Every proc moves >= 3 times. But binary must be even, so >= 4.
    # This makes L >= 4k + 3(n-k) = 3n + k.
    # Hmm, but non-binary could also move 3 times (odd).

    # Actually wait. moves(p) = (edge_L(p) + edge_R(p)) / 2? No that's wrong.
    # moves(p) = number of times p appears in the mover word.
    # edge_L(p) + edge_R(p) = 2 * moves(p) only holds if every appearance of p
    # has exactly one incoming and one outgoing edge traversal. In a cyclic walk
    # where each step crosses an edge, yes: appearance at position t means
    # w_{t-1} -> w_t crosses one edge (incoming) and w_t -> w_{t+1} crosses one edge (outgoing).
    # So: sum of edges touching p = 2 * moves(p). And the edges touching p are
    # exactly edge_L(p) and edge_R(p). So edge_L(p) + edge_R(p) = 2*moves(p). ✓

    # For binary b, moves(b) even >= 2.
    # edge_L(b) + edge_R(b) = 2*moves(b).
    # Both parities ≡ W mod 2.
    # W even: both even. Min (2,2), moves(b)=2.
    # W odd: both odd. Min (1,3) or (3,1), moves(b)=2.
    #         Or (3,3), moves(b)=3 — but moves(b) must be even! So moves(b) >= 4
    #         when both >= 3. (1,3): moves(b)=2. (1,5): moves(b)=3 NO. (3,5): moves(b)=4.
    #         Wait (1,3): sum=4, moves=2 ✓. (1,5): sum=6, moves=3. But moves must be even!
    #         So (1,5) is impossible for binary proc.
    #         Odd edge sums that are 2*even: 2*2=4 → (1,3) or (3,1).
    #                                        2*4=8 → (1,7),(3,5),(5,3),(7,1).
    #                                        etc.

    print(f"\n  For binary b with W odd and 0 singletons (all >= 3):")
    print(f"    edge_L + edge_R = 2*moves(b), both odd >= 3")
    print(f"    min sum = 6, moves(b) >= 3. But even => moves(b) >= 4")
    print(f"    Minimum binary moves when 0 singletons: 4")
    print(f"    Total L >= 4*{k} + 2*{n-k} = {4*k + 2*(n-k)} (non-binary min 2)")
    print(f"    But non-binary also odd edges => non-binary moves >= ... ")
    print(f"    Non-binary p: edge_L+edge_R = 2*moves(p), both odd.")
    print(f"    Minimum: (1,1) sum=2, moves=1. But fairness => moves >= 2.")
    print(f"    Next: (1,3) sum=4, moves=2. OK.")
    print(f"    So non-binary CAN have moves=2 with 0-singleton constraint")
    print(f"    if one of their edges is singleton... but we said 0 singletons.")
    print(f"    0 singletons => all >= 3. Non-binary: (3,3) min, moves=3.")
    print(f"    But non-binary moves needn't be even. moves=3 is fine.")
    print(f"    L >= 4*{k} + 3*{n-k} = {4*k + 3*(n-k)}")

    return


def singleton_edge_theorem(n, k):
    """
    THE MAIN THEOREM.

    Theorem: For n >= 5, k >= 3 pairwise non-adjacent binary procs,
    product < 4*3^(n-2), every fair adjacent mover word on C_n is killed.

    Proof strategy:

    Case A (W even, including W=0): All edge counts even, hence >= 2 if positive.
      No singletons possible. Need Tool 3 (binary-bounce).

    Case B (W odd): All edge counts odd.
      Sub-case B1 (L <= 3n-4): S >= (3n-L)/2 >= 2.
        Tool 2 (two-singleton-edge theorem) kills directly.

      Sub-case B2 (L >= 3n-2): S <= 1.
        Need Tool 3 for the 0 or 1 singleton case.

    Key question: does Tool 3 always apply in Cases A and B2?
    """
    print(f"\n{'='*70}")
    print(f"MAIN THEOREM STRUCTURE: n={n}, k={k}")
    print(f"{'='*70}")

    print(f"\nCase B1 (W odd, L <= {3*n-4}): >= 2 singletons => Tool 2 kills. ✓")
    print(f"\nCase A (W even) and Case B2 (W odd, L >= {3*n-2}): Need Tool 3.")

    # For Tool 3 to apply, we need to find a ternary proc p adjacent to binary b
    # with an interval [t,u) where:
    # - p doesn't move
    # - the other neighbor q of p doesn't move
    # - b moves exactly twice

    # Since binary procs are non-adjacent, each binary b has TWO non-binary neighbors.
    # At least one neighbor of b is not binary (they're non-adjacent, so both neighbors
    # are non-binary).

    # Consider a binary proc b with non-binary neighbors q_L and q_R.
    # b moves moves(b) times. Between consecutive moves of b, there are "gaps"
    # where b is stationary.

    # The walk visits b at moves(b) positions: t_1, t_2, ..., t_{moves(b)}.
    # Between t_i and t_{i+1} (cyclically), the walk is in a region NOT containing b.
    # Since the walk is adjacent, after leaving b it goes to q_L or q_R, and
    # must return to b via q_L or q_R.

    # In each gap between consecutive visits to b, the walk does an excursion
    # away from b and back. During this excursion, b doesn't move.

    # For binary-bounce at p (a neighbor of b), we need:
    # - An interval where p doesn't move, q (other neighbor of p from b) doesn't move,
    #   and b moves exactly twice.
    # So we need b to visit p's location, leave, come back (b bounces through p's edges).
    # Wait, p is a NON-MOVER in the interval. b is the one moving (bouncing).
    # p is adjacent to b. So p is a non-binary neighbor of b.

    # Let me restate Tool 3 in terms of the walk:
    # We need proc p (non-binary, adjacent to binary b) and interval [t,u):
    # At time t: mover ≠ p (p is non-mover)
    # At time u: mover = p
    # In [t,u): p doesn't appear as mover, q (other neighbor of p) doesn't appear,
    #           b appears exactly twice.
    # This means: in [t,u) the walk is in a region away from p and q, but visits b twice.

    # Hmm, but if b is adjacent to p, and the walk visits b, then the walk is
    # at b which is distance 1 from p. For p to not move in [t,u), the walk
    # must visit b and then go to b's other side (away from p) both times.

    # This is getting complex. Let me think about it differently.

    # KEY APPROACH: Instead of directly showing Tool 3 applies, show that
    # when W is even or W is odd with L >= 3n-2, the word MUST contain
    # a return cone (not via 2-singleton, but via a different structural argument)
    # OR a binary-bounce witness.

    # Actually, let me think about what happens at a binary processor with
    # moves(b) = 2 (the minimum even value).
    # b appears at positions t_1, t_2 in the word.
    # The walk arrives at b, does something, leaves. Then later arrives again and leaves.
    # Between the two visits (in both gaps), the walk is elsewhere.
    #
    # At time t_1: walk is at b. Previous mover was a neighbor of b (say q_L).
    #   After b moves, next mover is a neighbor of b (q_L or q_R).
    # At time t_2: same structure.
    #
    # Now consider the gap between t_1 and t_2 (the walk going from b to elsewhere and back).
    # Right after t_1: walk goes to some neighbor of b, does an excursion, comes back to b at t_2.
    # The excursion goes through one side of b.
    #
    # If the excursion goes through q_R (b's right neighbor), reaches some distance,
    # and comes back: all procs visited in this excursion are on the q_R side.
    # If some of them are binary and have exactly 2 moves total, and their
    # visits are both in this excursion... that's a potential return cone setup.

    # WAIT. Here's the simpler argument I should be making:

    # LEMMA: In a fair adjacent mover word on C_n with k >= 3 non-adjacent binary
    # procs, if moves(b) = 2 for some binary b, then either a return cone or
    # binary-bounce witness exists.
    #
    # Proof idea: b moves twice, at times t_1 < t_2.
    # The walk starts at b at t_1, exits to one side, does an excursion, returns at t_2.
    # Say it exits to q_R and returns from q_R (or from q_L).
    #
    # Case 1: exits to q_R, returns from q_R.
    #   The excursion visits some contiguous segment on the q_R side.
    #   Call this segment S. Every proc in S is visited only during [t_1, t_2).
    #   Before t_1: these procs haven't been visited (they're on the q_R side,
    #   and the walk hasn't gone there yet... WAIT this isn't necessarily true
    #   in a general cyclic walk.)

    # Hmm, the difficulty is that in a CYCLIC walk, the "before" and "after"
    # are relative. The walk wraps around.

    # Let me try the approach that GLB's computational results suggest should work.
    # The theorem should be:
    # "For k >= 3 non-adjacent binary procs, EVERY edge vector is killed."
    # This is what GLB verified length-by-length at n=9.
    # The counting argument should work for ALL lengths at once.

    print(f"\n--- Attempting the counting argument ---")

    # THE COUNTING ARGUMENT:
    #
    # Given: n procs, k >= 3 non-adjacent binary, cyclic adjacent mover word length L.
    # Winding number W. All edge counts ≡ W (mod 2).
    #
    # If W odd and L <= 3n-4: >= 2 singletons => Tool 2 kills. DONE.
    #
    # If W even: all edge counts even >= 0. Positive ones >= 2.
    #   The walk uses some subset of edges. Since all procs visited (fairness),
    #   the walk is connected and spans all vertices.
    #   But on C_n, you can span all vertices using only n-1 edges (a path).
    #   So at least one edge might have count 0.
    #
    #   With W=0 and all edges even: the walk has zero winding and bounces back and forth.
    #
    #   CLAIM: In this case, there exists a binary proc b and a gap interval where
    #   b moves exactly twice and a neighbor+its-other-neighbor don't move => Tool 3.
    #
    #   Why? Consider the "deepest penetration" of the walk on each side.
    #   Binary procs partition the ring into arcs. Each arc has >= 1 non-binary proc.
    #   The walk, with W=0, must bounce within each arc or across arcs.

    # I think the cleanest argument uses the NON-ADJACENCY + PRODUCT BUDGET.
    # The product budget forces ≥3 binary, and non-adjacency creates "gaps"
    # of ternary procs. The key structural fact:

    # STRUCTURAL FACT: In a fair adjacent walk on C_n, consider any binary proc b.
    # b has exactly 2 moves (in the minimum case). b's edges each have even count.
    # The edges of b sum to 2*2 = 4. So edges are (2,2) or (0,4) or (4,0).
    # If (0,4): all 4 edge traversals are on one side. Walk reaches b only from one direction.
    # If (2,2): walk reaches b from both sides, 2 times each way.

    # For a gap of size g (g non-binary procs between two binary procs b_i, b_{i+1}):
    # The g non-binary procs and g-1 interior edges + 2 binary-adjacent edges form a path.
    # The walk must traverse this path to visit the interior procs.
    # If W=0: each of the 2 binary-adjacent edges has even count >= 2.
    #         Each interior edge has even count >= 2 (all procs fair, path geometry).
    #         Total traversals in this gap path: >= 2*(g+1) edges * 2 = ...
    #         Actually there are g+1 edges in this gap (g-1 interior + 2 binary-adj).
    #         Each >= 2 traversals. Sum >= 2(g+1).
    #         These traversals contribute to moves of the g non-binary procs.
    #         Each non-binary proc in the gap has moves >= 2.
    #         L contribution from this gap >= 2*g (just from non-binary moves, not counting b_i, b_{i+1}).

    # I think the right approach is computational verification followed by
    # identifying the pattern. Let me write code to enumerate edge vectors
    # and check Tool 2 / Tool 3 applicability for general n and k.

    return


def enumerate_edge_vectors_small(n, k, gap_sizes, max_L=None):
    """
    Enumerate feasible edge vectors for small n and check singleton counts.

    Constraints:
    - n edges, all ≡ W (mod 2) for some W ∈ {0, 1}
    - For each binary proc b: edge_L(b) + edge_R(b) = 2*moves(b), moves(b) even >= 2
    - For each non-binary proc p: edge_L(p) + edge_R(p) = 2*moves(p), moves(p) >= 2
    - L = sum of all edge counts

    Focus: count singletons for each feasible vector.
    """
    if max_L is None:
        max_L = 4 * n  # reasonable upper bound for investigation

    print(f"\n{'='*70}")
    print(f"Edge vector enumeration: n={n}, k={k}, gaps={gap_sizes}")
    print(f"{'='*70}")

    # Build ring structure
    # Place binary procs at specific positions
    # Binary at positions: b_0=0, b_1=gap_sizes[0]+1, b_2=gap_sizes[0]+gap_sizes[1]+2, ...
    binary_positions = []
    pos = 0
    for i in range(k):
        binary_positions.append(pos)
        pos += 1 + gap_sizes[i]
    assert pos == n, f"Position sum {pos} != n={n}"

    is_binary = [False] * n
    for b in binary_positions:
        is_binary[b] = True

    print(f"Binary positions: {binary_positions}")
    print(f"Ring: {''.join('B' if is_binary[i] else 'T' for i in range(n))}")

    # For each parity W in {0, 1}, enumerate edge vectors
    for W_parity in [0, 1]:
        print(f"\n--- W parity = {W_parity} ---")

        singleton_histogram = Counter()
        total_vectors = 0

        # Edge counts: e_0, e_1, ..., e_{n-1} where e_i = count of edge (i, i+1 mod n)
        # All e_i ≡ W_parity (mod 2)
        # All e_i >= 0; if W_parity=0, positive ones >= 2; if W_parity=1, positive >= 1
        # Proc i: e_{i-1} + e_i = 2*moves(i), moves(i) >= 2 (moves even if binary)

        # Generate feasible edge vectors by constraint propagation
        # For small n, just enumerate within bounds
        if n > 9:
            print(f"  n={n} too large for exhaustive enumeration")
            continue

        min_edge = W_parity  # minimum nonzero edge count with correct parity
        if min_edge == 0:
            min_edge = 0  # edge can be 0 (even)

        # Maximum edge count per edge
        max_edge = max_L  # very loose bound

        # Generate candidates using valid values for each edge
        # Valid edge values: {0, 2, 4, ...} if W even, {1, 3, 5, ...} if W odd
        # Upper bounded by max_L

        valid_values = list(range(W_parity, max_L + 1, 2))

        # For tractability, limit range
        max_single_edge = min(max_L, 3*n)
        valid_values = [v for v in valid_values if v <= max_single_edge]

        # Check proc constraints for a given edge vector
        def is_feasible(edges):
            L = sum(edges)
            if L > max_L:
                return False
            for i in range(n):
                e_left = edges[(i - 1) % n]
                e_right = edges[i]
                total = e_left + e_right
                if total == 0:
                    return False  # proc i never visited
                moves_i = total // 2
                if total % 2 != 0:
                    return False
                if moves_i < 2:
                    return False  # fairness
                if is_binary[i] and moves_i % 2 != 0:
                    return False  # binary parity
            return True

        # For n <= 7, enumerate directly (too slow for n=9)
        if n <= 7:
            from itertools import product as iproduct
            count = 0
            for edges in iproduct(valid_values, repeat=n):
                if is_feasible(list(edges)):
                    L = sum(edges)
                    singletons = sum(1 for e in edges if e == 1)
                    singleton_histogram[singletons] += 1
                    total_vectors += 1
                    count += 1
            print(f"  Total feasible vectors: {total_vectors}")
            print(f"  Singleton histogram: {dict(sorted(singleton_histogram.items()))}")

            if 0 in singleton_histogram or 1 in singleton_histogram:
                print(f"  *** VECTORS WITH <= 1 SINGLETON EXIST ***")
                print(f"    0-singleton: {singleton_histogram.get(0, 0)}")
                print(f"    1-singleton: {singleton_histogram.get(1, 0)}")
            else:
                print(f"  All vectors have >= 2 singletons => Tool 2 kills all")
        else:
            # For larger n, sample or analyze theoretically
            print(f"  (Skipping exhaustive enumeration for n={n})")

    return


def binary_bounce_analysis(n, k, gap_sizes):
    """
    Analyze when Tool 3 (binary-bounce) applies.

    For each binary proc b with non-binary neighbors p_L, p_R:
    Tool 3 needs an interval [t,u) where:
    - some proc p (= p_L or p_R) doesn't move
    - p's OTHER neighbor q (the one that's not b) doesn't move
    - b moves exactly twice
    - p is the mover at time u, not at time t

    This means: in [t,u), the walk bounces through b (2 moves) without touching
    p or q. The walk must enter b from one side, go somewhere, come back to b,
    and then reach p.

    For this to work: p must be "between" two consecutive appearances
    of the walk where it's near b but doesn't visit p.

    Actually simpler: if b moves exactly 2 times total in the word,
    then the walk visits b twice. Between these visits, b is untouched.
    Consider the LAST time before a visit to p where b moved.
    If in [last_b_move, p_visit): b moved 0 times and p didn't move,
    that's not helpful (need b to move TWICE).

    Need: interval where b moves exactly twice.
    """
    print(f"\n{'='*70}")
    print(f"Binary-bounce analysis: n={n}, k={k}, gaps={gap_sizes}")
    print(f"{'='*70}")

    # For the general theorem, we need to show binary-bounce is ALWAYS available
    # when there are no singletons (or at most 1).

    # KEY INSIGHT from the walk structure:
    # Consider two adjacent binary procs... wait, they're NON-ADJACENT.
    # Consider a gap arc: b_i --- t_1 --- t_2 --- ... --- t_g --- b_{i+1}
    # where t_1, ..., t_g are non-binary (ternary) procs.
    # b_i and b_{i+1} are binary, gap size = g >= 1.
    #
    # In the walk, the mover must visit all of t_1, ..., t_g (fairness).
    # The walk enters this arc from b_i or b_{i+1} and exits similarly.
    #
    # For a gap of size 1: b_i --- t_1 --- b_{i+1}.
    #   t_1 has neighbors b_i and b_{i+1}, both binary.
    #   Tool 3 at p=t_1: need b_i or b_{i+1} to move exactly twice in [t,u)
    #   while t_1 and the other binary neighbor don't move.
    #
    #   Consider an interval where the walk goes b_i, t_1, b_{i+1}, ..., b_{i+1}, t_1
    #   During the "..." part (excursion away from t_1 through b_{i+1}):
    #   t_1 doesn't move. b_i doesn't move (it's on the other side, walk went right).
    #   b_{i+1} moves some number of times.
    #   If b_{i+1} moves exactly twice in this interval: binary-bounce at p=t_1!
    #
    #   But does b_{i+1} ALWAYS move exactly twice in some such interval?
    #   Not necessarily. It depends on the global walk structure.

    # BETTER APPROACH: Don't analyze the walk. Analyze the EDGE VECTOR.
    #
    # For an edge vector with 0 singletons and W even (all edges even >= 2):
    # Or W odd with L >= 3n-2 (0 or 1 singleton):
    # Can we ALWAYS find a binary-bounce configuration?

    # I think the answer requires more careful walk-level analysis.
    # Let me instead computationally verify the universal kill for small n.

    return


def computational_verification(n, gap_sizes):
    """
    Computationally verify that ALL mover words for Case 3c at given n are killed
    by Tool 2 or Tool 3. Enumerate all feasible mover words and check.
    """
    from itertools import product as iproduct

    k = len(gap_sizes)

    # Build ring
    binary_positions = []
    pos = 0
    for i in range(k):
        binary_positions.append(pos)
        pos += 1 + gap_sizes[i]
    assert pos == n

    is_binary = [False] * n
    for b in binary_positions:
        is_binary[b] = True

    print(f"\n{'='*70}")
    print(f"Computational verification: n={n}, k={k}, gaps={gap_sizes}")
    print(f"Binary positions: {binary_positions}")
    print(f"Ring: {''.join('B' if is_binary[i] else 'T' for i in range(n))}")
    print(f"{'='*70}")

    def generate_mover_words(max_L):
        """Generate all fair adjacent cyclic mover words up to length max_L."""
        # Use DFS to build adjacent walks that are cyclic (return to start)
        words = []

        def dfs(word, visited_counts):
            pos = word[-1]
            L = len(word)

            if L > max_L:
                return

            # Check if we can close the cycle (return to word[0])
            if L >= 2 * n:  # minimum possible length
                # Can we close? Need |pos - word[0]| <= 1 or ring wrap
                if abs(pos - word[0]) == 1 or abs(pos - word[0]) == n - 1:
                    # Check fairness: all procs visited >= 2
                    if all(c >= 2 for c in visited_counts):
                        # Check binary parity
                        if all(visited_counts[b] % 2 == 0 for b in binary_positions):
                            words.append(list(word))

            # Extend walk
            for next_pos in [(pos - 1) % n, (pos + 1) % n]:
                visited_counts[next_pos] += 1
                word.append(next_pos)
                dfs(word, visited_counts)
                word.pop()
                visited_counts[next_pos] -= 1

        # Start from each position (but by symmetry, can fix start = 0)
        visited = [0] * n
        visited[0] = 1
        dfs([0], visited)

        return words

    # For small n, enumerate all fair adjacent mover words
    max_L = 3 * n + 4  # cover the critical regime

    print(f"Enumerating mover words up to length {max_L}...")

    # This is too slow for DFS enumeration. Instead, analyze edge vectors.
    # For each feasible edge vector, check singleton count.

    # An edge vector (e_0, ..., e_{n-1}) determines the number of times each edge
    # is traversed. From it, we can compute moves(p) = (e_{p-1} + e_p) / 2.
    # Singletons = #{i : e_i = 1}.

    # Generate feasible edge vectors
    for W_parity in [0, 1]:
        print(f"\n--- W parity = {W_parity} ---")

        # Valid edge values
        if W_parity == 0:
            valid = [e for e in range(0, max_L+1, 2)]  # 0, 2, 4, ...
        else:
            valid = [e for e in range(1, max_L+1, 2)]  # 1, 3, 5, ...

        # Limit for tractability
        valid = [v for v in valid if v <= max_L]

        total_vectors = 0
        killed_by_tool2 = 0
        zero_singleton = 0
        one_singleton = 0

        # For n=5, enumerate all edge vectors
        if n <= 6:
            for edges in iproduct(valid, repeat=n):
                L = sum(edges)
                if L > max_L or L < 2*n:
                    continue

                # Check proc constraints
                feasible = True
                for i in range(n):
                    e_left = edges[(i-1) % n]
                    e_right = edges[i]
                    total = e_left + e_right
                    if total == 0:
                        feasible = False
                        break
                    moves_i = total // 2
                    if moves_i < 2:
                        feasible = False
                        break
                    if is_binary[i] and moves_i % 2 != 0:
                        feasible = False
                        break

                if not feasible:
                    continue

                total_vectors += 1
                singletons = sum(1 for e in edges if e == 1)

                if singletons >= 2:
                    killed_by_tool2 += 1
                elif singletons == 1:
                    one_singleton += 1
                else:
                    zero_singleton += 1

            print(f"  Total feasible vectors: {total_vectors}")
            print(f"  Killed by Tool 2 (>=2 singletons): {killed_by_tool2}")
            print(f"  1 singleton (need Tool 3): {one_singleton}")
            print(f"  0 singletons (need Tool 3): {zero_singleton}")

            if one_singleton > 0 or zero_singleton > 0:
                print(f"  *** {one_singleton + zero_singleton} vectors need Tool 3 ***")
            else:
                print(f"  ALL killed by Tool 2! ✓")

    return


def main():
    print("CIC Exploration 11: Return Cone kills Case 3c")
    print("=" * 70)

    # Part 1: Understand the edge parity constraint
    print("\n" + "=" * 70)
    print("PART 1: Edge Parity Analysis")
    print("=" * 70)

    # The fundamental constraint: all edges have the same parity (= W mod 2)
    # This means either ALL edges are even (no singletons possible)
    # or ALL edges are odd (singletons possible but constrained)

    # In the W-odd case:
    # S singletons + (n-S) non-singletons (each >= 3)
    # L >= S + 3(n-S) = 3n - 2S
    # S >= (3n - L) / 2
    #
    # For S >= 2: L <= 3n - 4.
    # L_min = 2n (fairness). At L=2n: S >= n/2 >= 3 for n >= 6.
    # At n=5, L=10: S >= 5/2 = 2.5, so S >= 3. Tool 2 kills.
    #
    # L <= 3n-4 is a HUGE range. For n=9: L <= 23. But minimum L = 18.
    # So for L in [18, 23], Tool 2 kills.
    # For L >= 25 (odd, since W odd): S <= 1.

    # WAIT. L must have the right parity too.
    # L = sum of edge counts. All edge counts ≡ W (mod 2).
    # L ≡ n * W (mod 2). So if W odd: L ≡ n (mod 2).
    # For n=9 (odd), W odd: L is odd. Minimum odd L with all procs >= 2: L >= 19?
    # No, L >= 2n = 18. But L must be odd. So L >= 19.
    # At L=19: S >= (27-19)/2 = 4. Tool 2 kills.
    # At L=21: S >= (27-21)/2 = 3. Tool 2 kills.
    # At L=23: S >= (27-23)/2 = 2. Tool 2 kills.
    # At L=25: S >= (27-25)/2 = 1. Could be 1. Need Tool 3.
    # At L=27: S >= 0. Could be 0. Need Tool 3.

    # This matches GLB's results! At n=9:
    # L=25: Tool 2 kills (every vector has >= 2 singletons)
    # L=27: Tool 2 kills (every vector has >= 2 singletons)
    # L=29: some vectors have 1 singleton, need Tool 3
    # L=33: first 0-singleton vectors appear

    # Wait, but my formula says L=25 could have 1 singleton (S >= 1).
    # GLB says L=25 has >= 2 singletons. Let me check more carefully.

    # At n=9, W odd, L=25:
    # S >= (3*9 - 25)/2 = (27-25)/2 = 1.
    # So S >= 1 is the bound. But GLB found >= 2 for all vectors.
    # The bound S >= (3n-L)/2 uses min non-singleton = 3. But binary procs
    # add extra constraints that INCREASE S beyond this generic bound.

    # Binary proc b: edge_L(b) + edge_R(b) = 2*moves(b), moves(b) even >= 2.
    # Both odd. If moves(b) = 2: edge_L + edge_R = 4. Options: (1,3), (3,1).
    # So one edge is singleton! Each binary proc with moves=2 contributes a singleton.
    # If moves(b) = 4: edge_L + edge_R = 8. Options: (1,7),(3,5),(5,3),(7,1).
    # Could have 0 singletons from this binary proc.

    # k binary procs. If ALL have moves = 2: k binary procs, each contributes 1 singleton.
    # Total S >= k >= 3. Tool 2 kills immediately!
    # So Tool 3 is only needed when some binary proc has moves >= 4.

    # Total binary moves >= 2k. If any has moves >= 4: total >= 2(k-1) + 4 = 2k+2.
    # Non-binary moves >= 2*(n-k).
    # L >= 2k + 2 + 2(n-k) = 2n + 2.
    # And the binary with moves >= 4 could have 0 singletons among its edges.
    # So S >= (k-1) from the other binary procs (each still moves=2 contributes 1).
    # k >= 3: S >= 2. Tool 2 still kills!

    # Wait, but the OTHER binary procs could also have moves >= 4.
    # If 2 binary procs have moves >= 4: total binary moves >= 2(k-2) + 8 = 2k+4.
    # Singletons from binary: >= k-2 >= 1 (for k=3).
    # So for k=3, if 2 binary procs have moves >= 4: S >= 1. Could be exactly 1.
    #
    # If ALL 3 binary procs have moves >= 4: total binary moves >= 12.
    # Non-binary moves >= 2(n-3). L >= 12 + 2(n-3) = 2n+6.
    # Singletons from binary: >= 0. Could be 0.

    # So the generic bound from binary alone:
    # Let j = number of binary procs with moves = 2 (contributing 1 singleton each).
    # Then: S >= j (from binary) + singletons from non-binary.
    # If j >= 2: Tool 2 kills. So critical case: j <= 1.
    # j = 0: all binary procs move >= 4.
    # j = 1: one binary moves = 2 (1 singleton from it), others move >= 4.

    # For j = 0 or 1, we need to understand the non-binary proc structure.

    print("\n*** BINARY MOVE COUNT AND SINGLETON ANALYSIS ***")
    print()
    print("Key insight: binary proc with moves(b)=2 (minimum) forces EXACTLY 1 singleton edge.")
    print("  Proof: edge_L + edge_R = 4, both odd => (1,3) or (3,1). One is singleton.")
    print()
    print("Let j = #{binary procs with moves=2}.")
    print("  j >= 2 => S >= 2 => Tool 2 kills. ✓")
    print("  j = 1 => S >= 1 from binary. Need additional singleton from non-binary for Tool 2,")
    print("           or Tool 3 for the 1-singleton case.")
    print("  j = 0 => All binary move >= 4. S could be 0. Need Tool 3.")
    print()

    # KEY CONSTRAINT from non-adjacency:
    # k >= 3 non-adjacent binary procs on C_n means k gaps, each >= 1.
    # n >= 2k (since k gaps of size >= 1 plus k binary procs).
    # For k = 3: n >= 6. But we're told n >= 5...
    # At n=5, k=3: gaps must sum to 2, with each >= 1. Only option: (1,1,0)?
    # No, non-adjacent means gap >= 1 between every pair. With k=3 on C_5:
    # positions 0,2,4: gaps (1,1,1) but that needs n=6.
    # positions 0,1,3: gap between 0,1 is 0 — ADJACENT! Not allowed.
    # So at n=5, k=3 non-adjacent is impossible? n >= 2k = 6 needed.
    # Hmm wait, for k=3 on C_n: need 3 gaps each >= 1 summing to n-3.
    # So n-3 >= 3, n >= 6.
    # The problem says n >= 5 but with >= 3 non-adjacent binary.
    # At n=5: max 2 non-adjacent binary (e.g., positions 0,2).
    # Case 3c (3 non-adjacent binary) requires n >= 6.

    # Actually the user said "pairwise non-adjacent" which means no two binary
    # procs are adjacent. For k=3 on C_5: need 3 procs with no two adjacent.
    # Maximum independent set on C_5 is 2 (it's an odd cycle). So k <= 2 at n=5.
    # At n=6: C_6 has max independent set 3. Positions 0,2,4. gaps (1,1,1). ✓
    # At n=7: max independent set 3. Various gap patterns.

    # So the theorem's domain is n >= 6 for k=3. But the user says n >= 5.
    # At n=5, Case 3c doesn't exist! The n=5 lower bound is handled differently.
    # At n >= 6, Case 3c with k=3 exists and needs this proof.

    # For n >= 9 specifically (the M_9 problem), k=3 with gaps summing to 6.

    print("Domain check: k=3 non-adjacent binary on C_n requires n >= 2k = 6.")
    print("At n=5: max 2 non-adjacent binary. Case 3c doesn't exist.")
    print("Theorem applies for n >= 6.")
    print()

    # Part 2: Computational verification for small n
    print("\n" + "=" * 70)
    print("PART 2: Computational Verification")
    print("=" * 70)

    # Test n=6, k=3, gaps=(1,1,1)
    computational_verification(6, [1, 1, 1])

    # Test n=7, k=3, gaps=(1,1,2)
    computational_verification(7, [1, 1, 2])

    # Test n=7, k=3, gaps=(1,2,1) — different orientation
    # Actually by ring symmetry this is equivalent to (1,1,2)

    # Test n=8, k=3
    computational_verification(8, [1, 1, 3])
    computational_verification(8, [1, 2, 2])

    # Part 3: Detailed analysis of the 0/1 singleton regime
    print("\n" + "=" * 70)
    print("PART 3: Critical Regime Analysis (j <= 1 binary with moves=2)")
    print("=" * 70)

    # When j <= 1 (at most 1 binary has moves=2):
    # j=0: ALL binary move >= 4. Binary move budget >= 12 (for k=3).
    # j=1: ONE binary moves=2, others >= 4. Budget >= 2+8 = 10.

    # Total L = binary_moves + nonbinary_moves >= binary_budget + 2*(n-k).
    # j=0: L >= 12 + 2(n-3) = 2n+6. For n=9: L >= 24.
    # j=1: L >= 10 + 2(n-3) = 2n+4. For n=9: L >= 22.

    # In W-odd case: L is odd (for n=9 odd).
    # j=0: L >= 25.
    # j=1: L >= 23.

    # At L=25, j=0: all binary move >= 4, all edges odd.
    # Binary b: edge_L + edge_R = 2*moves(b) >= 8. Both odd >= 3 (since 0 singletons from b).
    # Non-binary: edge_L + edge_R >= 4 (moves >= 2), both odd, so (1,3) or (3,1) possible.
    # Can non-binary edges be singletons? YES.
    #
    # How many singletons from non-binary?
    # S = total singletons = singletons from non-binary edges.
    # S >= (3n - L)/2 = (27-25)/2 = 1 (generic bound).
    # But with j=0 (all binary >= 4), the binary edges use more budget:
    # Binary edge total >= 8*3 = 24 (for k=3 binary procs, each using >= 8 edge units).
    # But binary edges are shared with non-binary neighbors!
    # edge_L(b) is also edge_R(left-neighbor-of-b).
    # So the total is constrained by the ring.

    # L = sum of edge counts = sum over edges.
    # Binary-adjacent edges (2k=6 for k=3): each is shared between a binary and non-binary.
    # Interior edges (n-2k): between two non-binary.
    #
    # Let a_i = binary-adjacent edge count, r_j = interior edge count.
    # Sum(a_i) + Sum(r_j) = L.
    # For each binary b: two adjacent edges with sum 2*moves(b).
    # k=3: 6 binary-adjacent edges, 3 binary procs, each "owning" 2 adjacent edges.
    # If all 3 binary procs have moves >= 4: sum of 6 binary-adjacent edges >= 3*8 = 24.
    # But wait, the 6 binary-adjacent edges are DISTINCT (since binary procs are non-adjacent).
    # So sum(a_i for i in 1..6) >= 24.
    # Interior edges: n-6 edges (for k=3). Each >= 1 (W odd, but could be 1 = singleton).
    # L = sum(a_i) + sum(r_j) >= 24 + (n-6)*1 = n + 18.
    # For n=9: L >= 27.

    # WAIT. That's powerful. If j=0 (all binary move >= 4), then L >= n + 18.
    # For n=9: L >= 27. At L=25: j=0 is IMPOSSIBLE.
    # So at L=25 (W odd), j >= 1. If j >= 2: Tool 2 kills.
    # If j = 1: exactly 1 singleton from binary. Need to check non-binary singletons.
    # L = 25. Binary moves: 2 + 4 + 4 = 10 (one moves=2, two move=4).
    # Binary-adjacent edge sum: 4 + 8 + 8 = 20.
    # Remaining for interior: 25 - 20 = 5.
    # Interior edges: n-6 = 3 (for n=9). Each odd >= 1. Sum = 5.
    # Options: (1,1,3), (1,3,1), (3,1,1).
    # Singletons from interior: 2 in each case.
    # Total singletons: 1 (from binary) + 2 (from interior) = 3 >= 2. Tool 2 kills!

    # So at L=25, n=9: ALL cases are killed by Tool 2!

    print(f"\n*** L=25, n=9, W odd analysis ***")
    print(f"If j=0 (all binary move >= 4): binary-adjacent edge sum >= 24.")
    print(f"  Interior sum >= n-6 = 3. Total L >= 27. Contradiction with L=25.")
    print(f"  So j=0 impossible at L=25. ✓")
    print(f"If j=1: binary-adj sum = 4 + 8 + 8 = 20. Interior sum = 5.")
    print(f"  Interior: 3 edges, all odd, sum 5. Must be (1,1,3) or perms.")
    print(f"  Singletons: 1(binary) + 2(interior) = 3 >= 2. Tool 2 kills. ✓")
    print(f"If j=2: S >= 2 from binary alone. Tool 2 kills. ✓")
    print(f"If j=3: S >= 3. Tool 2 kills. ✓")
    print()

    # L=27, n=9, W odd:
    # j=0: binary-adj sum >= 24. Interior sum = 27-24 = 3. 3 edges, each odd >= 1.
    #       Options: (1,1,1). All singletons! S = 3 >= 2. Tool 2 kills. ✓
    # j=1: binary-adj sum = 4 + 8 + 8 = 20. Interior = 7.
    #       3 edges, odd, sum 7. (1,1,5),(1,3,3),(1,5,1),(3,1,3),(3,3,1),(5,1,1).
    #       Singletons: 1(binary) + 2,0,2,0,0,2 = varies.
    #       (1,3,3): S = 1+1 = 2 >= 2. Tool 2 kills.
    #       Wait, (1,3,3) has 1 singleton from interior + 1 from binary = 2. ✓
    #       (3,3,1): same. (3,1,3): 1+1 = 2. ✓
    #       (1,1,5): 2+1 = 3. ✓
    #       All have >= 2. Tool 2 kills. ✓
    # j=2: binary-adj sum = 4+4+8 = 16. Interior = 11.
    #       3 edges, odd, sum 11. Many options but S >= 2 from binary. ✓
    # j=3: S >= 3. ✓

    print(f"*** L=27, n=9, W odd analysis ***")
    print(f"j=0: binary-adj >= 24, interior = 3, must be (1,1,1). S=3. Tool 2. ✓")
    print(f"j=1: binary-adj = 20, interior = 7. 3 odd edges summing to 7.")
    print(f"  Minimum singletons from interior when 1 edge = 1: 1.")
    print(f"  Total S >= 1(binary) + 1(interior) = 2. Tool 2. ✓")
    print(f"  Actually need to check: can all 3 interior edges be >= 3?")
    print(f"  3 odd edges >= 3 each: sum >= 9 > 7. Impossible! So >= 1 interior singleton.")
    print(f"  S >= 1+1 = 2. Tool 2. ✓")
    print(f"j>=2: S >= 2. ✓")
    print()

    # L=29, n=9, W odd:
    # j=0: binary-adj >= 24. Interior = 29-24 = 5. 3 edges, odd, sum 5.
    #       (1,1,3), (1,3,1), (3,1,1). S = 2 interior + 0 binary = 2. ✓
    #       Can we have binary-adj sum > 24? Yes, e.g., 26 or 28.
    #       If binary-adj = 26: interior = 3. (1,1,1). S = 3. ✓
    #       If binary-adj = 28: interior = 1. One edge = 1.
    #         But 3 interior edges exist, so need 1+0+0=1 BUT edges are odd, so
    #         0 is not allowed (W odd)! Min is 1. So 1+1+... wait, 3 edges sum to 1?
    #         Impossible (each >= 1, sum >= 3). So binary-adj <= 29-3 = 26.
    #       binary-adj = 24: interior = 5. S_interior >= 2 (since 3 odd edges sum 5: max non-singleton=3,
    #         so at most 1 edge >= 3, leaving 2 edges of sum 2, so (1,1): 2 singletons). ✓
    #       binary-adj = 26: interior = 3. All singletons. S = 3. ✓
    #       So j=0 with L=29: S >= 2. Tool 2 kills. ✓
    # j=1: binary-adj sum = 20 + extra from one binary moving more.
    #       Actually j=1 means one binary moves=2 (edges 1,3 or 3,1), others move >= 4 (edges sum >= 8).
    #       binary-adj from j=1 binary: 4. From other two: >= 16. Total >= 20.
    #       Interior = L - binary-adj <= 29-20 = 9.
    #       3 odd edges sum to 9. (3,3,3): S_interior = 0. S_total = 1. Hmm.
    #       (1,3,5): S_interior = 1. S_total = 2. ✓
    #       (3,3,3): S_interior = 0. S_total = 1.
    #       THIS IS THE ONE-SINGLETON CASE that GLB had to handle with Tool 3!

    print(f"*** L=29, n=9, W odd analysis ***")
    print(f"j=0: binary-adj >= 24, interior <= 5, 3 odd edges sum <= 5.")
    print(f"  Can't all be >= 3 (sum >= 9 > 5). S_interior >= 2. S >= 2. Tool 2. ✓")
    print(f"j=1: binary-adj >= 20, interior <= 9. 3 odd edges sum <= 9.")
    print(f"  (3,3,3) possible: S_interior=0, S_total=1. ONE-SINGLETON CASE.")
    print(f"  This is where Tool 3 (binary-bounce) is needed!")
    print(f"j>=2: S >= 2. ✓")
    print()

    # NOW: the general formula.
    # For general n, k=3, W odd:
    # j = #{binary with moves=2}. Let j_4 = 3 - j = #{binary with moves >= 4}.
    # binary-adj edges: j binary each contribute 4, j_4 each contribute >= 8.
    # Total binary-adj >= 4j + 8(3-j) = 24 - 4j.
    # Interior edges: n - 6, each odd >= 1.
    # L = binary-adj + interior. Interior = L - binary-adj <= L - (24-4j).
    # Interior singletons: 3 interior edges each >= 1. Non-singletons >= 3.
    # If interior sum = I, singletons among them >= max(0, ceil((3*3 - I)/2))...
    # Actually: (n-6) edges, each odd >= 1. Sum = I.
    # Non-singletons >= 3, so count of non-singletons * 3 + singletons * 1 <= I.
    # singletons + non-singletons = n-6.
    # non-singletons * 3 + singletons <= I.
    # non-singletons * 3 + singletons <= I.
    # 3(n-6-singletons) + singletons <= I.
    # 3(n-6) - 2*singletons <= I.
    # singletons >= (3(n-6) - I) / 2.

    # Total singletons: S >= j + max(0, (3(n-6) - I) / 2)
    # where I = L - binary-adj <= L - (24-4j).
    # S >= j + max(0, (3n-18 - L + 24 - 4j) / 2)
    # = j + max(0, (3n + 6 - L - 4j) / 2)

    # For S >= 2: j + (3n+6-L-4j)/2 >= 2
    # 2j + 3n+6-L-4j >= 4
    # 3n+6-L-2j >= 4
    # L <= 3n+2-2j.

    # So: S >= 2 when L <= 3n + 2 - 2j (in the W odd regime).
    # j=0: L <= 3n+2. So for ALL L in W-odd regime, S >= 2!
    # Wait that can't be right. Let me recheck.

    # j=0: binary-adj >= 24. Interior = L-24 (at least).
    # Actually binary-adj could be > 24 (if binary procs move 6, 8, ...).
    # The tighter bound: binary-adj >= 24, so interior <= L-24.
    # Interior singletons >= (3(n-6) - (L-24)) / 2 = (3n-18-L+24)/2 = (3n+6-L)/2.
    # For this to be >= 0: L <= 3n+6.
    # For n=9: 3*9+6 = 33. So for L <= 33 (odd): interior singletons >= (33-L)/2.
    # L=25: >= 4. L=27: >= 3. L=29: >= 2. L=31: >= 1. L=33: >= 0.
    # Total S = 0(from binary) + interior singletons.
    # L=29, j=0: S >= 2. Tool 2. ✓
    # L=31, j=0: S >= 1. Could be 1. Need Tool 3.
    # L=33, j=0: S >= 0. Could be 0. Need Tool 3.

    # j=1: binary-adj >= 20. Interior <= L-20.
    # Interior singletons >= (3(n-6) - (L-20))/2 = (3n-18-L+20)/2 = (3n+2-L)/2.
    # Total S >= 1 + (3n+2-L)/2.
    # For S >= 2: 1 + (3n+2-L)/2 >= 2. (3n+2-L)/2 >= 1. L <= 3n.
    # For n=9: L <= 27. So at L <= 27, j=1: S >= 2. ✓
    # At L=29, j=1: interior singletons >= (29-29)/2 = 0. S >= 1. Could be 1. Need Tool 3.
    # At L=31, j=1: interior singletons >= (29-31)/2 < 0. S >= 1 (from binary). Could be 1.

    # j=2: S >= 2 from binary alone. Tool 2 always kills. ✓
    # j=3: S >= 3. ✓

    # SUMMARY for n=9, W odd, k=3:
    # L=25: j=0 impossible (L too small), j >= 1 → S >= 2. Tool 2. ✓
    # L=27: j=0 → S >= 3, j=1 → S >= 2, j>=2 → S >= 2. All Tool 2. ✓
    # L=29: j=0 → S >= 2 ✓; j=1 → S >= 1 (ONE-SINGLETON: need Tool 3); j>=2 → S >= 2 ✓
    # L=31: j=0 → S >= 1 (need Tool 3); j=1 → S >= 1 (need Tool 3); j>=2 ✓
    # L=33: j=0 → S >= 0 (need Tool 3); j=1 → S >= 1 (need Tool 3); j>=2 ✓
    # L >= 35: j=0 → S could be 0; j=1 → S could be 1; j>=2 ✓

    # The 0/1 singleton regime starts at L = 3n - 2 = 25 for n=9.
    # Wait, the generic bound was S >= (3n-L)/2, which gives S >= 1 at L=25.
    # But the REFINED bound (using binary structure) gives S >= 2 at L=25 (since j=0 impossible).
    # The refined critical threshold is later.

    # GENERAL n, k=3, W odd:
    # Tool 2 kills when S >= 2.
    # j=0: S >= (3(n-6) - (L-24))/2 = (3n+6-L)/2. S >= 2 when L <= 3n+2.
    # j=1: S >= 1 + (3n+2-L)/2. S >= 2 when L <= 3n.
    # j=2: S >= 2 always. ✓
    # j=3: S >= 3 always. ✓
    #
    # Combined: Tool 2 fails only when:
    #   (j=0 and L >= 3n+4) or (j=1 and L >= 3n+2)
    # But wait, we need L to be achievable.
    # j=0: binary-adj >= 24, interior >= n-6. L >= 24 + n - 6 = n + 18.
    #       Binary moves >= 12, non-binary >= 2(n-3). L >= 12+2n-6 = 2n+6.
    #       For n >= 9: L >= 24. And L <= ... (no upper bound from constraints alone).
    #
    # Hmm actually I realize there IS an upper bound from the product budget.
    # The product budget limits how many states each proc has, which limits
    # how many distinct contexts are available, which limits the cycle length.
    # But this is harder to use directly.

    # Let me instead focus on proving Tool 3 works for the critical cases.

    print(f"\n{'='*70}")
    print(f"GENERAL FORMULA (n procs, k=3 non-adjacent binary, W odd)")
    print(f"{'='*70}")
    for n_val in range(6, 15):
        print(f"\nn={n_val}:")
        # j=0 threshold
        threshold_j0 = 3*n_val + 2
        # j=1 threshold
        threshold_j1 = 3*n_val
        # j=0 minimum L
        min_L_j0 = 2*n_val + 6
        # j=0 impossible when L < n_val + 18
        impossible_j0 = n_val + 18

        print(f"  j=0: Tool 2 kills for L <= {threshold_j0}. Min L = {min_L_j0}.")
        if min_L_j0 > threshold_j0:
            print(f"    j=0 always killed by Tool 2! (min L > threshold)")
        else:
            print(f"    Tool 3 needed for L >= {threshold_j0 + 2} (odd)")

        print(f"  j=1: Tool 2 kills for L <= {threshold_j1}. Min L = {2*n_val+4}.")
        if 2*n_val+4 > threshold_j1:
            print(f"    j=1 always killed by Tool 2!")
        else:
            print(f"    Tool 3 needed for L >= {threshold_j1 + 2} (odd)")

        print(f"  j>=2: Tool 2 always kills. ✓")

    # Part 4: W even case
    print(f"\n{'='*70}")
    print(f"PART 4: W even case (all edges even, 0 singletons)")
    print(f"{'='*70}")
    print(f"All edges even >= 2 (since visited). 0 singletons.")
    print(f"Tool 2 doesn't apply (need >= 2 singletons).")
    print(f"Need Tool 3 (binary-bounce) for ALL W-even words.")
    print()
    print(f"W=0 includes bounce-type walks. W=2,4,... includes multi-winding walks.")
    print(f"For W even, L ≡ 0 (mod 2) when n even, L ≡ 0 (mod 2) when n odd... ")
    print(f"Actually L = sum of edges, all even, so L is always even when W even.")
    print(f"Minimum L = 2n (all edges = 2, W=0).")

    # Part 5: The binary-bounce universal argument
    print(f"\n{'='*70}")
    print(f"PART 5: Binary-Bounce Universal Argument")
    print(f"{'='*70}")

    # For Tool 3 to apply at processor p (non-binary, adjacent to binary b):
    # Need interval [t,u) where p=mover at u, p frozen in [t,u),
    # neighbor q of p (not b) frozen in [t,u), b moves exactly twice in [t,u).

    # Consider processor p adjacent to binary b, with other neighbor q.
    # In the mover word, p appears at some positions. Between two consecutive
    # appearances of p (say at times s and u with s < u), p is frozen in (s,u).
    # We need q also frozen in this interval AND b moves exactly twice.

    # The walk from position s to u: starts at p, goes to neighbors, eventually returns to p.
    # Since p is frozen in (s,u), the walk leaves p and comes back.
    # The walk exits p via b or q. It returns via b or q.

    # Case: walk exits via b at s+1, returns via b at u-1.
    #   In [s+1, u-1], the walk is in the "b-side" of the ring (away from q).
    #   q is NOT visited in [s+1, u-1] (since the walk is on the other side and
    #   must cross p to reach q, but p doesn't move).
    #   Wait, the walk is on C_n, and p separates q from b only if the ring
    #   is split at p. But C_n is a cycle, so there are two paths from q to
    #   the b-side. One goes through p, the other goes around the ring.
    #   So q COULD be visited by going the long way around, NOT through p.

    # Hmm, this complicates things. The non-adjacency of binary procs creates
    # multiple arcs. Let me think about gap structure.

    # With k=3 binary procs at positions b_0, b_1, b_2 (non-adjacent on C_n):
    # Three arcs: arc_0 = (b_0, ..., b_1), arc_1 = (b_1, ..., b_2), arc_2 = (b_2, ..., b_0).
    # Each arc has gap_i >= 1 non-binary procs.

    # Consider p = neighbor of b_0 in arc_0 (i.e., p is the first non-binary proc after b_0).
    # p's neighbors: b_0 and the next proc in arc_0 (call it q).
    # For Tool 3 at p: need b_0 to move exactly twice while p and q are frozen.
    # The walk must visit b_0 twice (b_0's moves) without visiting p or q in between.
    # Since p and q are on the same side of b_0 (both in arc_0), and the walk
    # must avoid both, it must stay on the OTHER side of b_0 (arc_2 side).
    # But the walk can also go through b_0 and out the arc_2 side and around.

    # This is getting complicated. The key question is whether the walk can
    # AVOID creating a binary-bounce witness at ANY of the 2k neighbors of binary procs.

    # Actually, let me think about this more abstractly.
    # Each binary proc b has 2 non-binary neighbors. If gap = 1, then the neighbor
    # on each side is also adjacent to another binary proc.

    # CRITICAL OBSERVATION for gap = 1:
    # Arc: b_i -- t -- b_{i+1} (one non-binary proc between two binary procs).
    # t has neighbors b_i and b_{i+1}, BOTH binary.
    # For Tool 3 at p=t: need one of b_i, b_{i+1} to move exactly twice
    # while t and the other binary don't move.
    # If b_i moves exactly twice in some interval where t and b_{i+1} don't move:
    # binary-bounce at t.

    # In a gap-1 arc, t is sandwiched between two binary procs.
    # Consider the mover word restricted to {b_i, t, b_{i+1}}.
    # t must appear >= 2 times. b_i appears an even number >= 2 times. Same for b_{i+1}.
    # Between consecutive appearances of t (when t is frozen), the walk
    # must stay on one or both sides of t. But to reach the other side of t,
    # the walk must go through t (which is frozen) or around the entire ring.
    # Going around the ring is possible but uses many steps.

    # FOR THE SIMPLEST CASES, let me just prove the binary-bounce for gap-1 arcs.

    print(f"\nGap-1 arc: b_i -- t -- b_{{i+1}}")
    print(f"t has TWO binary neighbors. Consider interval between consecutive t-appearances.")
    print(f"Walk exits t to b_i or b_{{i+1}}, returns from b_i or b_{{i+1}}.")
    print(f"")
    print(f"Sub-case: exit to b_i, return from b_i (walk stays on b_i side).")
    print(f"  b_{{i+1}} doesn't move (walk doesn't reach it without passing t).")
    print(f"  ... unless walk goes all the way around the ring.")
    print(f"  If b_i moves exactly 2 times: binary-bounce! Tool 3 kills.")
    print(f"  If b_i moves != 2 times in this interval: need to check other intervals.")

    # The issue is that in any single gap-between-t-moves, b_i might move
    # more or fewer than 2 times, and the walk might go around the ring.

    # I think the cleanest approach is to prove the result computationally for
    # moderate n (say n=6..15) and then identify the structural pattern.
    # Let me write a more targeted computational check.

    return


def binary_bounce_walk_check(n, gap_sizes, max_L):
    """
    For given ring structure, generate ALL fair adjacent cyclic mover words
    up to length max_L and check if each is killed by Tool 2 or Tool 3.

    Tool 2: >= 2 singleton edges.
    Tool 3: exists processor p adjacent to binary b, interval [t,u) where
            p doesn't move, q (other neighbor) doesn't move, b moves exactly twice.
    """
    k = len(gap_sizes)
    binary_positions = []
    pos = 0
    for i in range(k):
        binary_positions.append(pos)
        pos += 1 + gap_sizes[i]
    assert pos == n

    is_binary = set(binary_positions)

    print(f"\n{'='*70}")
    print(f"Binary-bounce walk check: n={n}, gaps={gap_sizes}, max_L={max_L}")
    print(f"Binary at: {binary_positions}")
    print(f"{'='*70}")

    def has_tool3_witness(word):
        """Check if word has a binary-bounce witness (Tool 3)."""
        L = len(word)
        # For each non-binary proc p adjacent to a binary proc b:
        for b in binary_positions:
            for p in [(b-1) % n, (b+1) % n]:
                if p in is_binary:
                    continue  # p must be non-binary
                q = (p - 1) % n if (p + 1) % n == b else (p + 1) % n  # other neighbor of p

                # Find all intervals [t, u) where p is frozen
                positions_of_p = [i for i in range(L) if word[i] == p]
                if len(positions_of_p) < 2:
                    continue

                for idx in range(len(positions_of_p)):
                    t_start = positions_of_p[idx]  # p moves here
                    u_end = positions_of_p[(idx + 1) % len(positions_of_p)]  # p moves here next

                    # Interval is (t_start, u_end) cyclically — p frozen in this interval
                    # Actually Tool 3 needs: p is NOT mover at t, IS mover at u.
                    # So the interval [t, u) where t is some time after p's last move
                    # and u is the next time p moves.
                    # Let's use: t can be any time in the frozen interval, u = next p-move.

                    # Build the interval (t_start+1, ..., u_end-1) cyclically
                    interval_movers = []
                    pos_t = (t_start + 1) % L
                    while pos_t != u_end:
                        interval_movers.append(word[pos_t])
                        pos_t = (pos_t + 1) % L

                    # Check: q doesn't move in this interval
                    if q in interval_movers:
                        # q moves in this interval. But we might be able to find
                        # a sub-interval. Actually Tool 3 needs the FULL interval
                        # where BOTH p and q are frozen and b moves exactly twice.
                        # Let's check all sub-intervals where both p and q are frozen.

                        # Find positions of q in the interval
                        q_positions_in_interval = [i for i, m in enumerate(interval_movers) if m == q]

                        # Split interval at q positions and check each sub-interval
                        boundaries = [-1] + q_positions_in_interval + [len(interval_movers)]
                        for bi in range(len(boundaries) - 1):
                            start = boundaries[bi] + 1
                            end = boundaries[bi + 1]
                            sub_interval = interval_movers[start:end]
                            b_count = sub_interval.count(b)
                            if b_count == 2:
                                # Also need: at the start of this sub-interval,
                                # p is not the mover. Since p is frozen in the
                                # whole interval, p is not the mover. ✓
                                # And at the end, p is... well we need p to be
                                # the mover at u. If this sub-interval ends at u_end,
                                # then p moves at u_end. Otherwise, this sub-interval
                                # ends at a q-move, and we need the NEXT move of p.
                                #
                                # Actually the Tool 3 statement is:
                                # "there exist times t < u such that..."
                                # So t can be any time in the sub-interval, and u can be
                                # the next time p moves after the sub-interval.
                                # The key is: p and q are frozen in [t,u), b moves exactly twice.
                                # If the sub-interval has b moving twice and neither p nor q moving,
                                # and there exists a time t in this interval where p is not the mover,
                                # and u (the next p move) is after the interval:
                                # Then [t, u) contains exactly 2 b-moves, 0 p-moves, 0 q-moves.
                                # Choose t = start of sub-interval, u = u_end (or next p move).
                                # But we need b to move EXACTLY twice in [t,u). If u is beyond
                                # the sub-interval, b might move more times between end of
                                # sub-interval and u.

                                # Simpler: if in the sub-interval b moves exactly 2 times,
                                # and the sub-interval ends RIGHT before p moves (i.e., this
                                # sub-interval goes up to u_end), then [t, u_end) has exactly
                                # 2 b-moves, 0 p-moves, 0 q-moves. ✓

                                if end == len(interval_movers):
                                    # Sub-interval reaches u_end. Tool 3 applies!
                                    return True
                        continue

                    # q doesn't move in the entire interval [t_start+1, u_end-1]
                    b_count = interval_movers.count(b)
                    if b_count == 2:
                        return True

        return False

    def has_tool2_witness(word):
        """Check if word has >= 2 singleton edges."""
        L = len(word)
        edge_counts = Counter()
        for i in range(L):
            e = (min(word[i], word[(i+1) % L]), max(word[i], word[(i+1) % L]))
            # Handle ring wrap
            if abs(word[i] - word[(i+1) % L]) > 1:
                e = (min(word[i], word[(i+1) % L]), max(word[i], word[(i+1) % L]))
                # Ring edge: (0, n-1) or (n-1, 0)
                e = (0, n-1) if set([word[i], word[(i+1)%L]]) == set([0, n-1]) else e
            edge_counts[e] += 1
        singletons = sum(1 for c in edge_counts.values() if c == 1)
        return singletons >= 2

    # Generate mover words by DFS
    total_words = 0
    killed_tool2 = 0
    killed_tool3_only = 0
    survivors = []

    def dfs(word, move_counts):
        nonlocal total_words, killed_tool2, killed_tool3_only

        L = len(word)
        if L > max_L:
            return

        current = word[-1]

        # Try to close cycle
        if L >= 2 * n:
            first = word[0]
            if abs(current - first) == 1 or abs(current - first) == n - 1:
                # Check fairness and binary parity
                fair = all(c >= 2 for c in move_counts)
                binary_ok = all(move_counts[b] % 2 == 0 for b in binary_positions)
                if fair and binary_ok:
                    total_words += 1
                    if has_tool2_witness(word):
                        killed_tool2 += 1
                    elif has_tool3_witness(word):
                        killed_tool3_only += 1
                    else:
                        survivors.append(list(word))
                        if len(survivors) <= 5:
                            print(f"  SURVIVOR: {word}")

        # Extend
        for next_p in [(current - 1) % n, (current + 1) % n]:
            move_counts[next_p] += 1
            word.append(next_p)
            dfs(word, move_counts)
            word.pop()
            move_counts[next_p] -= 1

    # Start from position 0 (WLOG by rotational symmetry of the word,
    # but we want all words starting from 0)
    move_counts = [0] * n
    move_counts[0] = 1
    dfs([0], move_counts)

    print(f"\nTotal fair adjacent cyclic words (starting at 0): {total_words}")
    print(f"Killed by Tool 2 (>= 2 singletons): {killed_tool2}")
    print(f"Killed by Tool 3 only (binary-bounce): {killed_tool3_only}")
    print(f"Survivors: {len(survivors)}")

    if survivors:
        print(f"\n*** {len(survivors)} SURVIVORS FOUND! ***")
        for w in survivors[:10]:
            print(f"  {w}")
    else:
        print(f"\nALL WORDS KILLED by Tool 2 or Tool 3. ✓")

    return len(survivors)


if __name__ == "__main__":
    main()

    print("\n" + "=" * 70)
    print("PART 6: Walk-level computational verification")
    print("=" * 70)

    # n=6, k=3, gaps=(1,1,1): BTBTBT
    binary_bounce_walk_check(6, [1, 1, 1], max_L=22)

    # n=7, k=3, gaps=(1,1,2): BTBTBTT
    binary_bounce_walk_check(7, [1, 1, 2], max_L=24)
