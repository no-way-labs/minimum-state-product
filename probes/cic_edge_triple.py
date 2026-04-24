#!/usr/bin/env python3
"""CIC Exploration 2: Edge-Triple Lemma Investigation.

Key question: With ≥3 binary and ≤3 consecutive, does the adjacent-mover
walk structure + No Binary 2-Cycle force the state vector to be
ms=(2,3,...,3,2)?

Approach: Analyze what happens at a binary triple (3 consecutive binary).
The middle binary has only 8 contexts. Count constraints from the walk.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict


def analyze_binary_triple_walk():
    """Analyze constraints on a binary triple in an adjacent-mover walk.

    Positions: ..., a-1, a, a+1, a+2, a+3, ...
    Binary triple: a, a+1, a+2 all have m=2
    Adjacent-mover walk passes through this triple.
    """
    print("=" * 70)
    print("BINARY TRIPLE ANALYSIS")
    print("=" * 70)
    print()

    # The middle binary a+1 has neighbors a (binary) and a+2 (binary)
    # Contexts: (c[a], S, c[a+2]) where c[a], S, c[a+2] ∈ {0,1}
    # 8 total contexts

    # By No Binary 2-Cycle Lemma, each (L,R) is UP, DOWN, or NEUTRAL:
    # (0,0): UP, DOWN, or NEUTRAL
    # (0,1): UP, DOWN, or NEUTRAL
    # (1,0): UP, DOWN, or NEUTRAL
    # (1,1): UP, DOWN, or NEUTRAL

    # In the good cycle walk, the middle processor a+1 is visited as mover
    # multiple times. Each visit has specific (L,R) context and direction
    # (UP = 0→1, DOWN = 1→0).

    # Walk passes through a+1 in two ways:
    # 1. Going RIGHT: ..., a, a+1, a+2, ...
    #    Step k-1: mover=a. a fires, changing a's state.
    #    Step k: mover=a+1. a+1 sees (new_a, S, old_a+2).
    #    Step k+1: mover=a+2.
    #
    # 2. Going LEFT: ..., a+2, a+1, a, ...
    #    Step k-1: mover=a+2. a+2 fires, changing a+2's state.
    #    Step k: mover=a+1. a+1 sees (old_a, S, new_a+2).
    #    Step k+1: mover=a.

    # Key constraint: the walk must be a CYCLE. So the state of each
    # processor returns to its initial state after the full cycle.
    # For binary processors: state alternates 0→1→0→1...
    # So each binary processor fires an EVEN number of times.

    print("Consider binary triple at positions (a, a+1, a+2).")
    print("Middle processor P_{a+1} has 4 (L,R) contexts: (0,0), (0,1), (1,0), (1,1)")
    print("Each is UP, DOWN, or NEUTRAL.")
    print()

    # State evolution through the walk:
    # Binary processors alternate states. If a fires K times total,
    # K must be even (to return to initial state).

    # Count constraints:
    # P_{a+1} fires F times. F must be even.
    # Each firing is either UP (0→1) or DOWN (1→0).
    # F/2 UP firings and F/2 DOWN firings (since state must return).

    # Each UP firing uses a context (L, 0, R) where (L, R) is an UP pair.
    # Each DOWN firing uses a context (L, 1, R) where (L, R) is a DOWN pair.

    # The (L, R) at each firing depends on the walk:
    # Going right: L = state of P_a AFTER P_a fires
    # Going left: R = state of P_{a+2} AFTER P_{a+2} fires

    print("State return constraint: P_{a+1} fires F times, F even.")
    print("F/2 UP firings (0→1), F/2 DOWN firings (1→0).")
    print()

    # Now analyze the walk through the triple in detail.
    # In a bounce walk: ..., a, a+1, a+2, ..., a+2, a+1, a, ...
    # Each full bounce traverses the triple twice (right then left).

    # Consider one right-then-left traversal through the triple:
    # Step 1: P_a fires. Let's track states.
    # Step 2: P_{a+1} fires.
    # Step 3: P_{a+2} fires.
    # ... (walk continues to the right or turns)
    # Step 4: P_{a+2} fires (coming back from the right).
    # Step 5: P_{a+1} fires.
    # Step 6: P_a fires.

    # Between steps 3 and 4, P_{a+2} fires twice (step 3 and step 4).
    # If no other processor between a+2 and the turnaround changes a+2's
    # context, then P_{a+2} might have the same context at both firings.
    # But the walk goes RIGHT from a+2, potentially changing a+2's
    # right neighbor's state.

    print("Consider a bounce through the triple:")
    print("  RIGHT pass: P_a → P_{a+1} → P_{a+2}")
    print("  LEFT pass:  P_{a+2} → P_{a+1} → P_a")
    print()

    # Let's track states explicitly.
    # Initial states: s_a, s_{a+1}, s_{a+2} ∈ {0, 1}
    # After RIGHT pass:
    #   P_a fires: s_a → 1-s_a. P_{a+1} sees L=1-s_a.
    #   P_{a+1} fires: s_{a+1} → 1-s_{a+1}. Uses context (1-s_a, s_{a+1}, s_{a+2}).
    #   P_{a+2} fires: s_{a+2} → 1-s_{a+2}. Sees context (1-s_{a+1}, s_{a+2}, ?).
    # After LEFT pass (returning through the triple):
    #   P_{a+2} fires again: 1-s_{a+2} → s_{a+2}.
    #     Sees context (1-s_{a+1}, 1-s_{a+2}, ?_right).
    #   P_{a+1} fires again: 1-s_{a+1} → s_{a+1}.
    #     Sees context (1-s_a, 1-s_{a+1}, s_{a+2}).
    #   P_a fires again: 1-s_a → s_a.
    #     Sees context (?_left, 1-s_a, s_{a+1}).

    # After full bounce through triple: all states return to initial!
    # P_{a+1}'s two contexts in this bounce:
    #   RIGHT: (1-s_a, s_{a+1}, s_{a+2})
    #   LEFT:  (1-s_a, 1-s_{a+1}, s_{a+2})
    # Note: L is the SAME (1-s_a) in both passes!
    #        R is the SAME (s_{a+2}) in both passes!
    # Only S changes: s_{a+1} → 1-s_{a+1}

    print("P_{a+1} contexts in one bounce through triple:")
    print("  RIGHT: (1-s_a, s_{a+1}, s_{a+2})")
    print("  LEFT:  (1-s_a, 1-s_{a+1}, s_{a+2})")
    print("  Same (L,R) = (1-s_a, s_{a+2}) in both!")
    print()

    # This means: in one bounce, P_{a+1} fires UP and DOWN at the
    # SAME (L,R) context! But by No Binary 2-Cycle, each (L,R) is
    # either UP or DOWN, not both!

    # Wait, UP means f(L,0,R)=1 and DOWN means f(L,1,R)=0.
    # The RIGHT pass fires with S=s_{a+1}. If s_{a+1}=0, it's UP.
    # The LEFT pass fires with S=1-s_{a+1}. If s_{a+1}=0, S=1, it's DOWN.

    # So one pass is UP and the other is DOWN, at the SAME (L,R).
    # UP at (L,R): f(L,0,R)=1
    # DOWN at (L,R): f(L,1,R)=0
    # Both together: f(L,0,R)=1 AND f(L,1,R)=0 = FORBIDDEN by No Binary 2-Cycle!

    print("*** CONTRADICTION! ***")
    print()
    print("In one bounce through a binary triple:")
    print("  RIGHT pass: P_{a+1} fires at (L, s_{a+1}, R)")
    print("  LEFT pass:  P_{a+1} fires at (L, 1-s_{a+1}, R)")
    print("  Same (L,R), both states 0 and 1.")
    print()
    print("If s_{a+1}=0:")
    print("  RIGHT: fires UP at (L,0,R) → f(L,0,R)=1")
    print("  LEFT:  fires DOWN at (L,1,R) → f(L,1,R)=0")
    print("  BOTH: f(L,0,R)=1 AND f(L,1,R)=0 → FORBIDDEN!")
    print()
    print("If s_{a+1}=1:")
    print("  RIGHT: fires DOWN at (L,1,R) → f(L,1,R)=0")
    print("  LEFT:  fires UP at (L,0,R) → f(L,0,R)=1")
    print("  SAME CONTRADICTION!")

    print()
    print("=" * 70)
    print("WAIT — this assumes (L,R) is the same in both passes.")
    print("Let me verify this more carefully...")
    print("=" * 70)
    print()

    # Let me re-derive more carefully.
    # In a bounce: ..., a-1, a, a+1, a+2, a+3, ..., a+3, a+2, a+1, a, a-1, ...
    #
    # RIGHT pass through triple:
    # Step k-1: P_{a-1} fires (or P_a is first in the sweep)
    # Step k: P_a fires. State: s_a → 1-s_a.
    # Step k+1: P_{a+1} fires. Context: (1-s_a, s_{a+1}, s_{a+2}).
    #   Direction: if s_{a+1}=0, UP; if s_{a+1}=1, DOWN.
    #   State: s_{a+1} → 1-s_{a+1}.
    # Step k+2: P_{a+2} fires. Context: (1-s_{a+1}, s_{a+2}, s_{a+3}).
    #   State: s_{a+2} → 1-s_{a+2}.
    # Step k+3: P_{a+3} fires. Continue right...
    #
    # LEFT pass (after turnaround at some point):
    # Step j-1: P_{a+3} fires (or P_{a+2} is first in left sweep)
    # Step j: P_{a+2} fires. State: ... depends on what happened.

    # The issue is: between the RIGHT and LEFT passes, other processors
    # fire and change states. P_a and P_{a+2} might fire again
    # (in subsequent bounces), changing their states.
    #
    # But P_a's state only changes when P_a fires. Between P_{a+1}'s
    # RIGHT firing (step k+1) and LEFT firing:
    # - P_a fires at step k (RIGHT) and again at some later step (LEFT)
    # - So P_a's state at the LEFT pass is s_a (returned after 2 firings)
    #   or 1-s_a (after 1 additional firing)
    #
    # In a simple bounce (..., a, a+1, a+2, ..., turnaround, ..., a+2, a+1, a, ...):
    # P_a fires ONCE going right (step k) and ONCE going left (later step).
    # Between these, P_a doesn't fire (the walk goes right past a+2, turns, comes back).
    # So at the LEFT pass, P_a's state is 1-s_a (changed by the RIGHT pass, not yet
    # changed back).
    #
    # Similarly, P_{a+2} fires ONCE going right and ONCE going left.
    # At the LEFT pass through P_{a+1}:
    # P_{a+2} has already fired twice (once RIGHT at step k+2, once LEFT returning).
    # After two firings, P_{a+2} returns to s_{a+2}.
    # Wait no: P_{a+2} fires at step k+2 going right. Then the walk continues right.
    # Later, the walk returns through P_{a+2} going left. P_{a+2} fires again.
    # So P_{a+2}'s state at P_{a+1}'s LEFT pass:
    # After P_{a+2}'s LEFT firing, P_{a+2}'s state returns to s_{a+2}.
    # But P_{a+1}'s LEFT firing happens AFTER P_{a+2}'s LEFT firing.
    # So P_{a+2}'s state at P_{a+1}'s LEFT firing is s_{a+2} (returned).
    #
    # WAIT. Let me trace more carefully.

    print("Careful trace of states through a simple bounce:")
    print("Walk: ..., a, a+1, a+2, a+3, ..., [turnaround], ..., a+3, a+2, a+1, a, ...")
    print()

    # For simplicity, consider the walk segment: a, a+1, a+2, (a+3...turnaround...a+3), a+2, a+1, a
    # Initial states at positions a, a+1, a+2: (s0, s1, s2)

    # Step 1: P_a fires. State: s0 → 1-s0.
    #   States: (1-s0, s1, s2)
    # Step 2: P_{a+1} fires. Context: (1-s0, s1, s2). Direction: UP if s1=0, DOWN if s1=1.
    #   State: s1 → 1-s1.
    #   States: (1-s0, 1-s1, s2)
    # Step 3: P_{a+2} fires. Context: (1-s1, s2, s3). Direction depends on s2.
    #   State: s2 → 1-s2.
    #   States: (1-s0, 1-s1, 1-s2)
    # ... walk continues right, eventually turns around, comes back ...
    # ... during the rightward walk, P_{a+2}'s right neighbor changes state ...
    # ... the walk returns ...
    # Step j: P_{a+2} fires (returning). P_{a+2}'s state was 1-s2.
    #   P_{a+2}'s left neighbor is P_{a+1} with state 1-s1 (unchanged since step 2).
    #   P_{a+2}'s right neighbor has some state (changed during the rightward walk).
    #   Context: (1-s1, 1-s2, s3'). Direction: depends on 1-s2.
    #   State: 1-s2 → s2.
    #   States: (1-s0, 1-s1, s2)
    # Step j+1: P_{a+1} fires (returning).
    #   LEFT context: (L, 1-s1, R) where L = P_a's state, R = P_{a+2}'s state
    #   P_a hasn't fired since step 1, so P_a's state is 1-s0.
    #   P_{a+2} just fired (step j), so P_{a+2}'s state is s2.
    #   Context: (1-s0, 1-s1, s2).
    #   SAME AS STEP 2! Context is (1-s0, ?, s2) with ? = s1 at step 2 and 1-s1 at step j+1.
    #   L = 1-s0 (same), R = s2 (same), S different (s1 vs 1-s1).

    print("Step 2 (RIGHT): P_{a+1} context = (1-s0, s1, s2)")
    print("Step j+1 (LEFT): P_{a+1} context = (1-s0, 1-s1, s2)")
    print()
    print("(L,R) = (1-s0, s2) in BOTH cases!")
    print("S = s1 in step 2, S = 1-s1 in step j+1")
    print()

    # So P_{a+1} fires at context (1-s0, s1, s2) going right
    # and at context (1-s0, 1-s1, s2) going left.
    # SAME (L,R) = (1-s0, s2), different S.
    #
    # If s1=0: RIGHT is UP (0→1), LEFT is DOWN (1→0).
    #   f(1-s0, 0, s2) = 1 AND f(1-s0, 1, s2) = 0
    #   FORBIDDEN by No Binary 2-Cycle!
    #
    # If s1=1: RIGHT is DOWN (1→0), LEFT is UP (0→1).
    #   f(1-s0, 1, s2) = 0 AND f(1-s0, 0, s2) = 1
    #   SAME CONTRADICTION!

    print("*** CONFIRMED CONTRADICTION ***")
    print()
    print("In a simple bounce through a binary triple,")
    print("the middle processor P_{a+1} is forced to have")
    print("f(L,0,R) = 1 AND f(L,1,R) = 0 for (L,R) = (1-s0, s2).")
    print("This violates the No Binary 2-Cycle Lemma.")
    print()
    print("THEREFORE: No valid system can have 3 consecutive binary")
    print("processors in a BOUNCE good cycle.")
    print()

    # But wait: the walk doesn't have to be a simple bounce through
    # the triple. The walk could "stay" at a+1 (step 0) or take
    # other paths. Let me check if the contradiction extends to
    # all adjacent-mover walks.

    print("=" * 70)
    print("Does this extend to ALL adjacent-mover walks (not just bounces)?")
    print("=" * 70)
    print()

    # In any walk, P_{a+1} must fire at least twice (for the state to
    # return — if it fires an odd number of times, the state doesn't return).
    # Each firing approaches from the left (P_a just fired) or from the
    # right (P_{a+2} just fired) or is a repeat (P_{a+1} fires again).

    # Case 1: Two firings approach from the same direction (both from left).
    #   Then between the two firings, P_a fired (to change L) and P_{a+2}
    #   might or might not have fired (to change R).
    #   The (L,R) contexts could differ: L changes, R might change.
    #   No immediate contradiction.

    # Case 2: Two firings approach from different directions (one left, one right).
    #   This is the bounce case analyzed above.
    #   At RIGHT firing: L = state of P_a after P_a fires
    #   At LEFT firing: R = state of P_{a+2} after P_{a+2} fires
    #   The question is whether L and R remain the same.

    # In the bounce, between RIGHT and LEFT firings of P_{a+1}:
    # - P_a does NOT fire (the walk went right from a+1)
    # - P_{a+2} fires TWICE (going right and coming back)
    # So L stays 1-s0, and R returns to s2 after P_{a+2}'s two firings.
    # This gives the same (L,R) → contradiction.

    # But what if the walk does something more complex?
    # E.g., after going right from a+1, the walk bounces at a+2 and
    # returns to a+1 WITHOUT going further right.
    # Walk: ..., a, a+1, a+2, a+1, ...
    # In this case, P_{a+2} fires once (going right), and P_{a+1} fires
    # again immediately.
    # P_{a+1}'s second firing:
    #   P_{a+2} just fired, changing R.
    #   P_a did NOT fire since P_{a+1}'s first firing.
    #   Context: (1-s0, 1-s1, 1-s2). L = 1-s0, R = 1-s2.
    #   First firing context: (1-s0, s1, s2). L = 1-s0, R = s2.
    #   L is same, R differs! (L,R) = (1-s0, s2) vs (1-s0, 1-s2).
    #   So the two firings use DIFFERENT (L,R) pairs!

    print("Alternative walk: ..., a, a+1, a+2, a+1, ...")
    print("  Step 1 (RIGHT): context (1-s0, s1, s2), (L,R) = (1-s0, s2)")
    print("  Step 3 (LEFT): context (1-s0, 1-s1, 1-s2), (L,R) = (1-s0, 1-s2)")
    print("  Different (L,R)! No contradiction from these two firings alone.")
    print()

    # However, each firing still determines entries:
    # Step 1: f(1-s0, s1, s2) = 1-s1 (mover entry)
    # Step 3: f(1-s0, 1-s1, 1-s2) = s1 (mover entry)
    # These are entries at different (L,S,R) triples.
    # No 2-cycle issue with different (L,R).

    # But P_{a+1} must fire an EVEN number of times. If it fires at
    # k different (L,R) pairs, it uses k UP entries and k DOWN entries.
    # With only 4 possible (L,R) pairs, P_{a+1} can have at most 4 UP
    # and 4 DOWN entries. But each (L,R) is UP, DOWN, or NEUTRAL
    # (not both UP and DOWN). So P_{a+1} has at most 4 mover contexts.

    # For the simple bounce, P_{a+1} fires exactly twice per full bounce,
    # using the SAME (L,R) for both UP and DOWN → contradiction.

    # For more complex walks, P_{a+1} might use different (L,R) for
    # UP and DOWN, avoiding the immediate contradiction.

    # So the contradiction is specific to the simple bounce structure.
    # More complex walks might avoid it.

    print("=" * 70)
    print("CONCLUSION:")
    print("=" * 70)
    print()
    print("Simple bounce through binary triple → CONTRADICTION")
    print("(No Binary 2-Cycle violated)")
    print()
    print("More complex walks (e.g., a,a+1,a+2,a+1) use different (L,R)")
    print("for UP and DOWN, potentially avoiding the contradiction.")
    print()
    print("But: with 4 (L,R) pairs and multiple walk passes,")
    print("the (L,R) space gets exhausted quickly.")
    print("With enough passes, a collision is inevitable.")
    print()

    # Let me count: in a full cycle, P_{a+1} fires F times (even).
    # F/2 UP and F/2 DOWN. Each UP uses a specific (L,R) from {(0,0), (0,1), (1,0), (1,1)}.
    # Each DOWN uses a different (L,R). If F/2 > 2, then by pigeonhole,
    # at least two UP firings share the same L or two DOWN firings share the same L.
    # But that's not immediately a contradiction.

    # The real constraint: each (L,R) pair is assigned a DIRECTION (UP, DOWN, NEUTRAL).
    # An UP firing at (L,R) uses the entry f(L,0,R)=1.
    # A DOWN firing at (L,R) uses the entry f(L,1,R)=0.
    # We need UP and DOWN firings to use DIFFERENT (L,R) pairs.
    # With F/2 UP and F/2 DOWN firings, we need at least F/2 UP (L,R) pairs
    # and at least F/2 DOWN (L,R) pairs, all different.
    # Wait, different firings can reuse the same (L,R) if they're the same direction!

    # The only constraint is: the same (L,R) can't be both UP and DOWN.
    # Different UP firings CAN use the same (L,R).
    # So we need: UP (L,R) pairs ∩ DOWN (L,R) pairs = ∅.
    # With 4 (L,R) pairs, up to 2 can be UP and 2 DOWN (and rest NEUTRAL).
    # Or 3 UP and 1 DOWN, etc.

    # The number of firings F can be large (proportional to cycle length),
    # but the number of distinct (L,R) pairs is only 4. Multiple firings
    # can reuse the same pair as long as the direction is consistent.

    # So the constraint is weaker than I initially thought:
    # 4 (L,R) pairs, partitioned into UP, DOWN, NEUTRAL.
    # At least 1 UP and 1 DOWN (since P_{a+1} fires in both directions).
    # The number of firings F must be even, with F/2 ≥ 1 each.

    # This is satisfiable! E.g., (0,0)=UP, (1,1)=DOWN, rest=NEUTRAL.
    # P_{a+1} fires UP at (0,0) and DOWN at (1,1), F=2, valid.

    print("Actually, the binary triple doesn't give a universal")
    print("contradiction for all walk types. The simple bounce")
    print("contradiction is specific to walks where the same (L,R)")
    print("is used for both UP and DOWN at the middle processor.")
    print()
    print("For the edge-triple argument to work more broadly,")
    print("additional constraints from the walk structure are needed.")
    print()

    return True


def verify_binary_triple_bounce_contradiction():
    """Computationally verify: no valid system exists with 3 consecutive
    binary in a bounce walk."""
    print("=" * 70)
    print("VERIFICATION: Binary triple in bounce cycles")
    print("=" * 70)
    print()

    # Test: for ms with ≥3 consecutive binary, do ALL bounce cycles fail?
    n = 7
    test_cases = [
        # 3 consecutive binary at positions 0,1,2
        (2, 2, 2, 3, 3, 3, 3),
        (2, 2, 2, 4, 4, 4, 4),
        (2, 2, 2, 5, 3, 3, 3),
        (2, 2, 2, 3, 4, 3, 3),
    ]

    bounce_pats = [
        list(range(n - 1, -1, -1)) + list(range(1, n)),
        list(range(n)) + list(range(n - 2, 0, -1)),
    ]

    for ms in test_cases:
        print(f"ms={ms}")
        for base in bounce_pats:
            config = [0] * n
            cycle = [tuple(config)]
            visited = {tuple(config)}
            full = base * 5
            found = False
            for step, mover in enumerate(full):
                config = list(cycle[-1])
                config[mover] = (config[mover] + 1) % ms[mover]
                nc = tuple(config)
                if nc == cycle[0]:
                    found = True
                    movers_seq = full[:step + 1]
                    break
                if nc in visited:
                    break
                visited.add(nc)
                cycle.append(nc)

            if not found:
                print(f"  pattern {base[:5]}...: no cycle")
                continue

            # Check middle binary processor contexts
            p = 1  # middle of triple
            mover_ctxs = set()
            for idx in range(len(cycle)):
                c = cycle[idx]
                if movers_seq[idx] == p:
                    ctx = (c[0], c[1], c[2])
                    mover_ctxs.add(ctx)

            # Check for 2-cycle violation
            violations = []
            for L in range(ms[0]):
                for R in range(ms[2]):
                    up = (L, 0, R) in mover_ctxs
                    down = (L, 1, R) in mover_ctxs
                    if up and down:
                        violations.append((L, R))

            if violations:
                print(f"  pattern {base[:5]}...: cycle len={len(cycle)}, "
                      f"2-CYCLE VIOLATION at P1 for (L,R)={violations}")
            else:
                print(f"  pattern {base[:5]}...: cycle len={len(cycle)}, "
                      f"P1 mover contexts={mover_ctxs}, no violation")


def analyze_non_consecutive_binary():
    """What about ≥3 binary but NOT consecutive (≤2 consecutive)?"""
    print()
    print("=" * 70)
    print("NON-CONSECUTIVE BINARY ANALYSIS")
    print("=" * 70)
    print()

    # If binary processors are NOT consecutive (e.g., positions 0, 2, 4
    # with non-binary between), the middle binary has NON-BINARY neighbors.
    # Contexts: (c[p-1], S, c[p+1]) where c[p-1] ∈ {0,...,m_{p-1}-1}
    # and c[p+1] ∈ {0,...,m_{p+1}-1}. More contexts available!

    # The No Binary 2-Cycle lemma still applies, but with more (L,R) pairs,
    # the UP/DOWN partition has more room. The bounce contradiction might
    # not apply.

    # Example: ms = (2, 3, 2, 3, 2, 3, 3) with binary at 0, 2, 4
    # P2 has contexts: L ∈ {0,1,2} (from P1), R ∈ {0,1,2} (from P3)
    # 9 (L,R) pairs, 18 total contexts
    # Much more room for UP/DOWN partitioning

    n = 7
    ms_cases = [
        ((2, 3, 2, 3, 2, 3, 3), "3 binary non-consec"),
        ((2, 4, 2, 4, 2, 4, 4), "3 binary non-consec quat"),
    ]

    bounce_pats = [
        list(range(n - 1, -1, -1)) + list(range(1, n)),
        list(range(n)) + list(range(n - 2, 0, -1)),
    ]

    for ms, label in ms_cases:
        print(f"\n{label}: ms={ms}")
        for base in bounce_pats:
            config = [0] * n
            cycle = [tuple(config)]
            visited = {tuple(config)}
            full = base * 5
            found = False
            for step, mover in enumerate(full):
                config = list(cycle[-1])
                config[mover] = (config[mover] + 1) % ms[mover]
                nc = tuple(config)
                if nc == cycle[0]:
                    found = True
                    movers_seq = full[:step + 1]
                    break
                if nc in visited:
                    break
                visited.add(nc)
                cycle.append(nc)

            if not found:
                print(f"  pattern {base[:5]}...: no cycle")
                continue

            # Check all binary processors
            for p in range(n):
                if ms[p] != 2:
                    continue
                mover_ctxs = set()
                for idx in range(len(cycle)):
                    c = cycle[idx]
                    if movers_seq[idx] == p:
                        ctx = (c[(p - 1) % n], c[p], c[(p + 1) % n])
                        mover_ctxs.add(ctx)

                violations = []
                m_L = ms[(p - 1) % n]
                m_R = ms[(p + 1) % n]
                for L in range(m_L):
                    for R in range(m_R):
                        up = (L, 0, R) in mover_ctxs
                        down = (L, 1, R) in mover_ctxs
                        if up and down:
                            violations.append((L, R))

                total_lr = m_L * m_R
                up_count = sum(1 for L in range(m_L) for R in range(m_R)
                               if (L, 0, R) in mover_ctxs
                               and (L, 1, R) not in mover_ctxs)
                down_count = sum(1 for L in range(m_L) for R in range(m_R)
                                 if (L, 1, R) in mover_ctxs
                                 and (L, 0, R) not in mover_ctxs)

                if violations:
                    print(f"  P{p}: 2-CYCLE VIOLATION (L,R)={violations}")
                else:
                    print(f"  P{p}: OK. UP={up_count}, DOWN={down_count}, "
                          f"NEUTRAL={total_lr - up_count - down_count} "
                          f"(of {total_lr} pairs)")

            # Also check forced SCCs
            good_set = set(cycle)
            all_cfgs = list(cartesian(*(range(m) for m in ms)))
            non_good_set = set(c for c in all_cfgs if c not in good_set)

            det = {}
            for idx in range(len(cycle)):
                c = cycle[idx]
                c_next = cycle[(idx + 1) % len(cycle)]
                mv = movers_seq[idx]
                for p2 in range(n):
                    L = c[(p2 - 1) % n]
                    S = c[p2]
                    R = c[(p2 + 1) % n]
                    key = (p2, L, S, R)
                    if p2 == mv:
                        det[key] = c_next[p2]
                    else:
                        det[key] = S

            forced_adj = defaultdict(list)
            for c in non_good_set:
                for p2 in range(n):
                    L = c[(p2 - 1) % n]
                    S = c[p2]
                    R = c[(p2 + 1) % n]
                    key = (p2, L, S, R)
                    if key in det and det[key] != S:
                        new_c = list(c)
                        new_c[p2] = det[key]
                        nc = tuple(new_c)
                        if nc in non_good_set:
                            forced_adj[c].append(nc)

            # Quick 2-cycle check
            has_2cycle = False
            for c in forced_adj:
                for nc in forced_adj[c]:
                    if c in forced_adj.get(nc, []):
                        has_2cycle = True
                        break
                if has_2cycle:
                    break

            priv_count = len(forced_adj)
            print(f"  Forced privilege: {priv_count}/{len(non_good_set)} "
                  f"({100*priv_count/max(1, len(non_good_set)):.0f}%)")
            print(f"  Has forced 2-cycle: {has_2cycle}")
            print(f"  Cycle len={len(cycle)}")


# Run all analyses
analyze_binary_triple_walk()
print()
verify_binary_triple_bounce_contradiction()
analyze_non_consecutive_binary()
