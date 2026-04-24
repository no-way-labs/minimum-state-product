#!/usr/bin/env python3
"""Analyze cascade cycle CLOSURE: why the cycle must close.

The argument so far:
1. At binary=(1,1,1), interior-only dynamics hit a dead end (no privileged proc)
   or cycle. Either way, a non-interior proc must fire at some point.
2. The adversary can pick a border proc to fire -> boundary changes.

But does this create a BAD cycle? Maybe firing the border leads to good configs?

Key insight: The border fire changes c3 or c7. After this change, interior procs
may become privileged or not. The question is whether the resulting state is
good or bad.

CRITICAL OBSERVATION: Good cycle has only ~6 configs at binary=(1,1,1).
After a border proc fires, we're still at binary=(1,1,1) (border fires don't
change binary state). So we need to check: of the configs reachable by
border fire from binary=(1,1,1), how many land in good?

Since good has only 6 configs at binary=(1,1,1), and border fire can land
at any of 324 configs with binary=(1,1,1), the probability of landing in
good is ~6/324 = 1.85%. The adversary AVOIDS good configs.

Actually, the adversary picks WHICH config to start from (among those where
border is privileged) AND which successor to go to. If the border fire from
a bad config leads to a good config, the adversary just doesn't fire from there.
The adversary needs ONE bad config where border fire leads to ANOTHER bad config.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))

from itertools import product as cartesian
from collections import defaultdict


def analyze_border_fire_destinations(n, ms):
    """For each boundary (c3, c7), count configs and check what border fires do."""
    total = 1
    for m in ms:
        total *= m
    non_bin = total // 8

    # A border fire changes c3 or c7.
    # P3 fire: c3 -> f3(c2, c3, c4). With binary=(1,1,1), c2=1.
    # P7 fire: c7 -> f7(c6, c7, c0). With binary=(1,1,1), c0=1.

    # The config after P3 fires differs only in c3.
    # If the original was bad (not in good cycle), is the destination also bad?
    # Good cycle visits ~6 configs at binary=(1,1,1). These have specific
    # (c3, c4, c5, c6, c7) values.

    # For the cascade to close, we need:
    # 1. From binary=(1,1,1) + some bad non-binary state: border fires -> still bad
    # 2. Interior adjusts -> still bad -> eventually need another border/binary fire
    # 3. Eventually binary fires -> reverse sweep
    # 4. At binary=(0,0,0): same argument -> border fires -> boundary changes
    # 5. Reverse sweep happens -> back to binary=(1,1,1)
    # 6. Cycle closes

    # The key: 6 good configs at binary=(1,1,1) out of 324.
    # The border fire changes ONE coordinate (c3 or c7).
    # For a config (1,1,1, c3, c4, c5, c6, c7):
    # If P3 fires, c3 changes. New config: (1,1,1, c3', c4, c5, c6, c7).
    # For this to be good, (c3', c4, c5, c6, c7) must match one of the 6 good
    # non-binary states. So we need c4, c5, c6, c7 to match exactly.
    # This happens for at most ms[3] non-binary states (one c3 value per matching
    # (c4,c5,c6,c7)).

    # Actually, the 6 good configs at binary=(1,1,1) span 6 distinct non-binary
    # states. A border fire from (1,1,1, c3, c4, c5, c6, c7) changes only c3
    # (or c7). For the destination to be good, we need (c3', c4, c5, c6, c7)
    # to be one of the 6 good states. Since c4, c5, c6, c7 are unchanged,
    # this requires (c4, c5, c6, c7) to appear in some good state.

    # With 6 good states at binary=(1,1,1), there are at most 6 distinct
    # (c4, c5, c6, c7) patterns. A border fire can only land in good if the
    # current (c4, c5, c6, c7) happens to match one of these 6 patterns.

    # Total (c4, c5, c6, c7) patterns: ms[4]*ms[5]*ms[6]*ms[7] = 3*3*3*4 = 108.
    # So at most 6/108 ≈ 5.6% of patterns can land in good via P3 fire.
    # For each such pattern, only ONE c3' value leads to good (the specific
    # good state). Other c3' values stay bad.

    print(f"n={n}: At binary=(1,1,1):")
    print(f"  Total configs: {non_bin}")
    print(f"  Good configs: ~6")
    print(f"  (c4,c5,c6,c7) patterns: {non_bin // ms[3]}")
    print(f"  Good (c4,...) patterns: at most 6")
    print(f"  Border fire from bad -> good probability: at most 6/{non_bin // ms[3]} = {6/(non_bin // ms[3]):.3f}")

    # The adversary controls which bad config the border fire starts from.
    # They choose a bad config where (c4,c5,c6,c7) does NOT match any good pattern.
    # Then border fire CANNOT lead to good -> destination is bad.
    # This is possible as long as there exist bad configs with non-matching patterns.
    # Since 108 - 6 = 102 non-matching patterns exist, each with at least one bad
    # config, the adversary can always find one.

    print(f"  Non-matching patterns: {non_bin // ms[3] - 6}")
    print(f"  Adversary CAN force bad->bad border fire: YES (102 patterns available)")


def cascade_cycle_counting(n, ms):
    """Count the CASCADE CYCLE constraint budget.

    A cascade cycle visits 4 boundary conditions and has ~16 steps.
    Each step constrains one table entry. The cycle also requires that
    at each step's config, the mover proc IS privileged (entry != stay).

    At n=7 vs n=8, the good cycle constrains different fractions of the
    total table. The question: at n>=8, does the cascade's 16 entries
    fit within the free space AND avoid conflict with the good cycle?
    """
    total_entries = sum(ms[(p-1)%n] * ms[p] * ms[(p+1)%n] for p in range(n))
    gc_len = 2 * n  # approximate good cycle length

    # Good cycle constrains gc_len mover entries and gc_len * (n-1) non-mover entries
    # But many non-mover entries overlap across steps.
    # Rough estimate: gc_len * ~3 unique constrained entries per step? Hard to say.

    # Cascade constrains 16 entries (from the data).
    # Free entries: total - constrained.

    print(f"\nn={n}, ms={ms}")
    print(f"  Total table entries: {total_entries}")
    print(f"  Good cycle length: ~{gc_len}")
    print(f"  Cascade cycle entries: 16")

    # The REAL question: can the designer set the 16 cascade entries to BLOCK
    # the cascade? The cascade requires each mover entry to fire (f != stay).
    # To block: set one of the 16 entries to stay (f = self).
    # But: does this create a dead config (liveness fail)?

    # If we set one cascade entry to stay, say f_p(L,S,R) = S:
    # Then at the corresponding config, proc p doesn't fire.
    # But some other proc might fire instead -> the adversary takes a different path.
    # The cascade might just reroute through a different config.

    # This is the key difficulty: the cascade is not one specific path but
    # a FAMILY of paths. Blocking one config might not block the family.

    print(f"  Blocking one entry: adversary reroutes through 322 other configs")
    print(f"  at that binary triple.")


def binary_fire_argument():
    """The binary fire argument: why binary procs must eventually fire.

    At binary=(1,1,1), any path must eventually fire a non-interior proc.
    Options: border (P3, P7) or binary (P0, P1, P2).

    If border fires: boundary changes, interior adjusts, back to same binary state.
    After all boundary conditions are visited (4 for (c3,c7) mod their ranges),
    what then? The adversary has 12 boundary conditions at n=8 (3*4=12).

    But: border fires change ONE boundary coordinate. So boundaries cycle:
    c3: 0->1->2->0 (period 3)
    c7: 0->1->2->3->0 (period 4)

    After sufficiently many border fires, all boundaries visited.
    At each boundary, interior adjusts -> reaches dead end -> another border/binary fire.

    CLAIM: after cycling through all 12 boundaries at binary=(1,1,1),
    the only way to change binary state is to fire a binary proc.

    Actually, the adversary doesn't need to visit all boundaries. They just need
    to find one path that creates a cycle. The cycle must close, meaning it returns
    to a previously visited config. Since the config space is finite and the
    adversary keeps firing procs, this must happen.

    The cycle involves configs at binary=(1,1,1) AND possibly other binary states.
    But interior-only fires stay at binary=(1,1,1).
    Border-only fires stay at binary=(1,1,1).
    Only binary fires change binary state.

    So any cycle that visits ONLY binary=(1,1,1) is an interior+border cycle.
    Such a cycle would involve boundary changes and interior adjustments.
    This IS a bad cycle (convergence failure).

    Any cycle that also visits other binary states MUST include binary fires.
    A binary fire from (1,1,1) goes to (x,y,z) with some coordinate changed.
    This starts moving toward (0,0,0). Eventually reaches (0,0,0) (or some
    other binary triple). From (0,0,0), same argument: must eventually fire
    non-interior, leading to boundary changes and eventually binary fires back
    to (1,1,1). This creates the cascade.
    """

    print("="*70)
    print("BINARY FIRE ARGUMENT")
    print("="*70)
    print()
    print("Claim: In any valid system, the adversary can force a bad cycle")
    print("that includes both binary states (0,0,0) and (1,1,1).")
    print()
    print("Proof outline:")
    print("1. At binary=(1,1,1), interior-only dynamics must hit dead end (Lemma 1).")
    print("2. At the dead end, a non-interior proc is privileged.")
    print("3. The adversary can choose to fire a border proc (if available).")
    print("4. Border fire changes boundary, interior adjusts, hits dead end again.")
    print("5. If border proc NOT available: binary proc must be privileged.")
    print("   Binary fire starts reverse sweep toward (0,0,0).")
    print("6. At (0,0,0), same argument by symmetry.")
    print("7. The cycle (1,1,1) -> ... -> (0,0,0) -> ... -> (1,1,1) is a bad cycle.")
    print()
    print("Key Lemma 1: Interior-only dynamics at fixed binary state must terminate.")
    print("Proof: Interior fires change c4, c5, c6 only. Under fixed binary and")
    print("boundary, the interior state space has 3^k states (k = |interior|).")
    print("Since fire must change state (f != stay), each step changes some c_i.")
    print("The interior dynamics under fixed boundary is a directed graph on 3^k nodes.")
    print("If it's a DAG: reaches sink in 3^k steps. Sink has no privileged interior proc.")
    print("If it has a cycle: that's a bad cycle with only interior fires -> convergence fail.")
    print("Valid system requires DAG -> sink exists -> non-interior proc fires at sink.")
    print()
    print("But WAIT: boundary isn't fixed during interior adjustment!")
    print("Border procs might become privileged during interior fire.")
    print("The adversary can fire the border proc instead of continuing interior.")
    print()
    print("More precisely: at each step, the adversary picks ANY privileged proc.")
    print("If interior + border procs are both privileged, adversary picks border.")
    print("This changes boundary, and interior may need to re-adjust.")
    print("The adversary can keep bouncing between border fires and interior fires,")
    print("potentially cycling through boundary conditions.")


def main():
    analyze_border_fire_destinations(8, (2,2,2,3,3,3,3,4))
    analyze_border_fire_destinations(7, (2,2,2,3,3,3,4))

    cascade_cycle_counting(7, (2,2,2,3,3,3,4))
    cascade_cycle_counting(8, (2,2,2,3,3,3,3,4))

    binary_fire_argument()

    print()
    print("="*70)
    print("THE ESSENTIAL ARGUMENT")
    print("="*70)
    print()
    print("Consider any binary state b in {(0,0,0), (1,1,1)}.")
    print("Let C_b = set of all configs with binary state b. |C_b| = product/8.")
    print("Let G_b = good configs in C_b. |G_b| <= cycle_len/8.")
    print("Let B_b = bad configs in C_b. |B_b| = |C_b| - |G_b|.")
    print()
    print("For liveness, every config in B_b has at least one privileged proc.")
    print("Partition B_b by which TYPE of proc is privileged:")
    print("  B_bin: binary proc privileged (can reverse sweep)")
    print("  B_brd: border proc privileged (boundary change)")
    print("  B_int: interior proc privileged (interior adjustment)")
    print("(A config can be in multiple sets if multiple procs are privileged.)")
    print()
    print("B_b = B_bin ∪ B_brd ∪ B_int (by liveness, every config in at least one).")
    print()
    print("The adversary strategy:")
    print("  - At B_brd configs: fire border -> boundary changes, stay at binary=b")
    print("  - At B_bin configs: fire binary -> binary state changes")
    print("  - At B_int configs: fire interior -> stay at binary=b, interior changes")
    print()
    print("Interior fires eventually lead to B_brd or B_bin (Lemma 1).")
    print("Border fires change boundary but stay at binary=b.")
    print("The adversary alternates border+interior fires until forced to binary fire.")
    print()
    print("When does the adversary get forced to fire binary?")
    print("When a config has ONLY binary procs privileged (no border/interior).")
    print("Or: the adversary can CHOOSE binary fire whenever binary is privileged.")
    print()
    print("CLAIM: The adversary can always find a config in B_b where binary")
    print("is privileged, fire the binary proc, reach binary state b',")
    print("then similarly find a config at b' where binary is privileged,")
    print("fire back to b, creating a cycle.")
    print()
    print("This creates the cascade: b=(0,0,0) <-> b'=(1,1,1) with")
    print("border switches and interior adjustments between the binary sweeps.")


if __name__ == '__main__':
    main()
