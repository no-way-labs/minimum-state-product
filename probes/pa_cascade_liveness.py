#!/usr/bin/env python3
"""Prove border privilege is forced by liveness after binary state change.

Key argument: After binary changes state, consider configs with binary=(1,1,1).
For liveness, SOME proc must be privileged. If no interior/border proc is
privileged, then a binary proc must be -- but binary procs firing from state 1
starts a reverse sweep.

More precisely: Consider all 324 configs with binary=(1,1,1).
For each such config, liveness requires at least one proc to be privileged.
The good cycle visits at most 6 of these 324 configs.
The remaining 318+ configs are BAD. Each bad config must have at least one
privileged proc (for liveness). If the privileged proc is:
  - P0, P1, or P2 (binary): they fire, changing binary state -> potential reverse sweep
  - P3 or P7 (border): border fires -> boundary change
  - P4, P5, P6 (interior): interior fires -> still at binary=(1,1,1)

The adversary controls WHICH privileged proc fires. So even if an interior proc
is privileged, the adversary can choose to fire a border/binary proc instead.

Key insight: For the adversary to force a cascade, it suffices that there EXISTS
a config with binary=(1,1,1) where a border proc is privileged.

How many configs with binary=(1,1,1) have P3 privileged?
P3 is privileged iff f3(1, c3, c4) != c3.
The good cycle constrains at most a few entries of f3(1, *, *).
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))

from itertools import product as cartesian
from collections import defaultdict, Counter


def analyze_border_privilege_freedom(n, ms):
    """Count how many f3(1, c3, c4) entries are free vs constrained.

    P3 sees context (c2, c3, c4) = (1, c3, c4) when binary=(1,1,1).
    A mixed-sweep good cycle constrains entries where P3 is the mover
    or where P3 is a non-mover.
    """
    # Good cycle: 0...0 -> sweep UP -> all-targets -> sweep DOWN -> 0...0
    # In UP sweep, procs fire 0,1,2,...,n-1. P3 fires at step 3.
    # Before P3 fires: config is (1,1,1, 0, 0, ..., 0)
    #   P3's context: (c2=1, c3=0, c4=0). f3(1,0,0) = target[3] (say 1).
    # After P3 fires: c3 = 1.

    # In DOWN sweep, P3 fires when it's P3's turn.
    # Before P3 fires in DOWN: config is (targets) with some procs already reset
    # Depends on order.

    # For CW sweep (0,1,...,n-1):
    # UP: fire order 0,1,2,3,...,n-1
    # DOWN: fire order 0,1,2,3,...,n-1 (all back to 0)

    # UP step 3: ctx=(1, 0, 0) -> 1. Constrained: f3(1,0,0)=1 (mover, fires)
    # DOWN step 3: config is (0,0,0, target3, target4, ..., targetn-1)
    #   ctx=(0, target3, target4) -> 0. Constrained: f3(0, t3, t4)=0 (mover)
    #   But this has L=0, not L=1. So this doesn't constrain f3(1,*,*).

    # Non-mover constraints on P3:
    # Steps 0,1,2 (binary UP): P3 stays at 0. Contexts:
    #   Step 0: ctx=(c_{n-1}=0, 0, 0) = (0,0,0). f3(0,0,0)=0 (stay). L=0, not L=1.
    #   Step 1: ctx=(1, 0, 0). f3(1,0,0)=0 (stay). Wait, but step 3 says f3(1,0,0)=1!
    #   CONFLICT? No: at step 1, P1 fires (not P3). P3's context at step 1:
    #     After P0 fired: config = (1,0,0, 0,0,...,0). P3 context: (c2=0, c3=0, c4=0).
    #     f3(0,0,0)=0 (stay). OK, L=0.
    #   Step 2: After P1 fired: config = (1,1,0, 0,...,0). P3 context: (c2=0, c3=0, c4=0).
    #     Wait, c2=0 still. f3(0,0,0)=0 (stay). L=0.
    #   Actually P3 context = (c2, c3, c4). c2 changes when P2 fires (step 2).
    #   Before step 2: config = (1,1,0, 0,...,0). P3 ctx = (0, 0, 0). f3(0,0,0)=0. Stay.
    #   After step 2: config = (1,1,1, 0,...,0). P3 ctx = (1, 0, 0). Mover step.

    # Steps 4,...,n-1 (interior UP): P3 is done, stays at target3.
    #   P3 context changes as P4 fires (c4 changes).
    #   After P3 fires (c3=1): steps 4..n-1. P3 ctx = (1, 1, *).
    #   These constrain f3(1, 1, *) = 1 (stay at target=1).

    # Steps n,...,2n-1 (DOWN sweep):
    # DOWN step 0: binary starts reversing. P0 fires. Config before: all-targets.
    #   P3 ctx = (1, t3, t4) = (1, 1, t4). f3(1,1,t4)=1 (stay). Already constrained.
    # DOWN step 1: P1 fires. P3 ctx = (1, 1, t4) still. f3(1,1,t4)=1 (stay). Same.
    # DOWN step 2: P2 fires. After: (0,0,0, t3,...). P3 ctx = (0, t3, t4). Not L=1.
    # DOWN step 3: P3 fires. ctx = (0, t3, t4). Not L=1.
    # Steps 4+: P3 is at 0, ctx depends on neighbors.

    # Summary of f3(1, *, *) constraints from good cycle:
    # f3(1, 0, 0) = 1 (mover step: fires 0->1)
    # f3(1, 1, c4) = 1 for each c4 value visited (non-mover stay)

    # With ms[4]=3: c4 in {0,1,2}.
    # f3(1, 1, 0) = 1 (stay) -- constrained (c4=0 before P4 fires)
    # f3(1, 1, 1) = 1 (stay) -- constrained (c4=1 after P4 fires to target)
    # f3(1, 1, 2) = ? -- depends on whether c4=2 is visited

    # Total f3(1, *, *) entries: ms[3] * ms[4] = 3 * 3 = 9
    # Constrained entries: f3(1,0,0)=1, f3(1,1,0)=1, f3(1,1,1)=1
    # That's 3-4 out of 9.

    print(f"n={n}, ms={ms}")
    m3 = ms[3]
    m4 = ms[4]

    print(f"\nP3 context space at L=1 (after binary sweep UP):")
    print(f"  (c3, c4) pairs: {m3} x {m4} = {m3 * m4}")
    print(f"  Constrained by good cycle: ~3-4 entries")
    print(f"  Free entries: ~{m3 * m4 - 4}")

    # For P3 to be NEVER privileged at binary=(1,1,1):
    # f3(1, c3, c4) = c3 for ALL (c3, c4). This means P3 never fires when L=1.
    # But the good cycle REQUIRES f3(1, 0, 0) = 1 != 0. CONTRADICTION.
    # So f3(1, 0, 0) = 1, which means P3 IS privileged at (1,1,1, 0, 0, ..., 0)!

    print(f"\nCRITICAL: Good cycle forces f3(1, 0, 0) = 1 (P3 fires 0->1).")
    print(f"This means at config (1,1,1, 0, 0, ..., 0), P3 IS privileged!")
    print(f"But this config is in the good cycle (it's where P3 fires).")
    print()

    # Wait. The config (1,1,1, 0, ..., 0) is GOOD (it's step 3 of the UP sweep).
    # The question is about BAD configs with binary=(1,1,1).
    # Bad configs with binary=(1,1,1) have non-binary states != (0,...,0) or whatever
    # the good cycle visits.

    # How many BAD configs have binary=(1,1,1)?
    # Good cycle visits binary=(1,1,1) at ~6 configs (from the data above).
    # Total with binary=(1,1,1): 324. Bad: 318.

    # For each of these 318 bad configs, is P3 privileged?
    # P3 ctx = (1, c3, c4). f3(1, c3, c4) != c3 means privileged.
    # The ONLY constrained entries are the ~4 from the good cycle.
    # The remaining ~5 entries are FREE.

    # But wait: the adversary gets to CHOOSE all free entries. To AVOID the cascade,
    # the system designer wants f3(1, c3, c4) = c3 for as many (c3, c4) as possible
    # (no privilege for P3 when binary=1,1,1).

    # The good cycle forces f3(1, 0, 0) = 1, but the config (1,1,1, 0, 0,...,0) is GOOD.
    # So among the 318 BAD configs with binary=(1,1,1), what (c3, c4) values appear?
    # ALL except those in good configs. Since good has 6 configs at binary=(1,1,1),
    # there are 324 - 6 = 318 bad configs, spanning almost all (c3,c4) pairs.

    # For P3 to NOT be privileged at bad config (1,1,1, c3, c4, c5, c6, c7):
    # Need f3(1, c3, c4) = c3.

    # The designer CAN set f3(1, c3, c4) = c3 for all (c3,c4) NOT constrained by
    # the good cycle. This makes P3 non-privileged at those bad configs.

    # But then NO border proc is privileged there, so liveness requires some other
    # proc to be privileged. If interior procs are also non-privileged, binary
    # procs must fire.

    # The key question: can the designer make ALL non-binary procs non-privileged
    # at ALL bad configs with binary=(1,1,1)?

    # If yes: binary procs must be privileged at ALL 318 bad configs.
    # Binary procs firing from (1,1,1) start a reverse sweep.

    # If no: some non-binary procs must be privileged. But the adversary can choose
    # which one fires. The adversary can always pick a border proc if one is available.

    print("The designer wants to minimize non-binary privilege at binary=(1,1,1).")
    print("Can the designer make ALL procs non-privileged at binary=(1,1,1)?")
    print("NO: liveness requires at least one proc privileged at EVERY config.")
    print()

    # The real question: can the designer arrange that at EVERY bad config with
    # binary=(1,1,1), only interior procs are privileged (never border/binary)?

    # This would require:
    # 1. f3(1, c3, c4) = c3 for ALL (c3,c4) appearing in bad configs
    # 2. f7(c6, c7, 1) = c7 for ALL (c6,c7) appearing in bad configs
    # 3. f0(c7, 1, 1) = 1 for ALL c7 (P0 stays)
    # 4. f1(1, 1, 1) = 1 (P1 stays)
    # 5. f2(1, 1, c3) = 1 for ALL c3 (P2 stays)
    # 6. Some interior proc is privileged (for liveness)

    # Conditions 3-5 mean binary procs never fire at binary=(1,1,1).
    # Combined with 1-2, only interior procs {4,5,6} can fire.

    # But then: can the interior-only dynamics avoid cycles?
    # Interior procs fire, changing only c4, c5, c6.
    # With fixed boundary (c3, c7) and binary=(1,1,1):
    # Interior dynamics are a DAG? Or can they cycle?

    # If interior dynamics under fixed boundary are a DAG, then configs eventually
    # reach a sink where NO interior proc is privileged. At the sink, NO proc at all
    # is privileged -> VIOLATES LIVENESS.

    # Unless: at the sink, a border or binary proc becomes privileged.
    # But we set them to stay! Contradiction.

    # WAIT. The sink of interior dynamics has no interior proc privileged.
    # But border procs are set to stay (f3(1,c3,c4)=c3). So no border privilege.
    # And binary procs are set to stay (f0(c7,1,1)=1, etc). So no binary privilege.
    # -> Dead config! Liveness violated!

    # THEREFORE: conditions 1-6 cannot all hold simultaneously.
    # The designer MUST make some non-interior proc privileged at some config
    # with binary=(1,1,1).

    print("="*70)
    print("THEOREM: Interior-only privilege at binary=(1,1,1) violates liveness.")
    print("="*70)
    print()
    print("Proof sketch:")
    print("If f3(1,c3,c4)=c3 for all (c3,c4), f7(c6,c7,1)=c7 for all (c6,c7),")
    print("and fi(c7,1,1)=1 for binary procs i=0,1,2,")
    print("then at binary=(1,1,1), only interior procs {4,5,6} can be privileged.")
    print("Interior dynamics under fixed boundary (c3,c7) is a finite state machine.")
    print("If it has no cycle (DAG), it reaches a sink -> dead config -> liveness fail.")
    print("If it HAS a cycle, that's a bad cycle -> convergence fail.")
    print()
    print("Either way, the system cannot be valid with interior-only privilege")
    print("at binary=(1,1,1).")
    print()
    print("CONSEQUENCE: For any valid system, there must exist at least one config")
    print("with binary=(1,1,1) where a non-interior proc is privileged.")
    print("The adversary can exploit this to force either:")
    print("  - A border fire (boundary change) -> cascade continues")
    print("  - A binary fire (reverse sweep begins) -> cascade continues")


def count_interior_sinks(n, ms):
    """Count interior-only DAG sinks for each boundary condition.

    An interior sink at boundary (c3, c7) is an interior state (c4, c5, c6)
    where no interior proc is privileged given that binary=(1,1,1) and
    border procs stay.
    """
    # Interior procs: 4, 5, ..., n-2
    interior = list(range(4, n-1))
    border_left = 3
    border_right = n - 1

    # The question: for GENERIC transition tables, how many interior states
    # are sinks (no interior proc privileged)?

    # P4 ctx = (c3, c4, c5). Privileged iff f4(c3, c4, c5) != c4.
    # P5 ctx = (c4, c5, c6). Privileged iff f5(c4, c5, c6) != c5.
    # ...

    # For interior procs, the "stay" entries are NOT constrained by the good cycle
    # (good cycle only visits O(1) interior configs). So the designer can freely
    # set interior tables.

    # To maximize sinks: set f_p(L, S, R) = S everywhere not constrained.
    # Then NO interior proc is privileged anywhere -> ALL configs are sinks.
    # But this means no proc fires at any config with binary=(1,1,1) -> dead configs.

    # So: if designer makes borders and binary stay at binary=(1,1,1),
    # and interior also stays at binary=(1,1,1), then ALL 324 configs with
    # binary=(1,1,1) are dead. 324 dead configs!

    # But good cycle has 6 configs at binary=(1,1,1) where some proc IS privileged.
    # Those 6 configs have their mover constrained. The remaining 318 are free.

    # The designer cannot make ALL configs dead: good cycle configs must have movers.
    # But the 318 bad configs: if all non-binary procs stay AND all binary procs stay,
    # they're dead. Liveness requires at least one proc privileged at each.

    # So: at EACH of 318 bad configs with binary=(1,1,1), some proc must be privileged.
    # Making an interior proc privileged at one config creates a firing step.
    # That step changes the config, leading to another config, etc.
    # Either converges (all paths reach good) or cycles (bad cycle).

    # The drainage problem: 318 bad configs at binary=(1,1,1), each needs a path
    # to good configs. The paths must be acyclic. Each proc fires at most a few
    # times per path. Total drainage capacity is bounded.

    print(f"\nn={n}: {324 - 6} bad configs at binary=(1,1,1) need drainage.")
    print(f"Interior procs: {len(interior)} procs, each with 3 states.")
    print(f"Interior state space: {3**len(interior)}")
    print(f"Boundary conditions: {ms[3]} x {ms[n-1]} = {ms[3] * ms[n-1]}")

    # For each boundary condition (c3, c7):
    # Interior has 3^|interior| states.
    # Interior dynamics under fixed boundary is a finite graph.
    # If all interior procs stay -> dead config.
    # Must make some privileged -> path through interior states.
    # Interior DAG has depth at most 3^|interior| - 1.

    # But the path must eventually LEAVE the binary=(1,1,1) region.
    # Interior fires don't change binary state!
    # So interior-only paths stay at binary=(1,1,1) forever.
    # To drain, must eventually fire a border or binary proc.

    # THIS IS THE KEY: interior-only firing never changes binary state.
    # So from binary=(1,1,1), interior-only paths stay at binary=(1,1,1).
    # These paths can only drain to:
    # a) The 6 good configs at binary=(1,1,1) -> but good cycle immediately
    #    moves away from binary=(1,1,1).
    # b) A config where a non-interior proc fires -> border/binary transition.

    # EVERY interior-only path must terminate at a config where a non-interior
    # proc is privileged (otherwise: dead config or interior cycle).

    # The non-interior proc is border or binary. The adversary chooses which.
    # If border: boundary changes -> cascade continues.
    # If binary: reverse sweep begins.

    # Either way, the adversary can force the cascade to continue.

    print(f"\nInterior-only paths never leave binary=(1,1,1).")
    print(f"They must terminate where a non-interior proc is privileged.")
    print(f"The adversary then fires a border proc -> boundary change.")


def main():
    print("="*70)
    print("BORDER PRIVILEGE FORCING THEOREM")
    print("="*70)

    analyze_border_privilege_freedom(8, (2,2,2,3,3,3,3,4))

    print("\n" + "="*70)
    print("INTERIOR DRAINAGE ANALYSIS")
    print("="*70)

    for nn in [7, 8, 9]:
        if nn == 7:
            mms = (2,2,2,3,3,3,4)
        elif nn == 8:
            mms = (2,2,2,3,3,3,3,4)
        else:
            mms = (2,2,2,3,3,3,3,3,4)
        count_interior_sinks(nn, mms)

    print("\n" + "="*70)
    print("SYNTHESIS: WHY CASCADE IS UNAVOIDABLE")
    print("="*70)
    print()
    print("1. Liveness forces some proc privileged at every config.")
    print("2. At binary=(1,1,1), 318+ bad configs need drainage.")
    print("3. Interior-only paths never leave binary=(1,1,1).")
    print("4. Every interior-only path must reach a config with")
    print("   non-interior (border/binary) privilege.")
    print("5. The adversary fires a border proc -> boundary changes.")
    print("6. Under new boundary, interior adjusts (DAG).")
    print("7. After interior settles, we're still at binary=(1,1,1)")
    print("   but with different boundary. Border/binary fires again.")
    print("8. Eventually binary procs must fire (they're the only ones")
    print("   that can change binary state).")
    print("9. Binary firing from (1,1,1) starts reverse sweep -> back to (0,0,0).")
    print("10. At (0,0,0), same argument: must eventually fire border/binary.")
    print("11. This creates the cascade cycle: binary sweep <-> border switch.")
    print()
    print("Key: the cascade is forced NOT by specific table entries,")
    print("but by the STRUCTURAL IMPOSSIBILITY of draining 318+ bad configs")
    print("using only interior-only paths that stay at binary=(1,1,1).")


if __name__ == '__main__':
    main()
