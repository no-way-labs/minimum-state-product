"""
Focused check: do VALID SYSTEMS with sub-threshold product exist where
all binary procs have fc ≥ 4?

If no such system exists at n=5 (where M_5 = 96), then the answer is:
the sorry is provable because no valid system with sub-threshold product
and all binary fc ≥ 4 exists.

For n=5, ms=(2,3,2,3,2), product=72 < 108:
No valid system exists (since M_5 = 96 > 72).
So the good cycle in the sorry's context CAN'T come from a valid system.

Wait — the sorry IS inside a proof that assumes a valid system exists.
The system's good cycle satisfies the hypotheses. We need to show the
hypotheses are contradictory.

But with M_5 = 96: no valid system with product < 96 exists. And
sub-threshold for n=5 is product < 108. So valid systems with
96 ≤ product < 108 DO exist (M_5 = 96).

For the sorry: we're assuming a valid system with product < 4·3^(n-2).
We need to show that in its good cycle, not all binary procs have fc ≥ 4.

For n=5: all valid systems with product < 108 and ≥ 3 binary:
  - product = 96: ms=(2,2,2,3,4) and permutations. M_5 = 96. ✓ valid.
    Binary at 0,1,2 (3 consecutive!). fc distribution? Let's check.
  - product = 72: ms=(2,2,2,3,3) and permutations. M_5 = 96 > 72. ✗ no valid system.

So for n=5, the only sub-threshold multiset with ≥ 3 binary that has valid
systems is ms=(2,2,2,3,4), which has 3 CONSECUTIVE binary. The non-consecutive
case (like (2,3,2,3,2)) has product 72 < 96, so NO valid system exists.

For the sorry: it doesn't distinguish consecutive from non-consecutive.
It needs to work for ALL sub-threshold multisets with ≥ 3 binary.

KEY QUESTION: In valid systems with M_5 = 96 (ms=(2,2,2,3,4)),
what are the binary fire counts in the good cycle?

Let me check using the verifier.
"""

import sys
sys.path.insert(0, '.')
from verifier import verify_system, all_configs, privileged_set, apply_move
from collections import Counter

def extract_good_cycle_info(ms, fs):
    """Extract good cycle and fire count info from a valid system."""
    n = len(ms)
    result = verify_system(ms, fs)
    if not result['valid']:
        return None

    good = result.get('good_configs', set())
    if not good:
        return None

    # Build successor map
    succ = {}
    mover_map = {}
    for c in good:
        priv = privileged_set(c, fs, ms)
        if len(priv) != 1:
            return None
        p = priv[0]
        c2 = apply_move(c, p, fs, ms)
        succ[c] = c2
        mover_map[c] = p

    # Find cycle
    start = next(iter(good))
    cycle = [start]
    cur = succ[start]
    while cur != start:
        cycle.append(cur)
        cur = succ[cur]

    movers = [mover_map[c] for c in cycle]
    fc = Counter(movers)

    binary_procs = [i for i in range(n) if ms[i] == 2]
    binary_fcs = {b: fc[b] for b in binary_procs}

    return {
        'CL': len(cycle),
        'fc': dict(fc),
        'binary_fcs': binary_fcs,
        'all_binary_fc4': all(f >= 4 for f in binary_fcs.values()),
        'movers': movers
    }

# Check the M_5 = 96 witness: ms = (2,2,2,3,4)
# From memory: valid system exists.
# Let's construct it using the verifier's search or known witness.

# The M_5 witness at product 96: ms=(2,2,2,3,4), consecutive binary at P0,P1,P2.
# From the memory: "M_5=96 witness (ms=[2,2,2,3,4], consecutive binary at P0,P1,P2)"

# I don't have the exact transition functions. Let me check what fire counts
# are typical for small valid systems.

# For n=3: ms=(2,3,3), product=18 = 2·3^1, M_3 valid.
# Sol 3 v1: ms=(2,3,...,3), product=2·3^(n-1).
# For n=3: product = 2·3^2 = 18.
# CUP-2: ms=(2,3,...,3,2), product = 4·3^(n-2).
# For n=5: product = 4·27 = 108. AT threshold, not sub.

# For Sol 3 v1 at n=5: ms=(2,3,3,3,3), product=162. Above threshold.

# Let me think about what systems have ≥ 3 binary.
# ms=(2,2,2,3,4): the only sub-threshold multiset with ≥3 binary and valid system at n=5.

# Actually, the M_5=96 result means the MINIMUM product with a valid system at n=5 is 96.
# The multiset achieving this is ms=(2,2,2,3,4) or rotations.
# 2^3 * 3 * 4 = 96.

# For ANY valid system with this ms: what's the good cycle structure?
# CL = |good configs|. For ms=(2,2,2,3,4), CL ≤ 96.
# With 3 binary procs (fc even ≥ 2 each) and 2 non-binary procs:
# Sum fc = CL.

# Let's check: is CL = 2n = 10 for this system? That would give all fc = 2.
# Or is CL larger?

# From the memory: M_5=96 has "valid system at ms=(2,2,2,3,4)" and the
# good cycle is part of the witness.

print("Analysis of the sorry proof:")
print()
print("The sorry needs: ∀ binary b, fc(b) ≥ 4 → False")
print()
print("Available hypotheses include _hq with fc(_q) ≥ 3.")
print("This _hq comes from CL > 2n (the sorry is called in the")
print("CL = 2n proof, specifically in the CL ≤ 2n direction).")
print()
print("KEY INSIGHT: The _q with fc ≥ 3 was extracted from CL > 2n.")
print("With all binary fc ≥ 4: CL ≥ 2n + 2B ≥ 2n + 6.")
print("So _q with fc ≥ 3 definitely exists.")
print()
print("But we also need False. The argument must show that the")
print("COMBINATION of all binary fc ≥ 4, fc(_q) ≥ 3, ZW, cw > 0,")
print("and the other hypotheses is contradictory.")
print()
print("PROPOSED PROOF:")
print()
print("1. Binary stay = 0 (from distinct configs + binary toggle).")
print("2. cwMoveCountAt(b) + ccwMoveCountAt(b) = fc(b) ≥ 4 for binary b.")
print("3. Under ZW: edgeNetFlow(p) = 0 for all p.")
print("   So cwMoveCountAt(p) = ccwMoveCountAt(right p) for all p.")
print("4. Consider the edgeTraversalCount at each edge:")
print("   ET(p, right p) = cwMoveCountAt(p) + ccwMoveCountAt(right p)")
print("                   = 2 * cwMoveCountAt(p)  (under ZW)")
print("5. All ET are even.")
print("6. For binary b: ET(left b, b) + ET(b, right b) = 2*fc(b) ≥ 8.")
print("7. The walk graph (edges with ET > 0) must be connected (all procs fire).")
print()
print("Can we show ≥ 2 dead edges? That would disconnect the walk.")
print()
print("For binary b with fc = 4: cwMoveCountAt(b) + ccwMoveCountAt(b) = 4.")
print("If cwMoveCountAt(b) = 4, ccwMoveCountAt(b) = 0:")
print("   ET(left b, b) = 2*ccwMoveCountAt(b) = 0. Dead edge!")
print("If cwMoveCountAt(b) = 0, ccwMoveCountAt(b) = 4:")
print("   ET(b, right b) = 2*cwMoveCountAt(b) = 0. Dead edge!")
print()
print("But both can be ≥ 2: no dead edge from b.")
print()
print("HOWEVER: the walk is a connected CLOSED path on the ring.")
print("Under ZW: cwStepCount = ccwStepCount.")
print()
print("For each proc p: outgoing(p) = incoming(p).")
print("Where outgoing = cwMoveCountAt(p) + ccwMoveCountAt(p) + stay(p) = fc(p).")
print("And incoming = cwMoveCountAt(left p) + ccwMoveCountAt(right p) + stay(p).")
print("Under ZW: cwMoveCountAt(left p) = ccwMoveCountAt(p) (edge balance at (left p, p)).")
print("So incoming = ccwMoveCountAt(p) + cwMoveCountAt(p) + stay(p) - stay(p) + stay(p)")
print("Hmm, need to think about this more carefully.")
print()
print("Actually: fireCount_eq_moveCount_partition gives:")
print("  fc(p) = cwMoveCountAt(p) + ccwMoveCountAt(p) + stayMoveCountAt(p)")
print()
print("And outgoingMoveCount_eq_incomingMoveCount gives:")
print("  cwMoveCountAt(p) + ccwMoveCountAt(p) + stayMoveCountAt(p)")
print("  = cwMoveCountAt(left p) + ccwMoveCountAt(right p) + stayMoveCountAt(p)")
print("Wait, the incoming moves to p are:")
print("  - CW from left(p): cwMoveCountAt(left p)")
print("  - CCW from right(p): ccwMoveCountAt(right p)")
print("  - Stay at p: stayMoveCountAt(p)")
print()
print("Under ZW: cwMoveCountAt(left p) = ccwMoveCountAt(p).")
print("And ccwMoveCountAt(right p) = cwMoveCountAt(p).")
print("So incoming = ccwMoveCountAt(p) + cwMoveCountAt(p) + stayMoveCountAt(p) = fc(p).")
print("This is just flow conservation. No new info.")
print()
print("=== FINAL ANSWER ===")
print()
print("After extensive analysis, the proof should use the")
print("ENTRY CONFLICT AT A TERNARY PROC via the following mechanism:")
print()
print("Pick any binary b with fc(b) ≥ 4. Consider t = right(b).")
print("Binary b fires ≥ 4 times, creating ≥ 4 phases between firings.")
print("In each phase, b's value is fixed.")
print()
print("t has ≥ 4 transitions of b's value in its left context.")
print("At the boundaries of phases (just before b fires and just after):")
print("  t's left context L = b_val (before toggle) or 1-b_val (after).")
print()
print("With fc(b) = 4:")
print("  - 2 phases with b_val = 0: L = 0 throughout each phase")
print("  - 2 phases with b_val = 1: L = 1 throughout each phase")
print()
print("During a b_val=0 phase: t's non-mover contexts all have L=0.")
print("When t triggers b's firing (if t is the trigger): t's mover")
print("context has L=0.")
print()
print("After b fires (0→1): t's non-mover context has L=1.")
print("When t triggers b's next firing (from 1→0): t's mover context has L=1.")
print("After b fires (1→0): t's non-mover context has L=0.")
print()
print("So for L=0: t has mover contexts (from triggering) and non-mover")
print("contexts (during phases + after 1→0 firings).")
print()
print("For L=1: similar.")
print()
print("The entry conflict requires same (L,S,R) at mover and non-mover.")
print("This happens when the S,R values at a trigger event match those")
print("at a non-mover event with the same L.")
print()
print("With m_t ≥ 3 and m_{right t} ≥ 2: the (S,R) space has ≥ 6 pairs.")
print("With only 2 mover events per L-value: not enough for pigeonhole.")
print()
print("CONCLUSION: Pure pigeonhole at a single proc doesn't work.")
print("The proof likely needs a GLOBAL argument (ring-level constraint).")
print("The most promising route: show that the walk structure under ZW")
print("with all binary fc ≥ 4 forces the mover word to have a specific")
print("form that admits entry conflict at some proc via the existing")
print("infrastructure (TernaryPhaseEC, phase_dispatch_ec, etc.).")
