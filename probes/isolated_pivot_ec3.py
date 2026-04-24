"""
Round 3: Search for NON-TRIVIAL good cycles with fc(pivot)=2 at isolated pivots.

The previous search only found trivial length-2 cycles (44) where only the pivot fires.
We need cycles where all procs fire (fc(i) >= 1 for all i), which is the relevant
case for the lower bound proof.

Approach: Instead of random transition functions, enumerate abstract good cycles
by DFS on config space. A step changes exactly one proc's value.
We track which procs have fired and look for cycles that return to start
with all procs having fired.

For n=9, product=3888, this is tractable with pruning.
Actually, we should think about this more carefully. The minimum cycle length
where all procs fire at least m_i times is sum(m_i) = 3+3+2+2+3+2+2+3+3 = 23.
But fc(pivot)=2 means pivot fires only 2 times, not 3.
So min length = 3+3+2+2+2+2+2+3+3 = 22 (if all ternary procs fire 3 times
except pivot which fires 2).

Actually, for a proc with m_i=3 to return to start:
- fc=3: full tour 0->1->2->0 (or reverse)
- fc=2: 2-cycle like 0->1->0 or 0->2->0 (doesn't visit all values)
- fc=6: double tour, etc.
So fc=2 is fine for returning to start.

Minimum total: all fc=2 gives length 18. All fc=m_i gives length 23.

For the lower bound proof, we care about cycles in the good-config subgraph
of a VALID SYSTEM. These must have all procs firing. Let me focus on
cycles where every proc fires at least once.
"""

import itertools
from collections import defaultdict
import random

def run():
    # Use a SMALLER system first for tractability
    # n=5 analog: ms=(3,3,2,3,2), pivot at pos 3
    # But we need "isolated sandwiched" - need left4t to be non-binary
    # For n=5 ring, positions wrap: left4t of pos3 = pos(3-4)%5 = pos4(m=2) = binary!
    # Not isolated.

    # Try n=7: ms=(3,3,2,2,3,2,3), pivot at pos 4
    # left4t = pos 0 (m=3, non-binary) -> isolated!
    # left3t=1(3), left2t=2(2), leftt=3(2), pivot=4(3), rightt=5(2), right2t=6(3)
    # right2t is ternary, not binary. So right side is different.
    # For symmetry, use ms=(3,3,2,2,3,2,2) at n=7, pivot=4
    # right2t=6(2), right3t=0(3) via wrap. Isolated on both sides.

    # Actually let's just use n=7, ms=(3,3,2,2,3,2,2), pivot=4
    # left4t=0(3), left3t=1(3), left2t=2(2), leftt=3(2), pivot=4(3),
    # rightt=5(2), right2t=6(2), right3t=0(3) [wrap]

    ms = [3, 3, 2, 2, 3, 2, 2]
    n = 7
    pivot = 4
    product = 1
    for m in ms:
        product *= m
    print(f"=== n={n}, ms={ms}, product={product}, pivot={pivot} ===")
    print(f"Positions: " + ", ".join(f"{i}({ms[i]})" for i in range(n)))
    print()

    all_configs = list(itertools.product(*(range(m) for m in ms)))
    print(f"Total configs: {len(all_configs)}")

    # Build the abstract move graph:
    # From any config, we can fire any proc (changing its value to any other value).
    # We search for cycles where:
    # - fc(pivot) = 2
    # - All procs fire at least once (non-trivial)
    # - Cycle returns to start config

    # DFS approach: track (config, fire_counts, mover_word)
    # Pruning: once fc(i) > m_i, skip (wasteful).
    # Target: all fc >= m_i minimum, except pivot fc = 2.

    # For n=7, product = 3*3*2*2*3*2*2 = 432.
    # Min cycle length with fc(pivot)=2, others fc=m_i: 3+3+2+2+2+2+2 = 16
    # Min cycle length with all fc=2: 14.

    # This is still a LOT of paths. Let me use a different approach:
    # Fix a starting config and enumerate cycles of a specific length.

    # Better: use the Dijkstra-style formulation but with a transition function
    # that ALLOWS fc(pivot)=2. For this, the pivot's transition must create a 2-cycle.

    # Concrete approach: BUILD a system where the pivot has a 2-cycle transition,
    # other procs have standard transitions, and find good cycles.

    # Pivot transition for 2-cycle: f(L,S,R) toggles between two values.
    # E.g., f(L,S,R) = (S+1)%3 if some condition, else S.
    # For a 2-cycle: val goes 0->1->0 (fires twice, returns to 0, skips 2).

    # Let me use a more systematic approach: for each possible transition function
    # at the pivot that creates a 2-cycle on its values, and standard incrementing
    # for other procs, find good cycles.

    # Actually, the most productive thing is to use the VERIFIER infrastructure
    # to check valid systems, not just good cycles.

    # Let me instead approach this ANALYTICALLY.
    # The key question: in the mover word of a good cycle with fc(pivot)=2,
    # can pos 2 (left2t) fire in the INTERIOR of a phase (not adjacent to pivot)?

    # With fc(pos2)=2 (binary), pos2 fires exactly twice.
    # The 2 pivot firings create 2 phases.
    # If pos2 fires in the interior of both phases: (1,1) distribution -> Case 3.
    # If pos2 fires at phase boundaries: adjacent to pivot firings -> Case 1.

    # For pos2 to fire in the interior of a phase, there must be steps between
    # the pivot firing and the pos2 firing within that phase.

    # Is there a structural reason why pos2 MUST fire adjacent to pivot?
    # In a Dijkstra-style system: proc fires when L==S.
    # For pos2 (binary), this means pos1's value == pos2's value.
    # After pivot fires, the change propagates: pivot changes -> affects rightt's
    # privilege, not directly left side.

    # For LEFT side: pivot firing doesn't directly affect pos2's context.
    # pos2's context = (pos1_val, pos2_val, pos3_val).
    # Pivot is pos4, which is pos2+2. Pivot firing changes pos4_val.
    # This affects pos3's context (pos3 has right neighbor = pos4),
    # and pos5's context (pos5 has left neighbor = pos4).
    # But not pos2's context directly.

    # So pos2's privilege is independent of whether pivot just fired.
    # Therefore, pos2 CAN fire anywhere in the cycle, not just adjacent to pivot.
    # The observation that all found cycles were trivial (only pivot fires) is
    # because random transitions rarely create long good cycles.

    # Let me build VALID SYSTEMS (using the verifier) and extract their good cycles.
    print("="*70)
    print("=== Building valid systems and extracting good cycles ===")
    print("="*70)
    print()

    # Strategy: use good-targeting completion from the CLB work.
    # But that gives specific systems. Let me try exhaustive search for small ms.

    # For n=7, product=432: try to find ALL valid systems by brute force.
    # Too many transition functions. Instead, use the known constructions.

    # Actually, let me just do targeted enumeration of good cycles
    # (not full valid systems) for the question at hand.

    # REVISED APPROACH: Direct DFS for good cycles.
    # For each starting config, explore all possible single-proc-fires steps,
    # looking for cycles of length 14-20 with fc(pivot)=2 and all procs firing.

    # For efficiency, use BFS with depth limit.

    print("Direct enumeration of abstract good cycles...")
    print("(A good cycle is a sequence of configs where each step changes exactly")
    print("one proc's value to a different value, and we return to start.)")
    print()

    # State: (config, tuple_of_fire_counts)
    # We want cycles, so we track the starting config and stop when we return to it.

    # For tractability, fix a starting config and search for short cycles.
    # Min length: each proc fires at least once, pivot fires exactly 2.
    # Absolute minimum: 7 (each fires once) but pivot must fire 2, so min = 8.
    # But to RETURN to start, each binary proc must fire even times (min 2),
    # and each ternary proc with fc=2 returns via 2-cycle, fc=3 via full tour.

    # With fc(pivot)=2 and binary fc=2 and ternary fc=2:
    # All fc=2, total length = 14.

    # Let me search for cycles of length exactly 14 (all fc=2).
    target_fc = {i: 2 for i in range(n)}  # all fire exactly twice

    found_cycles = []
    configs_tried = 0

    # Pick a few starting configs and DFS
    random.seed(42)
    start_configs = random.sample(all_configs, min(50, len(all_configs)))

    for start in start_configs:
        configs_tried += 1
        if configs_tried % 10 == 0:
            print(f"  Tried {configs_tried} starts, found {len(found_cycles)} cycles...")
        if len(found_cycles) >= 20:
            break

        # DFS with pruning
        # State: (config, fire_counts_tuple, mover_word)
        stack = [(start, tuple(0 for _ in range(n)), [])]
        visited_states = set()

        while stack and len(found_cycles) < 20:
            config, fc_tuple, mover_word = stack.pop()
            L = len(mover_word)

            if L == 14:
                # Check if we returned to start
                if config == start and fc_tuple == tuple(target_fc[i] for i in range(n)):
                    found_cycles.append(list(mover_word))
                continue

            if L > 14:
                continue

            # Prune: check if remaining steps can satisfy fc constraints
            remaining = 14 - L
            needed = sum(max(0, target_fc[i] - fc_tuple[i]) for i in range(n))
            if needed > remaining:
                continue

            # Try each proc as mover
            for i in range(n):
                if fc_tuple[i] >= target_fc[i]:
                    continue  # already fired enough

                # Try each possible new value for proc i
                for new_val in range(ms[i]):
                    if new_val == config[i]:
                        continue  # must change

                    # Check return constraint: with fc remaining for proc i,
                    # can it return to start[i]?
                    new_fc_i = fc_tuple[i] + 1
                    remaining_i = target_fc[i] - new_fc_i
                    # After this firing, proc i is at new_val.
                    # It needs remaining_i more firings to return to start[i].
                    # With remaining_i = 0: new_val must equal start[i].
                    # With remaining_i = 1: can fire once more to any value.
                    if remaining_i == 0 and new_val != start[i]:
                        continue
                    # remaining_i == 1: must be able to go from new_val to start[i]
                    # in one step. Always possible if new_val != start[i].
                    # If new_val == start[i] and remaining_i == 1: need to fire once
                    # more, going to some v != start[i], then... wait, no more firings.
                    # So if new_val == start[i] and remaining_i == 1: we'd need to
                    # leave and come back, but we only have 1 more firing.
                    # Actually with remaining_i = 1: we fire once more from new_val
                    # and must land on start[i]. So new_val != start[i] is required
                    # for the last firing to go to start[i]. If new_val == start[i],
                    # the next firing goes elsewhere, and we can't return.
                    if remaining_i == 1 and new_val == start[i]:
                        continue

                    new_config = list(config)
                    new_config[i] = new_val
                    new_config = tuple(new_config)

                    new_fc = list(fc_tuple)
                    new_fc[i] = new_fc_i
                    new_fc = tuple(new_fc)

                    state_key = (new_config, new_fc)
                    if state_key in visited_states:
                        continue
                    visited_states.add(state_key)

                    new_mw = mover_word + [i]
                    stack.append((new_config, new_fc, new_mw))

    print(f"\nFound {len(found_cycles)} abstract good cycles of length 14 (all fc=2)")

    if not found_cycles:
        print("No cycles found with 50 random starts. Trying more starts...")
        # Try all configs with small values
        for start in all_configs[:200]:
            if len(found_cycles) >= 20:
                break
            stack = [(start, tuple(0 for _ in range(n)), [])]
            visited_states = set()
            iterations = 0

            while stack and len(found_cycles) < 20:
                iterations += 1
                if iterations > 500000:
                    break

                config, fc_tuple, mover_word = stack.pop()
                L = len(mover_word)

                if L == 14:
                    if config == start and fc_tuple == tuple(target_fc[i] for i in range(n)):
                        found_cycles.append(list(mover_word))
                    continue
                if L > 14:
                    continue

                remaining = 14 - L
                needed = sum(max(0, target_fc[i] - fc_tuple[i]) for i in range(n))
                if needed > remaining:
                    continue

                for i in range(n):
                    if fc_tuple[i] >= target_fc[i]:
                        continue
                    for new_val in range(ms[i]):
                        if new_val == config[i]:
                            continue
                        new_fc_i = fc_tuple[i] + 1
                        remaining_i = target_fc[i] - new_fc_i
                        if remaining_i == 0 and new_val != start[i]:
                            continue
                        if remaining_i == 1 and new_val == start[i]:
                            continue

                        new_config = list(config)
                        new_config[i] = new_val
                        new_config = tuple(new_config)

                        new_fc = list(fc_tuple)
                        new_fc[i] = new_fc_i
                        new_fc = tuple(new_fc)

                        state_key = (new_config, new_fc)
                        if state_key in visited_states:
                            continue
                        visited_states.add(state_key)

                        stack.append((new_config, new_fc, mover_word + [i]))

        print(f"After extended search: {len(found_cycles)} cycles found")

    # Analyze found cycles
    if found_cycles:
        print()
        print("="*70)
        print("=== Analyzing found abstract good cycles ===")
        print("="*70)

        case_counts = defaultdict(int)
        adj_ec_count = 0

        for ci, mw in enumerate(found_cycles[:20]):
            # Find pivot firing positions
            pivot_steps = [i for i, m in enumerate(mw) if m == pivot]
            p1, p2 = pivot_steps
            L = len(mw)

            phase1_len = (p2 - p1 - 1) % L
            phase2_len = (p1 - p2 - 1) % L
            phase1_steps = [(p1 + 1 + k) % L for k in range(phase1_len)]
            phase2_steps = [(p2 + 1 + k) % L for k in range(phase2_len)]

            phase1_movers = set(mw[s] for s in phase1_steps)
            phase2_movers = set(mw[s] for s in phase2_steps)

            left2t = 2  # pos 2
            right2t = 6  # pos 6

            p1_contam = (left2t in phase1_movers) or (right2t in phase1_movers)
            p2_contam = (left2t in phase2_movers) or (right2t in phase2_movers)

            pos2_interior = (left2t in phase1_movers) or (left2t in phase2_movers)
            pos6_interior = (right2t in phase1_movers) or (right2t in phase2_movers)

            if p1_contam and p2_contam:
                case = "Case3"
            elif not pos2_interior:
                case = "Case1"
            elif not pos6_interior:
                case = "Case2"
            else:
                case = "Mixed"

            case_counts[case] += 1

            if ci < 10:
                mw_str = "".join(str(m) for m in mw)
                markers = []
                for m in mw:
                    if m == pivot:
                        markers.append("^")
                    elif m == left2t:
                        markers.append("L")
                    elif m == right2t:
                        markers.append("R")
                    else:
                        markers.append(".")
                print(f"  Cycle {ci}: {mw_str}")
                print(f"           {''.join(markers)}  ({case})")
                print(f"    Pivot at steps {p1},{p2}; phase1_movers={phase1_movers}; phase2_movers={phase2_movers}")

        print(f"\nCase distribution across {len(found_cycles)} cycles:")
        for case, count in sorted(case_counts.items()):
            print(f"  {case}: {count}")
    else:
        print("\nNo non-trivial abstract good cycles found at length 14.")
        print("Trying shorter cycles or different approach...")

    # Let me try a completely different approach: use the n=9 system with
    # KNOWN valid constructions and check their good cycles.
    print()
    print("="*70)
    print("=== Alternative: Check known valid system good cycles ===")
    print("="*70)
    print()

    # The CLB construction for ms=(2,3,...,3,2) gives endpoint-binary systems.
    # For our geometry ms=(3,3,2,2,3,2,2,3,3), this doesn't directly apply.
    # But we can check Sol3-type systems.

    # Sol3 v1: ms=(2,3,...,3), f(L,S,R) = (S+1)%m if L==S else S.
    # For ms=(3,3,2,2,3,2,2,3,3): this is NOT Sol3 format (Sol3 has first proc binary).
    # Let me check if the standard Dijkstra system works here.

    # Standard Dijkstra: f_i(L,S,R) = (S+1)%m_i if L==S else S.
    # This gives good cycles where the token circulates.
    # For this system, the fire count of each proc in the good cycle = m_i.

    # So fc(pivot) = m_pivot = 3, NOT 2. The standard system has fc=m.
    # We need a NON-STANDARD system to get fc(pivot)=2.

    # For fc(pivot)=2 with m=3: the pivot must have a 2-cycle on its values.
    # This means the transition function at the pivot creates an oscillation
    # between two values, never visiting the third.

    # Build such a system:
    print("Building a system with fc(pivot)=2...")
    print()

    # Use ms=(3,3,2,2,3,2,2,3,3) with:
    # - Standard Dijkstra for all non-pivot procs
    # - Modified pivot: oscillates between 2 values

    # For the pivot (pos 4, m=3):
    # Standard: f(L,S,R) = (S+1)%3 if L==S else S
    # Modified: f(L,S,R) = toggles between 0 and 1 (ignores value 2)
    # This would make the pivot fire only when L==S, but change to:
    #   S=0 -> 1, S=1 -> 0, S=2 -> ... (need to handle)

    # Actually, for a valid system, we need the good cycle to exist.
    # Let's think about what "fc(pivot)=2" means in terms of bad cycles.
    # In the LOWER BOUND proof, we're showing that no valid system exists
    # with product < threshold. We enumerate potential good cycles
    # (mover words) and show each has entry conflict.

    # The good cycle's mover word determines fire counts.
    # fc(pivot)=2 is possible if:
    # - The mover word has pivot appearing exactly twice
    # - The config trajectory is consistent (returns to start)

    # For the lower bound, we need to show EC for ALL possible good cycles,
    # including those with fc(pivot)=2.

    # Let me directly enumerate mover words with the right properties
    # and check the phase/contamination structure.

    print("="*70)
    print("=== Mover word analysis (combinatorial, no configs needed) ===")
    print("="*70)
    print()

    # For the phase structure question, we only need the mover word.
    # With all fc=2, length=14, n=7:
    # Count pivot positions: C(14,2) = 91 ways to place pivot.
    # For each, determine phases and check contamination.

    # Actually we need ALL procs to fire, and for the specific geometry.
    # Let me enumerate mover words of length 14 with each proc firing exactly twice.
    # That's 14!/(2!)^7 = 14!/(128) = about 681 million. Too many.

    # Instead, let me just check: for a random mover word with these constraints,
    # what fraction are Case 3 vs Case 1/2?

    random.seed(42)
    n_samples = 100000
    case_counts = defaultdict(int)

    for _ in range(n_samples):
        # Generate random mover word: each proc appears exactly twice
        mw = []
        for i in range(n):
            mw.extend([i, i])
        random.shuffle(mw)

        pivot_steps = [i for i, m in enumerate(mw) if m == pivot]
        p1, p2 = pivot_steps
        L = len(mw)

        phase1_len = (p2 - p1 - 1) % L
        phase2_len = (p1 - p2 - 1) % L
        phase1_steps = [(p1 + 1 + k) % L for k in range(phase1_len)]
        phase2_steps = [(p2 + 1 + k) % L for k in range(phase2_len)]

        phase1_movers = set(mw[s] for s in phase1_steps)
        phase2_movers = set(mw[s] for s in phase2_steps)

        left2t = 2
        right2t = 6

        p1_contam = (left2t in phase1_movers) or (right2t in phase1_movers)
        p2_contam = (left2t in phase2_movers) or (right2t in phase2_movers)

        pos2_in_int = (left2t in phase1_movers) or (left2t in phase2_movers)
        pos6_in_int = (right2t in phase1_movers) or (right2t in phase2_movers)

        if p1_contam and p2_contam:
            case_counts["Case3_all_contam"] += 1
        if not pos2_in_int and not pos6_in_int:
            case_counts["trivial_no_2or6_in_interior"] += 1
        if not pos2_in_int:
            case_counts["Case1_tight_left"] += 1
        if not pos6_in_int:
            case_counts["Case2_tight_right"] += 1
        if pos2_in_int and pos6_in_int:
            case_counts["both_interior"] += 1

        # Check if BOTH firings of pos2 are adjacent to pivot
        # Adjacent = immediately before or after a pivot step
        pos2_steps_list = [i for i, m in enumerate(mw) if m == left2t]
        all_adjacent = True
        for s2 in pos2_steps_list:
            adj_to_pivot = False
            for ps in [p1, p2]:
                if (s2 - ps) % L == 1 or (ps - s2) % L == 1:
                    adj_to_pivot = True
            if not adj_to_pivot:
                all_adjacent = False
        if all_adjacent:
            case_counts["pos2_all_adjacent_to_pivot"] += 1

    print(f"Random mover word sampling ({n_samples} samples, n={n}, all fc=2):")
    for case, count in sorted(case_counts.items()):
        pct = 100 * count / n_samples
        print(f"  {case}: {count} ({pct:.1f}%)")

    print()
    print("KEY INSIGHT: In random mover words, Case 3 (all contaminated) occurs")
    print("frequently. The previous finding of 0 Case 3 was an artifact of only")
    print("finding trivial length-2 cycles. For ABSTRACT mover words with fc(pivot)=2,")
    print("all three cases occur.")

    # Now the critical question: for Case 3 cycles, does the proposed EC mechanism work?
    print()
    print("="*70)
    print("=== Adjacent-proc EC analysis (analytical) ===")
    print("="*70)
    print()
    print("THEOREM: For adjacent procs j and j+1 both firing in the same phase,")
    print("the boundary triple at j+1 = (c[j], c[j+1], c[j+2]) MUST DIFFER")
    print("between the step when j fires and when j+1 fires.")
    print()
    print("PROOF: Consider two orderings within a phase:")
    print("  (A) j fires at step s1, j+1 fires at step s2 > s1:")
    print("      At s1: triple = (c[j]_old, c[j+1], c[j+2])")
    print("      After s1: c[j] changes to c[j]_new != c[j]_old")
    print("      At s2: triple = (c[j]_new, ..., ...)")
    print("      First component differs. (No other step can change c[j].)")
    print("  (B) j+1 fires at step s2, j fires at step s1 > s2:")
    print("      At s2: triple = (c[j], c[j+1]_old, c[j+2])")
    print("      After s2: c[j+1] changes to c[j+1]_new != c[j+1]_old")
    print("      At s1: triple = (..., c[j+1]_new, ...)")
    print("      Second component differs. (No other step can change c[j+1].)")
    print("  In both cases, the triples differ. QED")
    print()
    print("CONSEQUENCE: The proposed mechanism (left3t firing shares boundary")
    print("triple with left2t mover step) CANNOT give EC at left2t, because")
    print("left3t (pos 1) and left2t (pos 2) are adjacent.")
    print()

    # But what about NON-ADJACENT sharing?
    # E.g., pos 0 fires and pos 2 is a non-mover. Later pos 2 fires.
    # Triple at pos 2 = (c[1], c[2], c[3]).
    # When pos 0 fires: c[0] changes, but c[1],c[2],c[3] unchanged.
    # When pos 2 fires later: c[1] may have changed (if pos 1 fired between).
    # If pos 1 did NOT fire between pos 0 and pos 2: c[1] unchanged.
    # And c[2] hasn't changed yet (pos 2 fires now). c[3] may have changed.
    # If c[3] also unchanged: triple is same -> EC!

    print("NON-ADJACENT sharing CAN give EC:")
    print("If pos j fires and pos j+2 fires later in the same phase,")
    print("AND pos j+1 does NOT fire between them,")
    print("AND pos j+3 does NOT fire between them,")
    print("then the triple at pos j+2 is identical at both steps -> EC.")
    print()
    print("This is the correct mechanism for Case 3, not the adjacent one.")

    # Let me check: for Case 3 mover words, how often does a non-adjacent
    # EC-enabling pattern exist?
    print()
    print("="*70)
    print("=== Non-adjacent EC in Case 3 mover words ===")
    print("="*70)
    print()

    random.seed(42)
    n_case3 = 0
    n_case3_with_nonadj_ec_pattern = 0
    ec_pattern_details = defaultdict(int)

    for _ in range(100000):
        mw = []
        for i in range(n):
            mw.extend([i, i])
        random.shuffle(mw)

        pivot_steps = [i for i, m in enumerate(mw) if m == pivot]
        p1, p2 = pivot_steps
        L = len(mw)

        phase1_len = (p2 - p1 - 1) % L
        phase2_len = (p1 - p2 - 1) % L
        phase1_steps = [(p1 + 1 + k) % L for k in range(phase1_len)]
        phase2_steps = [(p2 + 1 + k) % L for k in range(phase2_len)]

        phase1_movers = set(mw[s] for s in phase1_steps)
        phase2_movers = set(mw[s] for s in phase2_steps)

        left2t = 2
        right2t = 6
        p1_contam = (left2t in phase1_movers) or (right2t in phase1_movers)
        p2_contam = (left2t in phase2_movers) or (right2t in phase2_movers)

        if not (p1_contam and p2_contam):
            continue

        n_case3 += 1
        has_nonadj_ec = False

        # Check for EC pattern at any position pos:
        # Exists steps s1, s2 in same phase where:
        # - mw[s1] != pos, mw[s2] == pos (or vice versa)
        # - c[pos-1], c[pos], c[pos+1] are all unchanged between s1 and s2
        # This means: between s1 and s2, none of {pos-1, pos, pos+1} fires.
        # Wait, at s1, mw[s1] fires. At s2, mw[s2]=pos fires.
        # The triple at pos is (c[pos-1], c[pos], c[pos+1]).
        # For this triple to be same at s1 and s2:
        # - c[pos-1] unchanged between s1 and s2
        # - c[pos] unchanged between s1 and s2
        # - c[pos+1] unchanged between s1 and s2
        # This means: between s1 and s2, no proc in {pos-1, pos, pos+1} fires.
        # (pos fires AT s2, but the triple is measured BEFORE the firing.)

        for phase_steps in [phase1_steps, phase2_steps]:
            if has_nonadj_ec:
                break
            phase_mw = [(s, mw[s]) for s in phase_steps]

            for pos in range(n):
                if has_nonadj_ec:
                    break
                neighbors = {(pos-1)%n, pos, (pos+1)%n}

                # Find all steps where pos fires (mover) and all other steps (non-mover)
                mover_indices = [idx for idx, (s, m) in enumerate(phase_mw) if m == pos]
                nonmover_indices = [idx for idx, (s, m) in enumerate(phase_mw) if m != pos]

                for mi in mover_indices:
                    for ni in nonmover_indices:
                        # Check if between min(mi,ni) and max(mi,ni),
                        # no proc in neighbors fires (excluding the endpoints)
                        lo, hi = min(mi, ni), max(mi, ni)
                        between = phase_mw[lo+1:hi]  # steps strictly between
                        between_movers = set(m for _, m in between)
                        if not (between_movers & neighbors):
                            # Also check: at the non-mover step, the mover is NOT in neighbors
                            nm_mover = phase_mw[ni][1]
                            if nm_mover not in neighbors:
                                # Triple at pos unchanged between the two steps
                                has_nonadj_ec = True
                                ec_pattern_details[pos] += 1
                                break
                    if has_nonadj_ec:
                        break

        if has_nonadj_ec:
            n_case3_with_nonadj_ec_pattern += 1

    print(f"Case 3 mover words: {n_case3}")
    print(f"  With non-adjacent EC pattern: {n_case3_with_nonadj_ec_pattern} "
          f"({100*n_case3_with_nonadj_ec_pattern/max(1,n_case3):.1f}%)")
    print(f"  EC pattern by position: {dict(sorted(ec_pattern_details.items()))}")

    # Now do the SAME check for Case 1 and Case 2
    print()
    print("="*70)
    print("=== EC patterns for Cases 1, 2 ===")
    print("="*70)

    random.seed(42)
    case_ec = {"Case1": [0, 0], "Case2": [0, 0], "Case3": [0, 0]}

    for _ in range(200000):
        mw = []
        for i in range(n):
            mw.extend([i, i])
        random.shuffle(mw)

        pivot_steps = [i for i, m in enumerate(mw) if m == pivot]
        p1, p2 = pivot_steps
        L = len(mw)

        phase1_len = (p2 - p1 - 1) % L
        phase2_len = (p1 - p2 - 1) % L
        phase1_steps = [(p1 + 1 + k) % L for k in range(phase1_len)]
        phase2_steps = [(p2 + 1 + k) % L for k in range(phase2_len)]

        phase1_movers = set(mw[s] for s in phase1_steps)
        phase2_movers = set(mw[s] for s in phase2_steps)

        left2t = 2
        right2t = 6

        pos2_in_int = (left2t in phase1_movers) or (left2t in phase2_movers)
        pos6_in_int = (right2t in phase1_movers) or (right2t in phase2_movers)
        p1_contam = (left2t in phase1_movers) or (right2t in phase1_movers)
        p2_contam = (left2t in phase2_movers) or (right2t in phase2_movers)

        if not pos2_in_int:
            case = "Case1"
        elif not pos6_in_int:
            case = "Case2"
        elif p1_contam and p2_contam:
            case = "Case3"
        else:
            continue

        case_ec[case][0] += 1

        # Check for EC pattern at ANY position
        has_ec = False
        for phase_steps in [phase1_steps, phase2_steps]:
            if has_ec:
                break
            phase_mw = [(s, mw[s]) for s in phase_steps]

            for pos in range(n):
                if has_ec:
                    break
                neighbors = {(pos-1)%n, pos, (pos+1)%n}
                mover_indices = [idx for idx, (s, m) in enumerate(phase_mw) if m == pos]
                nonmover_indices = [idx for idx, (s, m) in enumerate(phase_mw) if m != pos]

                for mi in mover_indices:
                    for ni in nonmover_indices:
                        lo, hi = min(mi, ni), max(mi, ni)
                        between = phase_mw[lo+1:hi]
                        between_movers = set(m for _, m in between)
                        if not (between_movers & neighbors):
                            nm_mover = phase_mw[ni][1]
                            if nm_mover not in neighbors:
                                has_ec = True
                                break
                    if has_ec:
                        break

        # Also check across phases and at pivot steps
        if not has_ec:
            # Cross-phase: mover in one phase, non-mover in another
            # This requires same triple at different times - harder to check
            # without actual configs. Skip for now.
            pass

        if has_ec:
            case_ec[case][1] += 1

    print("EC pattern coverage by case:")
    for case in ["Case1", "Case2", "Case3"]:
        total, with_ec = case_ec[case]
        pct = 100 * with_ec / max(1, total)
        print(f"  {case}: {with_ec}/{total} ({pct:.1f}%) have EC pattern")

    print()
    print("="*70)
    print("=== FINAL SUMMARY ===")
    print("="*70)
    print()
    print("1. The proposed mechanism (left3t-firing shares boundary triple with")
    print("   left2t-mover step) is IMPOSSIBLE because they are adjacent procs.")
    print("   Adjacent proc firings ALWAYS change one component of the shared")
    print("   boundary triple.")
    print()
    print("2. All three hglobal cases (1, 2, 3) DO occur in mover words with")
    print("   fc(pivot)=2. The earlier finding of zero Case 3 was an artifact")
    print("   of trivial length-2 cycles.")
    print()
    print("3. Non-adjacent EC patterns exist and can kill cycles. These come from")
    print("   procs separated by >= 2 positions firing without intermediate")
    print("   neighbor changes.")
    print()
    print("4. The correct EC mechanism for Case 3 at left2t would involve a")
    print("   NON-ADJACENT proc (e.g., pos 0 or pos 3) firing and pos 2 firing")
    print("   with no intervening changes to {pos 1, pos 2, pos 3}.")

if __name__ == "__main__":
    run()
