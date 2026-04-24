"""
Analyze isolated sandwiched ternary pivots at n=9 with P=2.
ms = (3,3,2,2,3,2,2,3,3), pivot at position 4.
Classify which layer closes each good cycle with fc(pivot)=2.
"""

from itertools import product as iproduct

def generate_good_cycles(ms):
    """Generate all good cycles for given ms as lists of (mover, configs)."""
    n = len(ms)
    total = 1
    for m in ms:
        total *= m

    # Generate all configurations
    all_configs = list(iproduct(*(range(m) for m in ms)))

    # For each config, find which processors can fire (are movers)
    # A processor p fires if it's the "privileged" one.
    # In Dijkstra's framework: p fires if c[p] != c[(p-1) % n] for p>0, or special for p=0
    # Actually for general token rings: p is a mover if f_p(c[p-1], c[p], c[p+1]) != c[p]
    # But we need the transition function...

    # Wait - we need to enumerate good cycles abstractly as mover words.
    # A good cycle is a sequence of movers (p_0, p_1, ..., p_{L-1}) where each p fires
    # exactly m_p times total, and the cycle returns to the starting config.

    # Actually, let me think about this differently.
    # We need to enumerate all possible mover sequences (words) where:
    # - Each processor p appears exactly m_p times
    # - The sequence forms a valid cycle (returns to start for SOME transition function)

    # For the entry conflict analysis, we don't need the actual transition function.
    # We need to analyze the STRUCTURE of the mover word.

    # Let me enumerate mover words directly.
    pass


def enumerate_mover_words(ms):
    """
    Enumerate all mover words where processor p appears exactly ms[p] times.
    Total length = sum(ms).
    Returns list of tuples (mover sequence).
    """
    n = len(ms)
    L = sum(ms)

    # Build by placing each processor's firings
    # This is a multinomial enumeration
    remaining = list(ms)

    def backtrack(pos, remaining, word):
        if pos == L:
            yield tuple(word)
            return
        for p in range(n):
            if remaining[p] > 0:
                remaining[p] -= 1
                word.append(p)
                yield from backtrack(pos + 1, remaining, word)
                word.pop()
                remaining[p] += 1

    # This is way too many - L! / prod(ms[p]!)
    # For ms=(3,3,2,2,3,2,2,3,3) that's 23!/(3!*3!*2!*2!*3!*2!*2!*3!*3!) which is huge
    # Need a smarter approach
    pass


def analyze_pivot_phases():
    """
    For ms = (3,3,2,2,3,2,2,3,3), n=9, pivot at position 4 (ternary, ms[4]=3).
    fc(pivot) = 2, so pivot fires exactly 2 times in a good cycle of length sum(ms)-1 = 22.

    Wait - in a good cycle, each processor fires exactly ms[p] times.
    ms[4] = 3, so fc(4) = 3 normally.

    But the question says fc(4) = 2. This means we're looking at cycles where
    the pivot fires only 2 times? That would mean fc < full fire count.

    Actually, re-reading: "fireCount(pivot)=2" with P=2.
    In the context of the paper, a good cycle has each proc fire exactly m_p times.
    ms[4] = 3, so the pivot fires 3 times normally.

    Hmm, but the question says P=2. Let me re-read...
    "P = 2: pivot fires twice, creating 2 phases"

    With ms[4] = 3, the pivot fires 3 times, creating 3 phases.
    P=2 would need ms[4] = 2... but ms[4] = 3 in the given ms.

    Wait - maybe the question means a different ms where ms[4] = 2?
    Let me re-read: ms = (3,3,2,2,3,2,2,3,3). Position 4 has ms[4]=3.

    Actually, I think "P=2" might refer to something else, or perhaps
    we should look at ms where the pivot is ternary with value 3 but
    we're analyzing sub-patterns.

    Let me just focus on the structural analysis as described:
    pivot at pos 4, fires some number of times, creating phases between firings.
    With ms[4]=3, pivot fires 3 times creating 3 phases.

    Actually - I think the question might have P=2 meaning we focus on
    cycles where the pivot fires exactly 2 times out of ms[4]=3.
    But in a GOOD cycle, every proc fires exactly ms[p] times.

    OR: maybe the question is about fc=2 meaning the GOOD cycle has
    the pivot contributing fc=2 to the total fire count of the cycle.
    In standard good cycles, fc = sum(ms) and each proc fires ms[p] times.

    I think the most natural reading is: we have a ternary pivot (ms[4]=3)
    that fires 3 times. Let me just analyze with 3 firings and report.

    Actually wait - re-reading more carefully: "P=2: pivot fires twice"
    This is explicit. So maybe ms[4]=2? But the given ms says ms[4]=3.

    Let me try ms[4]=2: ms = (3,3,2,2,2,2,2,3,3). But then pivot is binary, not ternary.

    I think there might be a disconnect. Let me just analyze BOTH cases
    and let the user sort it out. But actually, let me just go with what's
    stated: pivot at pos 4, fires P=2 times. Maybe they mean a modified
    scenario or a sub-cycle analysis.

    Let me just implement the analysis for arbitrary P and ms.
    """
    pass


def main():
    """
    Direct approach: enumerate mover words focusing on the pivot structure.

    ms = (3,3,2,2,3,2,2,3,3), n=9, pivot=4, ms[pivot]=3.

    The pivot fires 3 times, creating 3 phases. But the question asks about P=2.

    I'll analyze BOTH P=3 (natural for ms[4]=3) and also check if the question
    means something specific about P=2.

    Actually, let me re-read one more time... "fireCount(pivot)=2" - maybe this
    means in a REDUCED cycle where pivot only fires 2 times? Or in a cycle
    where the total fire count through the pivot is 2?

    I think the most productive approach: just enumerate the phase structures
    for the pivot firing 3 times (as ms[4]=3 dictates), analyze all phases,
    and classify by layer. Also do the P=2 case with ms[4]=2 separately.

    But enumerating all mover words is infeasible. Instead, let me enumerate
    just the LOCAL structure around the pivot.
    """

    # Focus on the local neighborhood of the pivot.
    # Pivot = pos 4, left_t = pos 3, right_t = pos 5
    # left2t = pos 2 (binary, ms=2), right2t = pos 6 (binary, ms=2)
    # left3t = pos 1 (ternary, ms=3), right3t = pos 7 (ternary, ms=3)

    # Key positions: 2(bin), 3(bin), 4(ternary pivot), 5(bin), 6(bin)
    # ms = (3,3,2,2,3,2,2,3,3)
    #        0  1  2  3  4  5  6  7  8

    ms = (3, 3, 2, 2, 3, 2, 2, 3, 3)
    n = 9
    pivot = 4

    # Positions of interest
    left2t = 2   # binary, fires 2 times
    left_t = 3   # binary, fires 2 times
    right_t = 5  # binary, fires 2 times
    right2t = 6  # binary, fires 2 times

    L = sum(ms)  # = 23, cycle length

    print(f"ms = {ms}")
    print(f"n = {n}, L = {L}")
    print(f"Pivot at pos {pivot}, ms[pivot] = {ms[pivot]}")
    print(f"left2t={left2t} (ms={ms[left2t]}), left_t={left_t} (ms={ms[left_t]})")
    print(f"right_t={right_t} (ms={ms[right_t]}), right2t={right2t} (ms={ms[right2t]})")
    print()

    # The pivot fires ms[4]=3 times, creating 3 phases.
    # But the question specifies P=2. Let me handle this by considering
    # that maybe the question is about a DIFFERENT ms where ms[4]=2,
    # or about a sub-analysis. Let me do both.

    # APPROACH: Instead of enumerating all mover words (infeasible),
    # enumerate the LOCAL firing pattern of the 5 key positions
    # {2,3,4,5,6} within the full cycle.

    # The cycle has L=23 steps. We need to place:
    # - pos 2: 2 firings
    # - pos 3: 2 firings
    # - pos 4: 3 firings (or 2 for P=2 variant)
    # - pos 5: 2 firings
    # - pos 6: 2 firings
    # Total local firings: 11 (or 10 for P=2)
    # Remaining 12 (or 13) firings go to positions {0,1,7,8}

    # For the phase analysis, we only care about the RELATIVE ORDER
    # of firings at positions {2,3,4,5,6}.

    # The phases are defined by pivot firings. Between consecutive
    # pivot firings, we count how many times each neighbor fires.

    # With the pivot firing P times, there are P phases:
    # Phase i = interval (pivot_firing_i, pivot_firing_{i+1}) cyclically

    # The key insight: we only need the PATTERN of {2,3,5,6} firings
    # relative to the pivot firings. The other positions don't matter
    # for this local analysis.

    # Enumerate: distribute firings of {2,3,5,6} into P phases.
    # pos 2: 2 firings into P phases
    # pos 3: 2 firings into P phases
    # pos 5: 2 firings into P phases
    # pos 6: 2 firings into P phases

    # For each distribution, also need the ORDER within each phase.

    # Actually, for the layer analysis we need:
    # Per phase: (J, K, g, h) = (#fires of left_t, right_t, left2t, right2t)
    # And for tightness: the relative order of first firings within the phase

    # Let's enumerate distributions and orderings.

    for P in [2, 3]:
        print(f"{'='*60}")
        print(f"ANALYSIS FOR P = {P} (pivot fires {P} times)")
        print(f"{'='*60}")

        if P == 2:
            # Override: treat pivot as firing 2 times
            # (This could represent ms[4]=2 or a sub-analysis)
            pass

        analyze_phases(P, ms, pivot, left_t, right_t, left2t, right2t)
        print()


def distribute(total_fires, num_phases):
    """
    Enumerate all ways to distribute total_fires firings into num_phases phases.
    Each phase gets >= 0 firings. Returns list of tuples.
    """
    if num_phases == 1:
        yield (total_fires,)
        return
    for k in range(total_fires + 1):
        for rest in distribute(total_fires - k, num_phases - 1):
            yield (k,) + rest


def analyze_phases(P, ms, pivot, left_t, right_t, left2t, right2t):
    """
    Analyze phase structure for pivot firing P times.
    """
    # Distribute firings of each neighbor into P phases
    fire_counts = {
        'left_t': ms[left_t],    # 2
        'right_t': ms[right_t],  # 2
        'left2t': ms[left2t],    # 2
        'right2t': ms[right2t],  # 2
    }

    print(f"Fire counts: {fire_counts}")

    # Enumerate all distributions
    dists_lt = list(distribute(fire_counts['left_t'], P))
    dists_rt = list(distribute(fire_counts['right_t'], P))
    dists_l2 = list(distribute(fire_counts['left2t'], P))
    dists_r2 = list(distribute(fire_counts['right2t'], P))

    print(f"Distribution counts: left_t={len(dists_lt)}, right_t={len(dists_rt)}, "
          f"left2t={len(dists_l2)}, right2t={len(dists_r2)}")

    # For each combination of distributions, analyze phases
    total_words = 0
    layer1_closed = 0
    layer2_closed = 0
    layer3_closed = 0
    unclosed = 0

    # Track details
    layer_details = {1: [], 2: [], 3: [], 'unclosed': []}

    for d_lt in dists_lt:
        for d_rt in dists_rt:
            for d_l2 in dists_l2:
                for d_r2 in dists_r2:
                    total_words += 1

                    # For each phase i, we have:
                    # J_i = d_lt[i], K_i = d_rt[i], g_i = d_l2[i], h_i = d_r2[i]
                    phases = []
                    for i in range(P):
                        phases.append({
                            'J': d_lt[i],
                            'K': d_rt[i],
                            'g': d_l2[i],
                            'h': d_r2[i],
                        })

                    # Classify
                    layer = classify_word(phases, P)

                    if layer == 1:
                        layer1_closed += 1
                        layer_details[1].append((phases, d_lt, d_rt, d_l2, d_r2))
                    elif layer == 2:
                        layer2_closed += 1
                        layer_details[2].append((phases, d_lt, d_rt, d_l2, d_r2))
                    elif layer == 3:
                        layer3_closed += 1
                        layer_details[3].append((phases, d_lt, d_rt, d_l2, d_r2))
                    else:
                        unclosed += 1
                        layer_details['unclosed'].append((phases, d_lt, d_rt, d_l2, d_r2))

    print(f"\nTotal distribution combos: {total_words}")
    print(f"Layer 1 (pigeonhole):     {layer1_closed} ({100*layer1_closed/total_words:.1f}%)")
    print(f"Layer 2 (non-tight EC):   {layer2_closed} ({100*layer2_closed/total_words:.1f}%)")
    print(f"Layer 3 (binary recovery):{layer3_closed} ({100*layer3_closed/total_words:.1f}%)")
    print(f"Unclosed (layers 1-3):    {unclosed} ({100*unclosed/total_words:.1f}%)")

    # Now do the REFINED analysis with ordering
    # For layer 2, we need to check tightness, which depends on the
    # ordering of firings within a phase.

    print(f"\n--- Refined analysis with ordering ---")

    # For the refined analysis, we need to consider the ordering of
    # firings within each phase. A phase with J left_t firings and
    # g left2t firings has (J+g)! / (J! * g!) orderings on the left side,
    # similarly for right.

    # But we also need to interleave left and right firings with
    # other processors' firings. For tightness, we only care about
    # the FIRST few firings in the phase.

    # Tightness check for left side:
    # "Tight" = left2t fires first in the phase, then left_t fires immediately after
    # This requires g >= 1 and J >= 1 and the first mover is left2t, second is left_t

    # For the ordering analysis, enumerate all possible orderings of
    # the local firings {left_t, right_t, left2t, right2t} within each phase.
    # Other processors can fire in between, which makes things non-tight.

    # Actually, the question's definition says:
    # "Non-tight means: the first left-t firing has f > a+1"
    # where a is the phase-start step.
    # This means between the phase start and the first left_t firing,
    # there's at least one other firing (could be ANY processor).

    # Since there are L-P = 23-P other firings distributed across phases,
    # and we have 8 firings of {2,3,5,6} plus (L-P-8) = (23-P-8) other firings,
    # the question is whether the first left_t firing is the VERY first
    # firing in the phase.

    # For tightness to hold specifically as "left2t then left_t with nothing between":
    # We need: (1) left2t fires first in phase, (2) left_t fires second in phase,
    # (3) no other processor fires between them.

    # Given that a phase has many firings (on average (L-P)/P per phase),
    # the probability of this exact pattern is low. But we need to check
    # all possibilities.

    # Simpler approach: for each distribution, enumerate the orderings of
    # the LOCAL firings and check tightness.

    # Actually, the key insight is that we need to consider ALL possible
    # mover words, not just distributions. The distribution tells us
    # (J, K, g, h) per phase, but tightness depends on ordering.

    # For each phase with local firings, enumerate all orderings of
    # local processors, and for each ordering, determine tightness.
    # Non-local processors can appear anywhere, making non-tight more likely.

    # Let's do a comprehensive analysis.

    total_ordered = 0
    ordered_layer1 = 0
    ordered_layer2 = 0
    ordered_layer3 = 0
    ordered_unclosed = 0

    # For each distribution combo
    for d_lt in dists_lt:
        for d_rt in dists_rt:
            for d_l2 in dists_l2:
                for d_r2 in dists_r2:
                    phases_counts = []
                    for i in range(P):
                        phases_counts.append({
                            'J': d_lt[i], 'K': d_rt[i],
                            'g': d_l2[i], 'h': d_r2[i],
                        })

                    # For each phase, enumerate orderings of local firings
                    # A local ordering is a permutation of the multiset
                    # {left2t^g, left_t^J, right_t^K, right2t^h}

                    # For tightness, we only care about the first few positions
                    # AND whether non-local firings can interleave.

                    # Non-local firings per phase: we don't know exactly,
                    # but there are (L - P - 8) = (23 - P - 8) = (15-P) non-local firings
                    # distributed across P phases.

                    # For a WORST CASE (most tight) analysis: assume non-local
                    # firings can be placed to AVOID breaking tightness.
                    # For a BEST CASE (most non-tight): non-local firings
                    # always break tightness.

                    # Let's check both: can tightness EVER hold? must it ALWAYS hold?

                    phase_orderings = []
                    for i in range(P):
                        phase_orderings.append(
                            enumerate_local_orderings(phases_counts[i])
                        )

                    # For each combination of phase orderings
                    from itertools import product as iprod
                    for combo in iprod(*phase_orderings):
                        total_ordered += 1
                        layer = classify_ordered_word(phases_counts, combo, P)
                        if layer == 1:
                            ordered_layer1 += 1
                        elif layer == 2:
                            ordered_layer2 += 1
                        elif layer == 3:
                            ordered_layer3 += 1
                        else:
                            ordered_unclosed += 1

    print(f"\nTotal ordered combos: {total_ordered}")
    if total_ordered > 0:
        print(f"Layer 1 (pigeonhole):     {ordered_layer1} ({100*ordered_layer1/total_ordered:.1f}%)")
        print(f"Layer 2 (non-tight EC):   {ordered_layer2} ({100*ordered_layer2/total_ordered:.1f}%)")
        print(f"Layer 3 (binary recovery):{ordered_layer3} ({100*ordered_layer3/total_ordered:.1f}%)")
        print(f"Unclosed (layers 1-3):    {ordered_unclosed} ({100*ordered_unclosed/total_ordered:.1f}%)")

    # Show unclosed cases in detail
    if ordered_unclosed > 0 and ordered_unclosed <= 20:
        print(f"\nUnclosed cases detail:")
        # Re-enumerate to find them
        count = 0
        for d_lt in dists_lt:
            for d_rt in dists_rt:
                for d_l2 in dists_l2:
                    for d_r2 in dists_r2:
                        phases_counts = []
                        for i in range(P):
                            phases_counts.append({
                                'J': d_lt[i], 'K': d_rt[i],
                                'g': d_l2[i], 'h': d_r2[i],
                            })
                        phase_orderings = []
                        for i in range(P):
                            phase_orderings.append(
                                enumerate_local_orderings(phases_counts[i])
                            )
                        from itertools import product as iprod
                        for combo in iprod(*phase_orderings):
                            layer = classify_ordered_word(phases_counts, combo, P)
                            if layer > 3:
                                count += 1
                                if count <= 20:
                                    print(f"  #{count}: phases={phases_counts}, orderings={combo}")


def enumerate_local_orderings(phase):
    """
    Enumerate all orderings of local firings in a phase.
    Returns list of tuples like ('l2', 'lt', 'rt', 'r2', 'lt', ...)
    representing the order of local firings.
    """
    items = []
    items.extend(['l2'] * phase['g'])
    items.extend(['lt'] * phase['J'])
    items.extend(['rt'] * phase['K'])
    items.extend(['r2'] * phase['h'])

    if not items:
        return [()]

    # Generate unique permutations
    return list(unique_permutations(items))


def unique_permutations(items):
    """Generate unique permutations of a list with possible duplicates."""
    if len(items) <= 1:
        yield tuple(items)
        return

    seen = set()
    for i, item in enumerate(items):
        if item in seen:
            continue
        seen.add(item)
        rest = items[:i] + items[i+1:]
        for perm in unique_permutations(rest):
            yield (item,) + perm


def classify_word(phases, P):
    """
    Classify a mover word by layer based on phase counts only (no ordering).
    Returns the layer that closes it (1, 2, 3) or 99 if unclosed.

    Layer 1: Some phase has (g=0 and J>=1) or (h=0 and K>=1), AND
             the free second-neighbor condition from pigeonhole.
             For P=2 and binary second-neighbors (fc=2): needs P > fc.
             Since P=2 and fc=2: pigeonhole FAILS.
             For P=3 and fc=2: P > fc, so pigeonhole works if g=0 somewhere.
    """
    # Layer 1: pigeonhole
    # For binary second-neighbors (fire exactly 2 times), pigeonhole needs
    # more phases than fire count: P > 2.
    if P > 2:
        for phase in phases:
            if (phase['g'] == 0 and phase['J'] >= 1):
                return 1
            if (phase['h'] == 0 and phase['K'] >= 1):
                return 1

    # Layer 2 and 3 need ordering info - can't determine from counts alone
    # But we can check NECESSARY conditions

    # Layer 2 needs: some phase has g=0 (or h=0) AND J>=1 (or K>=1)
    # AND the ordering is non-tight
    has_free_phase = False
    for phase in phases:
        if (phase['g'] == 0 and phase['J'] >= 1):
            has_free_phase = True
        if (phase['h'] == 0 and phase['K'] >= 1):
            has_free_phase = True

    if has_free_phase:
        return 2  # Potentially layer 2 (needs ordering check)

    # Layer 3: tight phase with even J or K
    for phase in phases:
        if phase['J'] % 2 == 0 and phase['J'] >= 2:
            return 3
        if phase['K'] % 2 == 0 and phase['K'] >= 2:
            return 3

    # Check if any phase has conditions for layer 3
    # Even J or K in any phase
    for phase in phases:
        if phase['J'] >= 2 and phase['J'] % 2 == 0:
            return 3
        if phase['K'] >= 2 and phase['K'] % 2 == 0:
            return 3

    return 99


def classify_ordered_word(phases_counts, orderings, P):
    """
    Classify with ordering information.
    orderings[i] = tuple of local firing order in phase i.

    Layer 1: pigeonhole (P > fc of second-neighbor)
    Layer 2: non-tight within-phase EC
    Layer 3: binary recovery (even J or K)
    """
    # Layer 1: pigeonhole
    if P > 2:  # binary second-neighbors have fc=2
        for phase in phases_counts:
            if (phase['g'] == 0 and phase['J'] >= 1):
                return 1
            if (phase['h'] == 0 and phase['K'] >= 1):
                return 1

    # Layer 2: non-tight EC
    # For each phase, check if there's a free second-neighbor and non-tight first-neighbor
    for i in range(P):
        phase = phases_counts[i]
        order = orderings[i]

        # Left side: g=0 (left2t doesn't fire) and J>=1 (left_t does fire)
        if phase['g'] == 0 and phase['J'] >= 1:
            # Check tightness of left_t
            # Non-tight if: first lt firing is NOT at position 0 of the phase
            # OR there are other firings before it
            # In our local ordering, if the first element is not 'lt',
            # then there's something before it (could be right side firing)
            # Also, non-local firings can appear before it

            # With g=0, left2t doesn't fire in this phase.
            # Tight would require: left2t fires at position a (phase start),
            # then left_t at a+1. But g=0 means left2t DOESN'T fire!
            # So the "domino" pattern (left2t -> left_t) can't form.
            # This means it's automatically non-tight on the left side.

            # Wait, re-reading the layer 2 definition:
            # "A phase has a free second-neighbor (g=0 or h=0)"
            # g=0 means left2t doesn't fire in this phase.
            # "AND the first-neighbor firing is NON-TIGHT"
            # Non-tight means the first left_t firing has gap after t-firing.
            #
            # Actually, I think "tight" means the domino chain:
            # t fires -> left2t fires immediately -> left_t fires immediately
            # If g=0, the domino chain is broken, so it's automatically non-tight.
            #
            # But wait, the definition also says:
            # "Non-tight at left t means: the first mover is NOT left2t
            #  immediately followed by left t"
            # If g=0, this condition is automatically satisfied (first mover
            # can't be left2t since left2t doesn't fire).

            # So: g=0 AND J>=1 -> automatically non-tight -> Layer 2 closes!
            return 2

        # Right side: h=0 (right2t doesn't fire) and K>=1 (right_t does fire)
        if phase['h'] == 0 and phase['K'] >= 1:
            # Same logic: h=0 means right2t doesn't fire, so domino chain breaks
            # Automatically non-tight -> Layer 2 closes
            return 2

        # What if g>=1 and J>=1? Then we need to check ordering for tightness.
        # Tight on left: first firing in phase is left2t, second is left_t
        if phase['g'] >= 1 and phase['J'] >= 1:
            # Check if left side is non-tight based on ordering
            if len(order) >= 2:
                if not (order[0] == 'l2' and order[1] == 'lt'):
                    # Non-tight on left, but we also need the free condition
                    # Actually layer 2 requires g=0 OR h=0 (free second-neighbor)
                    # If g>=1 AND h>=1, layer 2 doesn't apply via the free condition
                    pass
            # Non-tight but not free -> not layer 2

        if phase['h'] >= 1 and phase['K'] >= 1:
            if len(order) >= 2:
                # Similar for right side
                pass

    # Layer 3: binary recovery
    # A phase has even J (>=2) or even K (>=2)
    # Binary recovery: second firing restores state -> EC
    for i in range(P):
        phase = phases_counts[i]
        if phase['J'] >= 2 and phase['J'] % 2 == 0:
            return 3
        if phase['K'] >= 2 and phase['K'] % 2 == 0:
            return 3

    return 99


# Let me also do a more fundamental analysis
def fundamental_analysis():
    """
    Think about this more carefully.

    ms = (3,3,2,2,3,2,2,3,3)
    Pivot = pos 4, ms[4] = 3 (ternary)

    Neighbors:
    - left_t = pos 3, ms[3] = 2 (binary)
    - right_t = pos 5, ms[5] = 2 (binary)
    - left2t = pos 2, ms[2] = 2 (binary)
    - right2t = pos 6, ms[6] = 2 (binary)

    The question asks about P=2. I think this means: among the 3 pivot firings,
    we PAIR them into P=2 "effective" phases. Or perhaps the question is about
    a different state vector.

    Actually, the most likely interpretation: the question defines P as the
    fire count of the pivot, and says P=2. This means ms[4] should be 2.
    But the given ms has ms[4]=3.

    Let me try BOTH:
    (A) ms as given, pivot fires 3 times (P=3)
    (B) Modified: ms[4]=2, pivot fires 2 times (P=2)

    For (B), ms = (3,3,2,2,2,2,2,3,3), product = 3*3*2*2*2*2*2*3*3 = 3888
    The threshold is 4*3^7 = 8748, so 3888 < 8748 (sub-threshold). This makes sense!
    A "sandwiched ternary" at pos 4 with ms[4]=2 is actually binary, not ternary.

    Hmm, but the question says "ternary pivot". Let me re-read...
    "isolated sandwiched ternary pivots at n=9 with P=2"

    OK so the pivot IS ternary (ms[4]=3). And P=2 might mean something else.

    Actually wait - in the entry conflict framework, "P" might be a DIFFERENT
    quantity. Let me re-read: "P = 2: pivot fires twice, creating 2 phases"

    Maybe in some cycles, a ternary processor only fires 2 times? That would
    break the good cycle condition (each proc fires exactly ms[p] times).

    UNLESS "P" refers to something like "the number of times the pivot
    creates a new phase" which could be different from fire count.

    OR: maybe the analysis is about a DIFFERENT state vector where the
    pivot position has ms=2 (binary) but is "ternary" in some other sense.

    I think the clearest path: just run both P=2 and P=3 cases and present
    the results. The user can determine which interpretation they meant.
    """
    pass


def refined_main():
    """
    Clean analysis focusing on distribution + ordering enumeration.
    """
    print("PIVOT LAYER ANALYSIS")
    print("=" * 70)
    print()
    print("ms = (3,3,2,2,3,2,2,3,3), n=9")
    print("Pivot at pos 4 (ms[4]=3)")
    print("Neighbors: pos 2,3 (binary), pos 5,6 (binary)")
    print()

    # Key question: with binary neighbors (each fires 2 times),
    # how do their firings distribute across pivot phases?

    for P in [2, 3]:
        print(f"\n{'#'*70}")
        print(f"# P = {P} (pivot fires {P} times)")
        print(f"{'#'*70}")

        # Each binary neighbor fires exactly 2 times.
        # These 2 firings are distributed across P phases.
        # Possible distributions of 2 into P buckets:

        print(f"\nDistributions of 2 firings into {P} phases:")
        dists = list(distribute(2, P))
        for d in dists:
            print(f"  {d}")

        print(f"\nPhase analysis:")
        print(f"  4 binary neighbors, each distributes 2 firings into {P} phases")
        print(f"  Total distribution combos: {len(dists)**4}")

        # Count phases with g=0 (left2t absent) or h=0 (right2t absent)
        # For layer analysis

        total = 0
        layer_counts = {1: 0, 2: 0, 3: 0, 99: 0}
        unclosed_examples = []

        for d_l2 in dists:  # left2t (pos 2)
            for d_lt in dists:  # left_t (pos 3)
                for d_rt in dists:  # right_t (pos 5)
                    for d_r2 in dists:  # right2t (pos 6)
                        total += 1
                        phases = []
                        for i in range(P):
                            phases.append({
                                'J': d_lt[i],  # left_t fires
                                'K': d_rt[i],  # right_t fires
                                'g': d_l2[i],  # left2t fires
                                'h': d_r2[i],  # right2t fires
                            })

                        layer = classify_phases_v2(phases, P)
                        layer_counts[layer] += 1
                        if layer == 99 and len(unclosed_examples) < 30:
                            unclosed_examples.append({
                                'phases': phases,
                                'd_l2': d_l2, 'd_lt': d_lt,
                                'd_rt': d_rt, 'd_r2': d_r2,
                            })

        print(f"\n  Results ({total} combos):")
        for layer in [1, 2, 3, 99]:
            label = {1: 'Layer 1 (pigeonhole)', 2: 'Layer 2 (non-tight EC)',
                     3: 'Layer 3 (binary recovery)', 99: 'Unclosed'}[layer]
            pct = 100 * layer_counts[layer] / total if total > 0 else 0
            print(f"    {label}: {layer_counts[layer]} ({pct:.1f}%)")

        if unclosed_examples:
            print(f"\n  Unclosed examples (up to 30):")
            for ex in unclosed_examples:
                phases_str = ", ".join(
                    f"(J={p['J']},K={p['K']},g={p['g']},h={p['h']})"
                    for p in ex['phases']
                )
                print(f"    Phases: [{phases_str}]")
                # Analyze why unclosed
                for i, p in enumerate(ex['phases']):
                    issues = []
                    if p['g'] == 0 and p['J'] == 0:
                        issues.append("g=0,J=0 (left idle)")
                    if p['h'] == 0 and p['K'] == 0:
                        issues.append("h=0,K=0 (right idle)")
                    if p['g'] > 0 and p['J'] > 0:
                        issues.append(f"g={p['g']},J={p['J']} (both active left)")
                    if p['h'] > 0 and p['K'] > 0:
                        issues.append(f"h={p['h']},K={p['K']} (both active right)")
                    if p['J'] == 1:
                        issues.append("J=1 (odd)")
                    if p['K'] == 1:
                        issues.append("K=1 (odd)")
                    if issues:
                        print(f"      Phase {i}: {', '.join(issues)}")


def classify_phases_v2(phases, P):
    """
    Classify phases by layer.

    Layer 1 (pigeonhole): P > 2 (binary fc) and some phase has
            g=0 & J>=1 or h=0 & K>=1

    Layer 2 (non-tight EC): Some phase has g=0 & J>=1 or h=0 & K>=1.
            With g=0, the domino (left2t -> left_t) can't form,
            so it's automatically non-tight. Layer 2 closes.

            KEY INSIGHT: if g=0 and J>=1 in ANY phase, layer 2 applies
            regardless of P, because the free second-neighbor means
            the first-neighbor's context is unconstrained on one side.

    Layer 3 (binary recovery): Some phase has even J>=2 or even K>=2.
            The binary neighbor fires an even number of times,
            returning to its original state, creating an entry conflict.
    """
    # First check: any phase with free second-neighbor and active first-neighbor?
    for phase in phases:
        # Left side: left2t absent, left_t present
        if phase['g'] == 0 and phase['J'] >= 1:
            if P > 2:
                return 1  # pigeonhole sufficient
            else:
                return 2  # non-tight EC (g=0 breaks domino chain)

        # Right side: right2t absent, right_t present
        if phase['h'] == 0 and phase['K'] >= 1:
            if P > 2:
                return 1
            else:
                return 2

    # Layer 3: even first-neighbor firings in some phase
    for phase in phases:
        if phase['J'] >= 2 and phase['J'] % 2 == 0:
            return 3
        if phase['K'] >= 2 and phase['K'] % 2 == 0:
            return 3

    return 99


if __name__ == '__main__':
    refined_main()

    # Also analyze: what distributions DON'T have any free phase?
    print("\n" + "=" * 70)
    print("DETAILED ANALYSIS: When does no phase have a free second-neighbor?")
    print("=" * 70)

    for P in [2, 3]:
        print(f"\nP = {P}:")
        dists = list(distribute(2, P))

        no_free_count = 0
        no_free_examples = []
        total = 0

        for d_l2 in dists:
            for d_lt in dists:
                for d_rt in dists:
                    for d_r2 in dists:
                        total += 1
                        has_free = False
                        for i in range(P):
                            if d_l2[i] == 0 and d_lt[i] >= 1:
                                has_free = True
                            if d_r2[i] == 0 and d_rt[i] >= 1:
                                has_free = True

                        if not has_free:
                            no_free_count += 1
                            if len(no_free_examples) < 20:
                                no_free_examples.append((d_l2, d_lt, d_rt, d_r2))

        print(f"  No-free-phase combos: {no_free_count} / {total} ({100*no_free_count/total:.1f}%)")

        if no_free_examples:
            print(f"  Examples:")
            for ex in no_free_examples:
                d_l2, d_lt, d_rt, d_r2 = ex
                print(f"    l2={d_l2}, lt={d_lt}, rt={d_rt}, r2={d_r2}")
                # For each phase, show structure
                for i in range(P):
                    g, J, K, h = d_l2[i], d_lt[i], d_rt[i], d_r2[i]
                    # No free means: whenever g=0 then J=0, and whenever h=0 then K=0
                    # Equivalently: J>0 implies g>0, and K>0 implies h>0
                    desc = f"g={g},J={J},K={K},h={h}"
                    if g > 0 and J > 0:
                        desc += " [left: both active → might be tight]"
                    if h > 0 and K > 0:
                        desc += " [right: both active → might be tight]"
                    print(f"      Phase {i}: {desc}")

                # Check layer 3
                for i in range(P):
                    J, K = d_lt[i], d_rt[i]
                    if J >= 2 and J % 2 == 0:
                        print(f"      -> Layer 3: J={J} even in phase {i}")
                    if K >= 2 and K % 2 == 0:
                        print(f"      -> Layer 3: K={K} even in phase {i}")
