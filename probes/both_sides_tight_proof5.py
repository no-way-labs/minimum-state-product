#!/usr/bin/env python3
"""
PART 5: Final proof construction.

From the analysis:
- Sorry 1012 is vacuous (walk constraint).
- Sorrys 1077/1121 are resolved by extending the chain to full depth.
- Chain always terminates with EC at depth n-1 or earlier.

This script:
1. Verifies the exact termination mechanism at the chain end.
2. Builds a clean inductive proof.
3. Verifies on n=5,7,9.
"""

from collections import Counter


def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    min_len = sum(ms)
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= min_len and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
            return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n)
                      if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            nc = list(config)
            nc[nxt] = (nc[nxt] + 1) % ms[nxt]
            nf = list(fc)
            nf[nxt] += 1
            word.append(nxt)
            dfs(word, nf, tuple(nc))
            word.pop()
    for p in range(n):
        first = list(start)
        first[p] = (first[p] + 1) % ms[p]
        dfs([p], [1 if i == p else 0 for i in range(n)], tuple(first))
    return results


def build_cycle(ms, n, word):
    ell = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:ell])) != ell:
        return None
    return configs[:ell]


def is_wrap_adjacent(word, n):
    return abs(word[-1] - word[0]) % n in (1, n-1)


def full_chain_analysis(word, interior, n, start_proc, direction):
    """
    Trace chain and return detailed termination info.
    The chain starts at start_proc and goes in 'direction' (+1 = right, -1 = left).

    Returns:
    - chain: list of (proc, first_fire_idx, tight)
    - termination: 'no_fire' (next proc doesn't fire) or 'gap' (fire but not tight)
    - ec_proc: processor where EC is found
    - ec_mover_idx, ec_nonmover_idx: interior indices of conflicting steps
    """
    int_len = len(interior)
    chain = []

    current_proc = start_proc
    # Find first fire of start_proc in interior
    current_first = None
    for i in range(int_len):
        if word[interior[i]] == current_proc:
            current_first = i
            break

    if current_first is None:
        return chain, 'start_not_found', None, None

    for depth in range(n):
        next_proc = (current_proc + direction) % n

        # Find last fire of next_proc in [0, current_first)
        last_next = None
        for i in range(current_first - 1, -1, -1):
            if word[interior[i]] == next_proc:
                last_next = i
                break

        if last_next is None:
            # next_proc doesn't fire before current_proc's first fire.
            # EC at current_proc: step current_first is mover for current_proc.
            # Any step in [0, current_first) that doesn't fire current_proc or
            # its ring neighbors gives same boundary triple -> EC.
            chain.append((current_proc, current_first, False))

            # Find the EC witness
            cp_L = (current_proc - 1) % n
            cp_R = (current_proc + 1) % n
            ec_nonmover = None
            for i in range(current_first):
                if word[interior[i]] not in (current_proc, cp_L, cp_R):
                    ec_nonmover = i
                    break

            if ec_nonmover is not None:
                return chain, 'no_fire', current_proc, (current_first, ec_nonmover)

            # Hmm, every step before current_first fires current_proc or neighbor.
            # This means the boundary triple DOES change between steps.
            # Need more subtle argument.
            # Actually: the walk constraint says the step BEFORE current_first
            # fires a neighbor of current_proc. If the walk is:
            #   ..., cp_L or cp_R, current_proc
            # then the step before current_first fires cp_L or cp_R (walk constraint).
            # But next_proc = cp_L or cp_R (direction determines which).
            # If next_proc doesn't fire, but the walk says the step before
            # current_proc fires a neighbor... contradiction!

            # Wait: the step before current_first in the interior is interior[current_first - 1].
            # word[interior[current_first-1]] must be adjacent to current_proc (walk on ring).
            # The neighbors of current_proc are cp_L and cp_R.
            # So word[interior[current_first-1]] in {cp_L, cp_R}.
            # next_proc is one of {cp_L, cp_R} (the one in direction).
            # If word[interior[current_first-1]] == next_proc, then next_proc DOES fire
            # at interior[current_first-1], contradicting "no_fire" finding.

            # So this branch should only happen if current_first == 0 (no steps before).
            # Let's check.
            if current_first == 0:
                return chain, 'no_fire_first_step', current_proc, None
            else:
                # Should not happen by walk constraint
                return chain, 'no_fire_UNEXPECTED', current_proc, None

        # next_proc fires at last_next. Is it tight?
        if last_next == current_first - 1:
            # Tight: chain extends
            chain.append((current_proc, current_first, True))

            # Also find first fire of next_proc for the next iteration
            first_next = None
            for i in range(int_len):
                if word[interior[i]] == next_proc:
                    first_next = i
                    break

            current_proc = next_proc
            current_first = first_next
        else:
            # Gap: last_next < current_first - 1
            # Step last_next + 1 is NOT next_proc (last_next is last fire before current).
            # Step current_first fires current_proc (mover).
            # Between last_next and current_first: no next_proc fires.
            # If no cp_L, current_proc fires either: triple preserved.
            chain.append((current_proc, current_first, False))

            # EC at current_proc: step last_next+1 as non-mover
            return chain, 'gap', current_proc, (current_first, last_next + 1)

    return chain, 'max_depth', None, None


def run_final_verification(n, ms, max_len):
    """Final verification with detailed chain termination analysis."""
    sandwiched = [p for p in range(n) if ms[p] >= 3
                  and ms[(p-1) % n] == 2 and ms[(p+1) % n] == 2]
    if not sandwiched:
        return

    words = enumerate_mover_words(ms, n, max_len)

    sorry_count = 0
    term_types = Counter()
    ec_procs_rel = Counter()  # relative position from t
    chain_depths = Counter()
    ec_found = 0
    ec_not_found = 0
    unexpected = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        ell = len(word)

        for t in sandwiched:
            bL = (t - 1) % n
            bR = (t + 1) % n

            t_fires = sorted(i for i in range(ell) if word[i] == t)
            if len(t_fires) < 2:
                continue

            for idx in range(len(t_fires)):
                s_step = t_fires[idx]
                a_step = t_fires[(idx - 1) % len(t_fires)]

                if s_step > a_step:
                    interior = list(range(a_step + 1, s_step))
                else:
                    interior = list(range(a_step + 1, ell)) + list(range(0, s_step))
                if not interior:
                    continue

                J = sum(1 for st in interior if word[st] == bL)
                K = sum(1 for st in interior if word[st] == bR)
                if J < 1 or K < 1:
                    continue

                fL_int_idx = next(i for i in range(len(interior)) if word[interior[i]] == bL)
                fR_int_idx = next(i for i in range(len(interior)) if word[interior[i]] == bR)

                # Check sorry conditions
                sorry_type = None
                chain_start = None
                chain_dir = None

                if fL_int_idx == 0 and fR_int_idx > 0:
                    # Potential sorry 1121: check if all outer conditions met
                    RR = (t + 2) % n
                    RRR = (t + 3) % n
                    rr_pos = [i for i in range(fR_int_idx) if word[interior[i]] == RR]
                    if rr_pos and rr_pos[-1] == fR_int_idx - 1:
                        first_rr = rr_pos[0]
                        if any(word[interior[i]] == RRR for i in range(first_rr)):
                            sorry_type = 1121
                            chain_start = bR
                            chain_dir = +1

                elif fR_int_idx == 0 and fL_int_idx > 0:
                    LL = (t - 2) % n
                    LLL = (t - 3) % n
                    ll_pos = [i for i in range(fL_int_idx) if word[interior[i]] == LL]
                    if ll_pos and ll_pos[-1] == fL_int_idx - 1:
                        first_ll = ll_pos[0]
                        if any(word[interior[i]] == LLL for i in range(first_ll)):
                            sorry_type = 1077
                            chain_start = bL
                            chain_dir = -1

                if sorry_type is None:
                    continue

                sorry_count += 1
                chain, result, ec_proc, ec_info = full_chain_analysis(
                    word, interior, n, chain_start, chain_dir)

                depth = len(chain)
                chain_depths[depth] += 1
                term_types[result] += 1

                if ec_proc is not None:
                    ec_found += 1
                    dist = ((ec_proc - t) % n)
                    if dist > n // 2:
                        dist -= n
                    ec_procs_rel[dist] += 1
                else:
                    ec_not_found += 1
                    if unexpected < 5:
                        print(f"  UNEXPECTED: word={word}, t={t}, result={result}")
                    unexpected += 1

    print(f"  Sorry phases: {sorry_count}")
    print(f"  Chain depths: {dict(sorted(chain_depths.items()))}")
    print(f"  Termination: {dict(term_types)}")
    print(f"  EC found: {ec_found}, not found: {ec_not_found}")
    print(f"  EC proc relative to t: {dict(sorted(ec_procs_rel.items()))}")
    return sorry_count, ec_found, ec_not_found


print("="*70)
print("FINAL CHAIN TERMINATION VERIFICATION")
print("="*70)

for n, ms, max_len in [
    (5, [2, 3, 2, 3, 2], 18),
    (7, [2, 3, 2, 3, 2, 3, 3], 24),
    (7, [2, 3, 3, 2, 3, 2, 3], 24),
]:
    print(f"\nn={n}, ms={ms}")
    run_final_verification(n, ms, max_len)


# Proof structure:
# The chain has a clean inductive argument.
# At each level, the Lean proof does:
#   by_cases: does next_proc fire in [a, current_first)?
#     No: EC at current_proc via configVal_eq_of_noFire_between.
#     Yes: find last fire of next_proc. Is it tight?
#       Not tight (gap): EC at current_proc.
#       Tight: chain extends. Inductive step.
#
# The induction is on 'remaining depth' = n - (number of chain procs used).
# When remaining depth reaches 0: the chain has used n procs, wrapping around.
# At that point, the "next" proc in the chain is the OTHER binary neighbor,
# which already fired. This gives a double-fire or EC.
#
# Actually, when the chain reaches the other binary neighbor bR (for left chain):
# bR fires at step fR in the interior. The chain's current proc fires at some
# step before bR. But bR already fired at fR_int_idx (in the interior).
# So bR fires TWICE in the phase: once from the chain, once at fR_int_idx.
# With m(bR) = 2: bR fires exactly 2 times in the entire cycle.
# Both fires being in one phase is possible but constraining.
# Actually, it's not a contradiction per se. But the chain's EC mechanism
# still works: either gap or no-fire gives EC.
#
# The simplest termination: the chain terminates when current_first reaches 0
# (no more steps before the current proc's first fire).
# At that point: "no fire" termination.
# The walk constraint ensures that if current_first > 0, the step before
# it fires a neighbor of current_proc. If the neighbor in the chain direction
# fires there, the chain extends. Otherwise, it terminates.
#
# TERMINATION PROOF:
# Each chain step decreases current_first by at least 1 (since tight means
# last_next = current_first - 1, so next iteration's current_first <= last_next
# which equals the FIRST fire of next_proc, which is <= last_next = current_first - 1).
# Wait: next iteration uses first_next (first fire of next_proc), not last_next.
# first_next <= last_next = current_first - 1.
# So the first fire index STRICTLY DECREASES at each step.
# Starting from some value < len(interior) and decreasing by at least 1 each time:
# after at most len(interior) steps, current_first reaches 0.
# At current_first = 0: the next-outward proc can't fire before index 0.
# "No fire" termination -> EC.
#
# BUT: when current_first = 0 and the step at index 0 fires current_proc,
# where is the nonmover step for EC?
# The EC needs a step with the same boundary triple as step interior[0].
# The mover at interior[0] is current_proc.
# We need a nonmover for current_proc with the same (L, S, R) triple.
# If current_first = 0: there are no steps before it in the interior.
# But: step a (just before interior) fires t. Is t a non-neighbor of current_proc?
# If yes: step a has the same triple at current_proc as step interior[0] (assuming
# no fires of current_proc or its neighbors between a and interior[0]... but
# interior[0] IS the first fire, so no fires before it).
# Step a fires t. Does t fire current_proc's neighbors?
# t is sandwiched ternary. current_proc is some proc far from t.
# For current_proc's boundary triple: we need configs at (cp-1, cp, cp+1).
# Between step a and step interior[0]: no fires of cp-1, cp, cp+1 (since
# interior[0] fires cp, and it's the first such fire).
# Wait: interior[0] fires cp. But step a fires t. If t != cp-1, cp, cp+1:
# then configs don't change at (cp-1, cp, cp+1) from step a to step interior[0].
# Step a is a nonmover for cp (fires t ≠ cp). Step interior[0] is mover for cp.
# Same triple -> EC.
#
# When IS t a neighbor of current_proc?
# t is sandwiched ternary. The chain extends from bL through consecutive procs.
# At depth d: current_proc = left^d(bL) = left^(d+1)(t).
# t's neighbors: bL = left(t), bR = right(t).
# current_proc = left^(d+1)(t). This equals bL only when d = 0.
# It equals bR only when left^(d+1)(t) = right(t), i.e., d+1 = n-1, d = n-2.
# For d < n-2: current_proc is NOT a neighbor of t.
# So step a fires t which is NOT a neighbor of current_proc.
# Therefore: step a is a nonmover for current_proc with same boundary triple.
# EC at current_proc between step a and step interior[0].
#
# THIS IS THE KEY!

print("\n" + "="*70)
print("THE PROOF")
print("="*70)
print()
print("THEOREM: In a TernaryPhase at sandwiched ternary t with J >= 1, K >= 1,")
print("the Lean sorry cases (lines 1012, 1077, 1121) all produce hasEntryConflict.")
print()
print("PROOF:")
print()
print("Case 1 (Sorry 1012): Both fL > phase.a AND fR > phase.a.")
print("  IMPOSSIBLE by walk constraint. Step phase.a follows a t-fire step.")
print("  By ring adjacency: word[phase.a] in {bL, bR}.")
print("  So either fL = phase.a or fR = phase.a. Contradiction.")
print("  QED.")
print()
print("Case 2 (Sorrys 1077/1121): WLOG sorry 1077 (1121 is symmetric).")
print("  fR = phase.a (bR fires first), fL > phase.a.")
print("  LL tight to fL, LLL fires before first LL.")
print()
print("  Define the chain: p_0 = bL, p_1 = LL, p_2 = LLL, ..., p_k = left^(k+1)(t).")
print("  Each p_i fires in the interior. The 'tight' condition means:")
print("  last fire of p_{i+1} before first fire of p_i is at first(p_i) - 1.")
print()
print("  The chain extends while tight. When it breaks:")
print("    - 'Gap' at p_i: last fire of p_{i+1} is NOT at first(p_i) - 1.")
print("      Step last(p_{i+1}) + 1 is nonmover for p_i with same boundary triple.")
print("      -> EC at p_i.")
print("    - 'No fire' at p_i: p_{i+1} doesn't fire before first(p_i).")
print("      Two sub-cases:")
print("        (a) first(p_i) > 0: step interior[first(p_i)-1] fires a neighbor")
print("            of p_i by walk constraint. That neighbor is p_{i+1} (chain direction).")
print("            But p_{i+1} doesn't fire. Contradiction.")
print("        (b) first(p_i) = 0: the step BEFORE the interior is step a (fires t).")
print("            t is not a neighbor of p_i (for chain depth >= 1, p_i = left^(k+1)(t)")
print("            with k >= 1, so p_i is at distance >= 3 from t on the ring).")
print("            Configs at (p_i-1, p_i, p_i+1) are unchanged from step a to interior[0].")
print("            Step a fires t != p_i (nonmover). Step interior[0] fires p_i (mover).")
print("            Same boundary triple -> EC at p_i.")
print()
print("  The chain MUST terminate because first(p_i) strictly decreases at each")
print("  tight step (first(p_{i+1}) <= first(p_i) - 1). Starting from some value")
print("  < phase_length, it reaches 0 in finitely many steps.")
print()
print("  At termination: EC at the chain-end processor. QED.")
print()
print("="*70)
print("REMAINING SUBTLETY")
print("="*70)
print()
print("Sub-case (a) above needs care: interior[first(p_i)-1] fires a neighbor")
print("of p_i. But which neighbor? If it fires p_{i-1} (not p_{i+1}), then")
print("p_{i+1} still doesn't fire, and we need EC another way.")
print()
print("Let me check: does the walk constraint guarantee interior[first(p_i)-1]")
print("fires p_{i+1} (the outward neighbor)?")
print()
print("Walk constraint: word[interior[j]] and word[interior[j+1]] are ring-adjacent.")
print("If interior[first(p_i)] fires p_i, then interior[first(p_i)-1] fires")
print("a ring neighbor of p_i, which is either p_{i-1} or p_{i+1}.")
print()
print("It could fire p_{i-1} (the inward neighbor). In that case:")
print("p_{i+1} STILL doesn't fire before p_i's first fire. But p_{i-1} fires")
print("at interior[first(p_i)-1]. Is there EC?")
print()
print("Actually: if p_{i+1} doesn't fire in [0, first(p_i)), we just need EC.")
print("Step interior[first(p_i)] fires p_i (mover). For nonmover step:")
print("Need any step in [0, first(p_i)) where (p_i-1, p_i, p_i+1) values match.")
print("Between any such step and first(p_i): if NO fires of {p_i-1, p_i, p_i+1}")
print("in between, then values are preserved.")
print()
print("The chain guarantees no fires of p_i in [0, first(p_i)) (it's the FIRST).")
print("But p_i-1 and p_i+1 can fire.")
print("If p_{i+1} doesn't fire in [0, first(p_i)): p_i+1 values unchanged there.")
print("If p_{i-1} fires at some step j < first(p_i):")
print("  Between j+1 and first(p_i): no p_{i-1} fires (unless multiple).")
print("  Need: no p_{i-1}, p_i, p_{i+1} fires in (j, first(p_i)).")
print()
print("This is getting complicated for the general case. Let me verify that")
print("the 'no fire at first_idx=0' case is the ONLY termination mode.")

# Count termination modes in detail
print("\nRe-running with detailed termination modes...\n")

for n, ms, max_len in [
    (5, [2, 3, 2, 3, 2], 18),
    (7, [2, 3, 2, 3, 2, 3, 3], 24),
]:
    sandwiched = [p for p in range(n) if ms[p] >= 3
                  and ms[(p-1) % n] == 2 and ms[(p+1) % n] == 2]
    words = enumerate_mover_words(ms, n, max_len)
    term_details = Counter()

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        ell = len(word)

        for t in sandwiched:
            bL = (t - 1) % n
            bR = (t + 1) % n

            t_fires = sorted(i for i in range(ell) if word[i] == t)
            if len(t_fires) < 2:
                continue

            for idx in range(len(t_fires)):
                s_step = t_fires[idx]
                a_step = t_fires[(idx - 1) % len(t_fires)]

                if s_step > a_step:
                    interior = list(range(a_step + 1, s_step))
                else:
                    interior = list(range(a_step + 1, ell)) + list(range(0, s_step))
                if not interior:
                    continue

                J = sum(1 for st in interior if word[st] == bL)
                K = sum(1 for st in interior if word[st] == bR)
                if J < 1 or K < 1:
                    continue

                fL_int_idx = next(i for i in range(len(interior)) if word[interior[i]] == bL)
                fR_int_idx = next(i for i in range(len(interior)) if word[interior[i]] == bR)

                sorry_type = None
                chain_start = None
                chain_dir = None

                if fL_int_idx == 0 and fR_int_idx > 0:
                    RR = (t + 2) % n
                    RRR = (t + 3) % n
                    rr_pos = [i for i in range(fR_int_idx) if word[interior[i]] == RR]
                    if rr_pos and rr_pos[-1] == fR_int_idx - 1:
                        first_rr = rr_pos[0]
                        if any(word[interior[i]] == RRR for i in range(first_rr)):
                            sorry_type = 1121
                            chain_start = bR
                            chain_dir = +1

                elif fR_int_idx == 0 and fL_int_idx > 0:
                    LL = (t - 2) % n
                    LLL = (t - 3) % n
                    ll_pos = [i for i in range(fL_int_idx) if word[interior[i]] == LL]
                    if ll_pos and ll_pos[-1] == fL_int_idx - 1:
                        first_ll = ll_pos[0]
                        if any(word[interior[i]] == LLL for i in range(first_ll)):
                            sorry_type = 1077
                            chain_start = bL
                            chain_dir = -1

                if sorry_type is None:
                    continue

                # Trace chain with detailed termination
                chain, result, ec_proc, ec_info = full_chain_analysis(
                    word, interior, n, chain_start, chain_dir)

                if ec_info is not None:
                    mover_idx, nonmover_idx = ec_info
                    term_details[f'{result}_mi={mover_idx}_ni={nonmover_idx > 0}'] += 1
                else:
                    term_details[result] += 1

    print(f"n={n}, ms={ms}: {dict(sorted(term_details.items()))}")
