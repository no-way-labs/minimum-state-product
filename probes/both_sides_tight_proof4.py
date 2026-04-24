#!/usr/bin/env python3
"""
PART 4: Verify chain termination depth and build the inductive proof.

Critical question: What is the MAXIMUM chain depth observed?
If it's bounded by a small constant (relative to n), we can unroll.
If it grows with n, we need proper induction.

Also: verify that every sorry-case cycle has EC at SOME chain proc.
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


def find_all_ec(word, cycle, ms, n):
    ell = len(word)
    ecs = []
    for p in range(n):
        pL = (p - 1) % n
        pR = (p + 1) % n
        mover_triples = {}
        for step in range(ell):
            triple = (cycle[step][pL], cycle[step][p], cycle[step][pR])
            if word[step] == p:
                mover_triples[triple] = step
            elif triple in mover_triples:
                ecs.append((p, mover_triples[triple], step))
    return ecs


def trace_chain(word, interior, n, start_proc, direction, max_depth):
    """Trace the chain from start_proc in given direction.

    The chain works backwards from a first-fire position:
    We have a sequence of procs p1, p2, p3, ... going outward from t.
    p1 fires at some position in interior. p2 fires just before p1 (tight).
    p3 fires before p2. Etc.

    For the sorry analysis:
    - direction='left': chain goes t, bL, LL, LLL, ... (indices decrease)
    - direction='right': chain goes t, bR, RR, RRR, ... (indices increase)

    We trace the chain of TIGHT fires going outward.
    Returns the chain and how it terminates.
    """
    chain = []

    # The chain is described by the sequence of first fires going outward.
    # At each level, we look for the FIRST fire of the next-outward proc.
    # If it exists and is tight (immediately before the current first fire),
    # the chain extends. Otherwise, it terminates.

    # Start: proc at distance 1 from t (bL or bR) fires at some position.
    # The first fire of the starting proc:
    int_len = len(interior)

    # For sorry 1077: bR fires at interior[0], chain goes LEFT.
    # bL fires at interior[fL_int_idx]. The chain from bL:
    #   LL fires before bL (tight means just before bL's first fire)
    #   LLL fires before LL
    #   ...

    # For sorry 1121: bL fires at interior[0], chain goes RIGHT.
    # bR fires at interior[fR_int_idx]. The chain from bR:
    #   RR fires before bR (tight means just before bR's first fire)
    #   RRR fires before RR
    #   ...

    # The chain is a sequence of procs going outward.
    # At each step: find first fire of current proc, check if next-outward fires before it.

    current_proc = start_proc
    current_first_idx = None  # interior index of first fire of current_proc

    # Find first fire of start_proc
    for i in range(int_len):
        if word[interior[i]] == start_proc:
            current_first_idx = i
            break

    if current_first_idx is None:
        return chain, 'start_not_found'

    for depth in range(max_depth):
        next_proc = (current_proc + direction) % n

        # Find first fire of next_proc in interior[0 : current_first_idx)
        next_first_idx = None
        for i in range(current_first_idx):
            if word[interior[i]] == next_proc:
                next_first_idx = i
                break

        if next_first_idx is None:
            # next_proc doesn't fire before current_proc
            chain.append({
                'proc': current_proc,
                'first_fire_idx': current_first_idx,
                'next_proc': next_proc,
                'termination': 'no_fire',
                'depth': depth,
            })
            return chain, 'ec_at_' + str(current_proc)

        # Find LAST fire of next_proc before current_first_idx
        last_next_idx = None
        for i in range(current_first_idx - 1, -1, -1):
            if word[interior[i]] == next_proc:
                last_next_idx = i
                break

        # Is it tight? (last fire of next_proc is immediately before first fire of current_proc)
        tight = (last_next_idx == current_first_idx - 1)

        if not tight:
            # Gap between last next_proc fire and first current_proc fire
            # EC at current_proc: step after last next_proc fire has same triple
            chain.append({
                'proc': current_proc,
                'first_fire_idx': current_first_idx,
                'next_proc': next_proc,
                'last_next_fire': last_next_idx,
                'termination': 'gap',
                'depth': depth,
            })
            return chain, 'ec_at_' + str(current_proc)

        # Tight: chain extends
        chain.append({
            'proc': current_proc,
            'first_fire_idx': current_first_idx,
            'next_proc': next_proc,
            'termination': 'tight',
            'depth': depth,
        })

        current_proc = next_proc
        current_first_idx = next_first_idx

    chain.append({
        'proc': current_proc,
        'first_fire_idx': current_first_idx,
        'termination': 'max_depth',
        'depth': max_depth,
    })
    return chain, 'max_depth'


def analyze_all(n, ms, max_len):
    """Full analysis of chain depths for all sorry-case phases."""
    sandwiched = [p for p in range(n) if ms[p] >= 3
                  and ms[(p-1) % n] == 2 and ms[(p+1) % n] == 2]
    if not sandwiched:
        print(f"  No sandwiched ternary. Skipping.")
        return

    words = enumerate_mover_words(ms, n, max_len)
    print(f"  Total words: {len(words)}")

    chain_stats = Counter()
    max_chain_depth = 0
    termination_types = Counter()
    sorry_phases = 0
    ec_verified = 0
    ec_missing = 0

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

                int_movers = [word[st] for st in interior]
                fL_int_idx = next(i for i in range(len(interior)) if word[interior[i]] == bL)
                fR_int_idx = next(i for i in range(len(interior)) if word[interior[i]] == bR)

                # Sorry 1121: fL at start, chain goes RIGHT
                if fL_int_idx == 0 and fR_int_idx > 0:
                    # Need to check: is the sorry condition met?
                    # RR tight to fR, and RRR fires before first RR
                    RR = (t + 2) % n
                    steps_before_fR = [word[interior[i]] for i in range(fR_int_idx)]
                    rr_positions = [i for i in range(fR_int_idx) if word[interior[i]] == RR]

                    if rr_positions and rr_positions[-1] == fR_int_idx - 1:
                        # RR tight. Now check if the Lean sorry applies.
                        # The Lean sorry at 1121: RRR fires before first RR
                        RRR = (t + 3) % n
                        first_rr = rr_positions[0]
                        rrr_before = any(word[interior[i]] == RRR for i in range(first_rr))

                        if rrr_before:
                            sorry_phases += 1

                            # Trace the full chain
                            chain, result = trace_chain(word, interior, n, bR, +1, n)
                            depth = len(chain)
                            max_chain_depth = max(max_chain_depth, depth)
                            chain_stats[depth] += 1

                            if 'ec_at' in result:
                                termination_types['ec'] += 1
                                ec_verified += 1
                            else:
                                termination_types[result] += 1
                                # Check if cycle actually has EC
                                ecs = find_all_ec(word, cycle, ms, n)
                                if ecs:
                                    ec_verified += 1
                                else:
                                    ec_missing += 1
                                    print(f"  NO EC! word={word}, t={t}, chain={result}")

                # Sorry 1077: fR at start, chain goes LEFT
                if fR_int_idx == 0 and fL_int_idx > 0:
                    LL = (t - 2) % n
                    ll_positions = [i for i in range(fL_int_idx) if word[interior[i]] == LL]

                    if ll_positions and ll_positions[-1] == fL_int_idx - 1:
                        LLL = (t - 3) % n
                        first_ll = ll_positions[0]
                        lll_before = any(word[interior[i]] == LLL for i in range(first_ll))

                        if lll_before:
                            sorry_phases += 1

                            chain, result = trace_chain(word, interior, n, bL, -1, n)
                            depth = len(chain)
                            max_chain_depth = max(max_chain_depth, depth)
                            chain_stats[depth] += 1

                            if 'ec_at' in result:
                                termination_types['ec'] += 1
                                ec_verified += 1
                            else:
                                termination_types[result] += 1
                                ecs = find_all_ec(word, cycle, ms, n)
                                if ecs:
                                    ec_verified += 1
                                else:
                                    ec_missing += 1
                                    print(f"  NO EC! word={word}, t={t}, chain={result}")

    print(f"  Sorry phases: {sorry_phases}")
    print(f"  Max chain depth: {max_chain_depth}")
    print(f"  Chain depth distribution: {dict(sorted(chain_stats.items()))}")
    print(f"  Termination types: {dict(termination_types)}")
    print(f"  EC verified: {ec_verified}, EC missing: {ec_missing}")

    return {
        'sorry_phases': sorry_phases,
        'max_depth': max_chain_depth,
        'ec_verified': ec_verified,
        'ec_missing': ec_missing,
    }


print("="*70)
print("CHAIN DEPTH AND TERMINATION ANALYSIS")
print("="*70)

for n, ms, max_len in [
    (5, [2, 3, 2, 3, 2], 18),
    (7, [2, 3, 2, 3, 2, 3, 3], 24),
    (7, [2, 3, 3, 2, 3, 2, 3], 24),
]:
    print(f"\nn={n}, ms={ms}, max_len={max_len}")
    analyze_all(n, ms, max_len)


# Now let's understand the PROOF mechanism more precisely.
# The chain traces fires going outward from t.
# At each level, the chain either terminates (EC) or extends (tight fire).
# When tight, the step sequence at the boundary is:
#   ..., next_proc fires, current_proc fires
# (consecutive steps, adjacent procs on ring).
#
# This is a LOCAL SWEEP pattern: two adjacent procs fire in consecutive steps,
# with the outer one firing first.
#
# The chain is a sequence of such sweeps. The full pattern looks like:
# step a fires t
# step a+1 fires bL (or bR)
# step a+2 fires LL (tight to bL) -- if chain extends this far
# step a+3 fires LLL (tight to LL) -- if chain extends this far
# ...
#
# This is EXACTLY a sweep going outward from t!
# The first few interior steps sweep LEFT (or RIGHT) through consecutive procs.
# The chain terminates when this sweep breaks (some proc skips or doesn't fire).
#
# KEY INSIGHT: The sweep consumes consecutive steps AND consecutive procs.
# After k steps of sweep: procs t, p1, p2, ..., pk have fired at steps a, a+1, ..., a+k.
# The remaining phase has s - a - k - 1 steps for the other side's fires.
#
# The chain from the OTHER side (bR) fires at step a+1 (sorry 1077/1121).
# Wait: in sorry 1121, bL fires at a+1 and the chain goes RIGHT from bR.
# The bR chain fires are at positions BEFORE bR's first fire in the interior.
# These positions are AFTER a+1 (bL's fire) and BEFORE fR.
#
# So the sweep from one side occupies steps a+1, a+2, ..., a+k (firing bL, LL, LLL, ...).
# And the RR chain occupies steps somewhere between a+k+1 and fR-1.
#
# These are NON-OVERLAPPING sections of the interior.
# Total interior steps used: k (left sweep) + chain from right.
# Phase length = s - a. Interior = s - a - 1 steps.
# Both chains must fit within the interior.

print("\n" + "="*70)
print("SWEEP PATTERN ANALYSIS")
print("="*70)
print()
print("The chain is a SWEEP: consecutive procs fire in consecutive steps.")
print("In the sorry case, the sweep goes outward from t:")
print("  step a fires t")
print("  step a+1 fires bL (leftward sweep)")
print("  step a+2 fires LL (if tight)")
print("  step a+3 fires LLL (if tight)")
print("  ...")
print()
print("From the other side, bR fires at some step fR > a+1.")
print("The 'sweep' from the left uses steps a+1 through a+k.")
print("The right chain uses steps between a+k+1 and fR.")
print()
print("The KEY constraint: the sweep from one side and the chain from")
print("the other side must SHARE the finite interior steps.")
print("This limits the maximum combined depth.")
print()
print("For the LEAN PROOF:")
print("  The sorry needs hasEntryConflict gc.")
print("  The chain ALWAYS produces EC because:")
print("  1. At each chain level, either EC (gap/no-fire) or extend (tight).")
print("  2. The chain can extend at most floor((n-3)/2) levels from one side")
print("     before the procs from both sides overlap on the ring.")
print("  3. At the overlap, a processor fires in both chains -> double-fire or EC.")
print()
print("  SIMPLEST LEAN FIX: Generalize the chain pattern into a recursive lemma:")
print("    chain_ec (depth : Nat) (p : Fin n) (bound : Fin cycle_len)")
print("    : depth > 0 -> ... -> hasEntryConflict gc")
print("  with decreasing argument on depth (starting from n).")
