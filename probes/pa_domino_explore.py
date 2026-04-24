#!/usr/bin/env python3
"""
PA Domino Exploration: Prove entry conflict for consecutive binary normalForm residual.

Setup: 3 consecutive binary at positions {i, t=right(i), right²(i)}.
t has fc(t) ≥ 2, fires in isolated fashion.
Under ¬EC and normalForm phases (J+K ≤ 1 after dispatch failure),
we have fc(left t) + fc(right t) = fc(t), and each phase has J+K = 1.

Key insight to test: binary fire counts must be even (≥2), so
  fc(left t) ≥ 2, fc(right t) ≥ 2, fc(t) = fc(left t) + fc(right t) ≥ 4.

Then: track contexts at t-fire steps. Binary neighbors → only 8 possible contexts.
With fc(t) ≥ 4, check if EC is forced.
"""
from itertools import product as iproduct

def analyze_domino(fc_t, fc_left, fc_right, verbose=False):
    """
    Given fc(t), fc(left t), fc(right t), enumerate all possible phase sequences
    and check whether EC is forced at t.

    Phase sequence: binary string of length fc(t).
    phase[k] = 0 means (J,K) = (1,0) in phase k (left fires, right doesn't)
    phase[k] = 1 means (J,K) = (0,1) in phase k (right fires, left doesn't)

    Constraint: number of 0s = fc_left, number of 1s = fc_right.

    At t-fire step s_k (k = 0, ..., fc_t - 1):
    - S_k = c_t at step s_k. t is binary, fires each time: S alternates 0,1,0,1,...
      Starting value s0 ∈ {0,1}. S_k = (s0 + k) % 2.
    - L_k = c_{left t} at step s_k. left(t) is binary.
      L_k depends on cumulative left-fires in phases 0..k-1 (phases before this t-fire).
      Actually, in phase k, left fires BEFORE t fires (if phase[k]=0).
      Wait — ordering within a phase matters.
    """
    # We need to be more careful about ordering within a phase.
    # In a sweep good cycle, within each phase (between consecutive t-fires),
    # either left(t) or right(t) fires once.
    # The order: in a CW sweep, the mover visits ..., left(t), t, right(t), ...
    # or in a CCW sweep: ..., right(t), t, left(t), ...
    #
    # But this is the normalForm residual where we have isolated t-firings
    # (not necessarily sweep). Let's think about what "phase k" means:
    # Between t-fire at step s_{k-1} and t-fire at step s_k,
    # exactly one of {left(t), right(t)} fires once.
    #
    # For the context at t when t fires at step s_k:
    # The left value L_k depends on whether left(t) fired in phases 0..k-1,
    # and critically, whether left(t) fires BEFORE or AFTER t in phase k.
    #
    # Actually, the phase is the INTERVAL between consecutive t-fires.
    # Phase k is from step s_{k-1}+1 to step s_k.
    # The left/right firing happens somewhere in this interval.
    # So at step s_k (when t fires), the left/right neighbor's value reflects
    # all firings in phases 0..k (inclusive of phase k, since the neighbor
    # fires before t fires at s_k).
    #
    # Let me define:
    # - L_k = starting left value + (number of left fires in phases 1..k) mod 2
    #   where "phase k" includes firings BEFORE step s_k
    # - Similarly for R_k

    # Let's enumerate:
    # phase_seq[k] for k = 1, ..., fc_t tells us what fires in phase k
    # (between s_{k-1} and s_k)
    # But we also need the "wrap phase" (from s_{fc_t-1} back to s_0).
    # Actually for a cyclic good cycle, there are exactly fc_t phases
    # (gaps between consecutive t-fires), including the wrap-around.

    # Let me index phases as k = 0, ..., fc_t - 1.
    # Phase k is the interval after t-fire k and before t-fire (k+1) mod fc_t.
    # In phase k, if phase_seq[k] = 0, left fires once; if 1, right fires once.

    # At t-fire step k, the context (L_k, S_k, R_k):
    # S_k = (s0 + k) % 2  (t alternates each fire)
    # L_k = (l0 + cumulative_left_fires_up_to_step_s_k) % 2
    # R_k = (r0 + cumulative_right_fires_up_to_step_s_k) % 2

    # The cumulative left fires "up to step s_k" means: fires in phases 0..k-1
    # (those are the phases that complete before t-fire k), PLUS whatever
    # fires in phase k that happen before step s_k.
    # But wait: t-fire k happens at step s_k. Phase k is AFTER t-fire k.
    # So the firings that affect L_k are those in phases 0, 1, ..., k-1
    # (the phases between t-fires 0→1, 1→2, ..., (k-1)→k).

    # Actually let me re-index. Phase k is the gap between t-fire (k-1) and t-fire k.
    # So phase 1 is between t-fire 0 and t-fire 1.
    # The wrap-around phase 0 is between t-fire (fc_t - 1) and t-fire 0.

    # At t-fire k (k = 0, ..., fc_t - 1):
    # Cumulative left fires before t-fire k = sum of left fires in phases 1..k
    #   (phases that complete before t-fire k)
    # Cumulative left fires through the whole cycle = sum over all fc_t phases = fc_left

    # Since left is binary: fc_left is even (left returns to initial value).
    # Similarly fc_right is even.

    # So at t-fire k:
    #   cum_left(k) = sum_{j=1}^{k} phase_seq[j] == 0  (i.e., count of 0s in phases 1..k)
    #   Wait, phase_seq[j] = 0 means left fires. Let me use:
    #   left_in_phase[j] = 1 if phase_seq[j] = 0, else 0
    #   right_in_phase[j] = 1 if phase_seq[j] = 1, else 0

    # cum_left(k) = sum_{j=1}^{k} left_in_phase[j]  (for k ≥ 1)
    # cum_left(0) = 0  (no phases complete before t-fire 0)

    # L_k = (l0 + cum_left(k)) % 2
    # R_k = (r0 + cum_right(k)) % 2
    # S_k = (s0 + k) % 2

    # Check: after full cycle, cum_left(fc_t) should equal fc_left
    # But cum_left(fc_t) = sum_{j=1}^{fc_t} left_in_phase[j]
    # We have fc_t phases total (indexed 1..fc_t, wrapping phase 0 → phase fc_t).
    # Wait, I have fc_t phases indexed 0..fc_t-1. Let me use 0-indexing.

    # Re-do with 0-indexing:
    # Phases: p_0, p_1, ..., p_{fc_t - 1}
    # p_k is the gap between t-fire k and t-fire (k+1) mod fc_t

    # At t-fire k:
    # All phases that completed before t-fire k are p_0, ..., p_{k-1} (cyclically)
    # Wait, for a cyclic arrangement:
    # t-fire 0 → p_0 → t-fire 1 → p_1 → ... → t-fire (fc_t-1) → p_{fc_t-1} → t-fire 0

    # So before t-fire k, the completed phases are p_0, ..., p_{k-1}.
    # Before t-fire 0, no phases have completed (or equivalently, all have completed cyclically).

    # cum_left(k) = sum_{j=0}^{k-1} left_in_phase[j]  for k ≥ 1
    # cum_left(0) = 0

    # L_k = (l0 + cum_left(k)) % 2
    # R_k = (r0 + cum_right(k)) % 2
    # S_k = (s0 + k) % 2

    # Cyclic consistency: after all fc_t phases, left returns to l0.
    # cum_left(fc_t) ≡ sum of all left_in_phase = fc_left ≡ 0 (mod 2)  ✓ (fc_left even)

    # For EC: we need two indices k1 ≠ k2 with (L_{k1}, S_{k1}, R_{k1}) = (L_{k2}, S_{k2}, R_{k2})
    # AND at one step t is the mover (always true at t-fire steps).
    # But we also need the SAME context to appear at a NON-mover step.

    # Wait — EC means: there exist steps a, b where mover(a) = t, mover(b) ≠ t,
    # and the context at t is the same.

    # At t-fire step s_k: mover = t, context = (L_k, S_k, R_k).
    # At non-t-fire steps: we need to know the context at t.
    # Between t-fires k and k+1, exactly one neighbor fires.

    # If phase k has left firing (phase_seq[k] = 0):
    #   At the start of phase k (right after t-fire k), context at t is:
    #     (L_k', S_k', R_k') where S_k' = (s0 + k + 1) % 2 (t just fired, so value changed)
    #     Wait no. At t-fire k, t's value changes from S_k to (S_k + 1) % 2.
    #     So right after t-fire k: config at t is (L_k, (S_k+1)%2, R_k)
    #     Hmm, but L_k might change too if left fired at a step before s_k in the same phase...
    #     No. L_k is the value at step s_k (when t fires). Right after t fires,
    #     left hasn't fired yet in phase k. So the config at t is (L_k, (S_k+1)%2, R_k).
    #   Then left fires somewhere in phase k. Before left fires, context at t (non-mover) is:
    #     Still (L_k, (S_k+1)%2, R_k) (nothing changed at t's neighborhood except t itself).
    #     Wait, other processors might fire too! In a general good cycle, many procs fire
    #     between t-fires. Only left(t) and right(t) affect t's context.
    #   After left fires in phase k, the context at t becomes:
    #     ((L_k+1)%2, (S_k+1)%2, R_k)
    #   At t-fire k+1 (step s_{k+1}), the context at t is:
    #     L_{k+1} = (l0 + cum_left(k+1)) % 2 = (L_k + left_in_phase[k]) % 2
    #     If phase_seq[k] = 0: L_{k+1} = (L_k + 1) % 2
    #     S_{k+1} = (s0 + k + 1) % 2 = (S_k + 1) % 2
    #     R_{k+1} = (r0 + cum_right(k+1)) % 2 = R_k (right didn't fire in phase k)
    #     So context at t-fire k+1: ((L_k+1)%2, (S_k+1)%2, R_k)
    #     This matches the context at t AFTER left fires in phase k. So at t-fire k+1,
    #     the non-mover context (from some step in phase k after left fired) equals the
    #     mover context at t-fire k+1!
    #
    #     WAIT. That would mean EC always holds! Let me check more carefully.

    # Let me think about this again. At t-fire k+1:
    #   mover context = (L_{k+1}, S_{k+1}, R_{k+1})

    # In phase k (between t-fire k and t-fire k+1), after left fires:
    #   non-mover context at t = ((L_k+1)%2, (S_k+1)%2, R_k)
    #   (t's value is (S_k+1)%2 = (s0+k+1)%2 since t doesn't fire in this interval)
    #   (left's value is (L_k+1)%2 since left fired once)
    #   (right's value is R_k since right didn't fire)

    # At t-fire k+1:
    #   L_{k+1} = (L_k + 1) % 2  (left fired in phase k)
    #   S_{k+1} = (s0 + k + 1) % 2
    #   R_{k+1} = R_k  (right didn't fire in phase k)

    # So the mover context at t-fire k+1 is ((L_k+1)%2, (s0+k+1)%2, R_k)

    # And the non-mover context at t (after left fires in phase k, before t fires at k+1)
    # is ((L_k+1)%2, (s0+k+1)%2, R_k)  -- WAIT, what's t's value at this point?
    # t's value is (s0 + k) % 2 + 1 = (s0 + k + 1) % 2? No.
    # After t-fire k, t's value is (s0 + k + 1) % 2 (it was S_k = (s0+k)%2, then fired).
    # t doesn't fire again until s_{k+1}. So in phase k, t's value is (s0+k+1)%2.
    # At t-fire k+1 (step s_{k+1}), t's value is STILL (s0+k+1)%2 (before firing).
    # So S_{k+1} should be (s0+k+1)%2 as context at mover step. Wait:

    # Hmm, S_k was defined as the value of c_t at step s_k. After t fires at s_k,
    # c_t becomes (S_k + 1) % 2. So at step s_{k+1} (before t fires), c_t = (S_k+1)%2
    # = (s0+k+1)%2. And S_{k+1} = c_t at step s_{k+1} = (s0+k+1)%2.

    # So: at t-fire k+1, context = (L_{k+1}, (s0+k+1)%2, R_{k+1})
    # Non-mover context after left fires in phase k = (L_{k+1}, (s0+k+1)%2, R_k)
    # And R_{k+1} = R_k.
    # So they're EQUAL!

    # This means: the non-mover context at t right before t-fire k+1
    # equals the mover context at t-fire k+1.

    # THAT IS ALWAYS EC. For any phase k, the non-mover observation of t
    # (at the step right before t fires) has the same (L,S,R) as the mover
    # observation at t-fire k+1.

    # Wait, is there a subtlety? The non-mover step is some step between s_k and s_{k+1}
    # where the mover is NOT t. And the context at t at that step equals the context
    # at t at step s_{k+1} where t IS the mover. So we have a mover step (s_{k+1}) and
    # a non-mover step (the step after left fires in phase k) with the same context
    # at processor t. That's entry conflict at t.

    # BUT WAIT: we need to be careful. The step "after left fires in phase k"
    # might be step s_{k+1} - 1 or even step s_{k+1} itself!
    # If left fires at step s_{k+1} - 1, then after left fires, the next step is s_{k+1}
    # which is when t fires. There's no "non-mover step" with that context at t
    # between left's fire and t's fire.

    # Actually, left fires at some step s_L in the interval (s_k, s_{k+1}).
    # After left fires at s_L, the context at t is the "post-left-fire" context.
    # Now, are there any steps between s_L and s_{k+1} where t is NOT the mover?
    # If other processors fire between s_L and s_{k+1}, those are non-mover steps
    # at t, and t's context might change if left or right fire again.
    # But we said right doesn't fire in phase k, and left fires exactly once.
    # So between s_L and s_{k+1}, only processors other than left(t), right(t), t fire.
    # These don't change t's context. So at every step from s_L+1 to s_{k+1}-1,
    # t's context is ((L_k+1)%2, (S_k+1)%2, R_k).
    # And at step s_{k+1}, t's context is the same, and t fires.

    # For EC, we need at least one step in [s_L+1, s_{k+1}-1] where mover ≠ t.
    # If s_L + 1 = s_{k+1}, there are no intermediate steps!
    # This happens when left fires at the step immediately before t fires.

    # Can this happen for ALL phases? That would mean left fires right before every
    # t-fire, and right fires right before every other t-fire where right is the neighbor.

    # Hmm, this is getting complicated. Let me think about it differently.

    # Actually, in a good cycle, steps are indexed by which processor fires.
    # Step s_L: left(t) fires. Step s_{k+1}: t fires. If s_L = s_{k+1} - 1,
    # then left fires at step s_{k+1} - 1 and t fires at step s_{k+1}.
    # Between them (exclusive), there are 0 steps. So there IS no step where
    # the context at t is ((L_k+1)%2, (S_k+1)%2, R_k) and mover ≠ t.

    # The mover context at step s_{k+1} - 1 (when left fires) is at proc left(t),
    # and the context at proc t is observed as a non-mover at step s_{k+1} - 1.
    # But at step s_{k+1} - 1, mover = left(t), and the context at t is:
    # (L_k, (S_k+1)%2, R_k)  -- BEFORE left fires at this step.
    # After left fires, the context at t becomes ((L_k+1)%2, (S_k+1)%2, R_k).
    # But the "observation" at step s_{k+1}-1 is the pre-fire config.

    # So at step s_{k+1}-1 (mover = left(t)):
    #   context at t = (L_k, (S_k+1)%2, R_k)  [pre-fire config]
    #   t is not the mover, so this is a non-mover observation of t

    # At step s_{k+1} (mover = t):
    #   context at t = ((L_k+1)%2, (S_k+1)%2, R_k)  [pre-fire config]

    # These are DIFFERENT (L_k vs (L_k+1)%2). So this particular pair doesn't give EC.

    # OK so the "right before t fires" step doesn't automatically give EC if left fires
    # there. What about the step AT which left fires?

    # Step s_L (mover = left(t)). Context at t:
    #   PRE-fire: (..., (S_k+1)%2, R_k) where left(t)'s value is whatever it was.
    #   But we're looking at context AT t, which is (c_{left(t)}, c_t, c_{right(t)}).
    #   At step s_L, before left fires: c_{left(t)} = L_k (hasn't fired yet in phase k).
    #   So context at t = (L_k, (S_k+1)%2, R_k).

    # Now: at which t-fire step is the context (L_k, (S_k+1)%2, R_k)?
    # At t-fire k: context = (L_k, S_k, R_k) = (L_k, (s0+k)%2, R_k)
    # At t-fire k+1: context = ((L_k+1)%2, (S_k+1)%2, R_{k+1})

    # The non-mover context (L_k, (S_k+1)%2, R_k):
    # S component is (S_k+1)%2 = (s0+k+1)%2
    # Mover context at t-fire k has S = (s0+k)%2 ≠ (s0+k+1)%2. Different.
    # Mover context at t-fire j has S = (s0+j)%2. This equals (s0+k+1)%2 iff j ≡ k+1 (mod 2).

    # So the non-mover context at step s_L (in phase k) could match a mover context at
    # t-fire j where j has the same parity as k+1.

    # At t-fire j (j ≡ k+1 mod 2): context = (L_j, (s0+j)%2, R_j).
    # For EC: need L_j = L_k and R_j = R_k.

    # This is getting complex. Let me just enumerate computationally.
    pass

def check_ec_domino_detailed(fc_t, verbose=False):
    """
    Enumerate all valid (fc_left, fc_right, phase_seq, s0, l0, r0) combos
    and check EC at t.

    EC at t means: exists a t-fire step and a non-t step with the same context at t.
    """
    assert fc_t >= 4 and fc_t % 2 == 0

    total = 0
    ec_count = 0
    no_ec_examples = []

    # fc_left + fc_right = fc_t, both even, both >= 2
    for fc_left in range(2, fc_t - 1, 2):
        fc_right = fc_t - fc_left
        if fc_right < 2 or fc_right % 2 != 0:
            continue

        # Enumerate phase sequences: binary strings of length fc_t
        # with exactly fc_left zeros (left-fire phases) and fc_right ones (right-fire phases)
        from itertools import combinations
        for right_phases in combinations(range(fc_t), fc_right):
            phase_seq = [0] * fc_t
            for j in right_phases:
                phase_seq[j] = 1

            for s0 in range(2):
                for l0 in range(2):
                    for r0 in range(2):
                        total += 1

                        # Compute contexts at t-fire steps
                        # and at non-mover steps where neighbors fire

                        mover_contexts = set()  # contexts when t fires
                        nonmover_contexts = set()  # contexts at t when t doesn't fire

                        # Track cumulative fires
                        cum_left = 0
                        cum_right = 0

                        for k in range(fc_t):
                            # At t-fire k:
                            L_k = (l0 + cum_left) % 2
                            S_k = (s0 + k) % 2
                            R_k = (r0 + cum_right) % 2
                            mover_contexts.add((L_k, S_k, R_k))

                            # In phase k (between t-fire k and t-fire k+1):
                            # t's value is (S_k + 1) % 2 (just fired)
                            t_val_in_phase = (S_k + 1) % 2

                            if phase_seq[k] == 0:
                                # Left fires once in this phase.
                                # Before left fires: context at t = (L_k, t_val_in_phase, R_k)
                                # This is a non-mover step (some proc fires, but specifically
                                # we know at the step WHEN left fires, the context at t is
                                # (L_k, t_val_in_phase, R_k) and mover = left(t) ≠ t).
                                nonmover_contexts.add((L_k, t_val_in_phase, R_k))

                                # After left fires: context at t = ((L_k+1)%2, t_val_in_phase, R_k)
                                # Steps between left-fire and next t-fire also have this context
                                # at t, and at those steps mover ≠ t (until t fires again).
                                # But we need at least one such step. If left fires at s_{k+1}-1,
                                # there might be no step between left-fire and t-fire.
                                # However, if OTHER procs fire between left-fire and t-fire,
                                # those are non-mover steps.
                                #
                                # For now, let's be CONSERVATIVE: only count the step when
                                # left/right fires as a guaranteed non-mover observation.
                                # That step definitely exists and mover ≠ t.

                                cum_left += 1
                            else:
                                # Right fires once in this phase.
                                # At the step when right fires:
                                # context at t = (L_k, t_val_in_phase, R_k) [before right fires]
                                # Wait: at the step when right fires, the pre-fire config has
                                # right's old value. But the context at t includes right(t)'s
                                # value, which is R_k (hasn't changed yet in this phase).
                                # Hmm, but right fires in this phase. At the step when right fires:
                                # context at t (pre-fire) = (L_k, t_val_in_phase, R_k)
                                # Wait, but left(t)'s value: left didn't fire in this phase, so
                                # it's still L_k? No. L_k was the value at t-fire k. In phase k,
                                # if phase_seq[k] = 1, left doesn't fire, so left's value stays L_k
                                # throughout phase k. So at the right-fire step:
                                # context at t = (L_k, t_val_in_phase, R_k)
                                nonmover_contexts.add((L_k, t_val_in_phase, R_k))

                                cum_right += 1

                        # Check EC: mover context ∩ nonmover context nonempty
                        ec = len(mover_contexts & nonmover_contexts) > 0

                        if ec:
                            ec_count += 1
                        else:
                            no_ec_examples.append({
                                'fc_t': fc_t, 'fc_left': fc_left, 'fc_right': fc_right,
                                'phase_seq': tuple(phase_seq),
                                's0': s0, 'l0': l0, 'r0': r0,
                                'mover_ctxs': mover_contexts,
                                'nonmover_ctxs': nonmover_contexts
                            })

    return total, ec_count, no_ec_examples

# But first: verify the constraint fc_left >= 2 and fc_right >= 2
# This comes from: left(t) and right(t) are binary, so fire count is even >= 2.
# But wait: could a binary proc have fc = 0? In a good cycle, every proc fires.
# So fc >= 1. But binary: fc must be even (returns to initial value).
# fc even and >= 1 means fc >= 2. ✓

# And fc_t = fc_left + fc_right >= 4.
# But fc_t must also be even (t is binary): fc_t >= 4 is even. ✓

print("=" * 70)
print("DOMINO ARGUMENT: Entry Conflict for Consecutive Binary NormalForm")
print("=" * 70)
print()
print("Constraint: fc(left t) + fc(right t) = fc(t), all even, all >= 2")
print("So fc(t) >= 4.")
print()

for fc_t in [4, 6, 8, 10]:
    total, ec_count, no_ec = check_ec_domino_detailed(fc_t)
    print(f"fc(t) = {fc_t}: {total} cases, EC in {ec_count}/{total}", end="")
    if no_ec:
        print(f"  *** {len(no_ec)} FAILURES ***")
        for ex in no_ec[:3]:
            print(f"  No EC: fc_L={ex['fc_left']}, fc_R={ex['fc_right']}, "
                  f"phases={ex['phase_seq']}, s0={ex['s0']}, l0={ex['l0']}, r0={ex['r0']}")
            print(f"    Mover ctxs:    {sorted(ex['mover_ctxs'])}")
            print(f"    Nonmover ctxs: {sorted(ex['nonmover_ctxs'])}")
    else:
        print("  ✓ ALL EC")

print()
print("=" * 70)
print("KEY INSIGHT CHECK")
print("=" * 70)
print()
print("At the step when the neighbor fires in phase k,")
print("the non-mover context at t is (L_k, (S_k+1)%2, R_k).")
print("The mover context at t-fire j is (L_j, (s0+j)%2, R_j).")
print()
print("For EC: need L_j = L_k, (s0+j)%2 = (s0+k+1)%2, R_j = R_k.")
print("The S-match requires j ≡ k+1 (mod 2), i.e., j and k have different parity.")
print()

# More refined analysis: track which specific context matches
print("=" * 70)
print("DETAILED ANALYSIS: How EC arises")
print("=" * 70)

def analyze_ec_mechanism(fc_t=4):
    """Show the specific mechanism for fc_t = 4."""
    from itertools import combinations

    fc_left = 2
    fc_right = 2

    for right_phases in combinations(range(fc_t), fc_right):
        phase_seq = [0] * fc_t
        for j in right_phases:
            phase_seq[j] = 1

        s0, l0, r0 = 0, 0, 0

        mover_data = []
        nonmover_data = []

        cum_left = 0
        cum_right = 0

        for k in range(fc_t):
            L_k = (l0 + cum_left) % 2
            S_k = (s0 + k) % 2
            R_k = (r0 + cum_right) % 2
            mover_data.append((k, (L_k, S_k, R_k)))

            t_val = (S_k + 1) % 2
            nonmover_data.append((k, (L_k, t_val, R_k), 'L' if phase_seq[k]==0 else 'R'))

            if phase_seq[k] == 0:
                cum_left += 1
            else:
                cum_right += 1

        mover_set = {ctx for _, ctx in mover_data}
        nonmover_set = {ctx for _, ctx, _ in nonmover_data}
        overlap = mover_set & nonmover_set

        print(f"\nPhase seq = {phase_seq}")
        for k, ctx in mover_data:
            flag = " *EC*" if ctx in nonmover_set else ""
            print(f"  t-fire {k}: mover ctx = {ctx}{flag}")
        for k, ctx, side in nonmover_data:
            flag = " *EC*" if ctx in mover_set else ""
            print(f"  phase {k} ({side}): nonmover ctx = {ctx}{flag}")
        if not overlap:
            print(f"  *** NO EC ***")

print("\nfc(t) = 4, fc_left = 2, fc_right = 2, s0=l0=r0=0:")
analyze_ec_mechanism(4)
