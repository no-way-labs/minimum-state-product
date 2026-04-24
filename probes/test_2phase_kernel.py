#!/usr/bin/env python3
"""Test: is the 2-phase normal-form configuration impossible
even WITHOUT convergence/sub-threshold?

Enumerate all possible 2-phase pivot configurations:
- t has binary left and right neighbors (m_L = m_R = 2)
- t fires exactly twice (at s₁ and s₂)
- Phase 1 [s₁+1, s₂) has J₁=1, K₁=1 (normal form (1,1))
- Phase 2 [s₂+1, s₁) has J₂=1, K₂=1
- Check if a valid good cycle can exist with these constraints

The context at t is (val_L, val_T, val_R) ∈ {0,1} × Fin(m_t) × {0,1}.
At each pivot fire: f_t(L, S, R) ≠ S (privileged).
At each nonmover step: f_t(L, S, R) = S (not privileged).

With (1,1) in each phase: left fires once and right fires once.
The mover sequence in phase 1 is: ..., left or right, ..., right or left, ..., (neighbor at s₂-1)
"""

def check_2phase_possible():
    """Check all possible 2-phase (1,1)/(1,1) configs for ternary t."""

    # t is ternary (m=3). Left and right are binary (m=2).
    # Context at t: (L, S, R) ∈ {0,1} × {0,1,2} × {0,1}
    #
    # Phase 1: t fires at s₂ with context (L₂, S, R₂).
    #   Between s₁+1 and s₂: left fires once (L flips), right fires once (R flips).
    #   Also other procs fire (don't affect L, S, R at t).
    #   At s₁+1 (after t fires at s₁): L = L₁', S = S₁' = f(L₁,S₁,R₁), R = R₁'
    #   After left fires: L flips. After right fires: R flips. Order doesn't matter for final values.
    #   At s₂: L₂ = 1-L₁', R₂ = 1-R₁', S₂ = S₁' (t doesn't fire in phase).
    #   f(L₂, S₂, R₂) ≠ S₂ (t fires at s₂).
    #
    # Phase 2: t fires at s₁ with context (L₁, S₁, R₁).
    #   At s₂+1: L = L₂' = L₂ (t firing doesn't change L), S = S₂' = f(L₂,S₂,R₂), R = R₂' = R₂
    #   Wait: t firing at s₂ changes S but not L, R. So L₂' = L₂, R₂' = R₂.
    #   After left fires: L flips. After right fires: R flips.
    #   At s₁: L₁ = 1-L₂, R₁ = 1-R₂, S₁ = S₂' = f(L₂,S₂,R₂).
    #   f(L₁, S₁, R₁) ≠ S₁ (t fires at s₁).
    #
    # Cycle closure: At s₁+1: S₁' = f(L₁,S₁,R₁). This must equal S₂ (= S at start of phase 1).
    #   S₂ = S₁' = f(L₁,S₁,R₁). Also S₁ = f(L₂,S₂,R₂).

    # Let's parameterize:
    # Choose L₁ ∈ {0,1}, R₁ ∈ {0,1}, S₁ ∈ {0,1,2}.
    # Then: L₂ = 1-L₁, R₂ = 1-R₁.
    # S₂ = f(L₁, S₁, R₁) (from phase 2 → phase 1 transition).
    # S₁ = f(L₂, S₂, R₂) (from phase 1 → phase 2 transition).
    # Constraint: f(L₁, S₁, R₁) ≠ S₁ (privileged at s₁).
    # Constraint: f(L₂, S₂, R₂) ≠ S₂ (privileged at s₂).
    #
    # Also need: at nonmover steps in the phase, t is NOT privileged.
    # In phase 1: at every step k ∈ [s₁+1, s₂), the context at t is some (L_k, S₁', R_k).
    # S₁' = f(L₁, S₁, R₁) = S₂. At these steps: f(L_k, S₂, R_k) = S₂.
    # The (L_k, R_k) values depend on whether left/right have fired yet.

    # For the SIMPLEST case: phase has exactly 2 steps (left fires, right fires).
    # Step 1: say left fires. Context at t before: (L₁', S₂, R₁').
    #   Where L₁' = L₁ (L hasn't flipped yet? Wait, s₁+1 is after t fires.
    #   At s₁+1: L = L₁ (t firing doesn't change L), R = R₁, S = f(L₁,S₁,R₁) = S₂.
    #   Hmm wait, at config s₁+1: this is the state AFTER t fires at s₁.
    #   t fires: S changes from S₁ to f(L₁,S₁,R₁). L and R unchanged.
    #   So at s₁+1: L = L₁, S = S₂ = f(L₁,S₁,R₁), R = R₁.

    # Step s₁+1: some proc fires (not t). Say left fires.
    #   f_t not privileged: f(L₁, S₂, R₁) = S₂.
    #   After left fires: L flips to 1-L₁.

    # Step s₁+2: say right fires.
    #   At this config: L = 1-L₁, S = S₂, R = R₁.
    #   f_t not privileged: f(1-L₁, S₂, R₁) = S₂.
    #   After right fires: R flips to 1-R₁.

    # Config s₂: L = 1-L₁ = L₂, S = S₂, R = 1-R₁ = R₂. t IS privileged: f(L₂, S₂, R₂) ≠ S₂.
    # But we need f(L₂, S₂, R₂) = S₁ (from the cycle closure).

    # So constraints on f_t:
    # f(L₁, S₁, R₁) = S₂ ≠ S₁  (t fires at s₁)
    # f(L₂, S₂, R₂) = S₁ ≠ S₂  (t fires at s₂)
    # f(L₁, S₂, R₁) = S₂        (t not privileged at s₁+1, before left fires)
    # f(1-L₁, S₂, R₁) = S₂      (t not privileged after left fires, before right fires)
    # ... and in phase 2:
    # f(L₂, S₁, R₂) = S₁        (t not privileged at s₂+1)
    # f(1-L₂, S₁, R₂) = S₁      (after left fires in phase 2)
    # Note: 1-L₂ = L₁ and 1-R₂ = R₁

    count_valid = 0
    count_total = 0

    for m_t in [2, 3]:  # t binary or ternary
        for L1 in range(2):
            for R1 in range(2):
                for S1 in range(m_t):
                    L2 = 1 - L1
                    R2 = 1 - R1

                    # Try all possible S2 ≠ S1
                    for S2 in range(m_t):
                        if S2 == S1:
                            continue
                        count_total += 1

                        # Check: f(L1, S1, R1) = S2 (fires to S2)
                        # Check: f(L2, S2, R2) = S1 (fires to S1)
                        # Check: f(L1, S2, R1) = S2 (not privileged in phase 1 before left fires)
                        # Check: f(L2, S2, R1) = S2 (not privileged in phase 1 after left fires)
                        #   Wait: after left fires, L = 1-L1 = L2. Before right fires, R = R1.
                        #   So context: (L2, S2, R1). f(L2, S2, R1) = S2.
                        # Check: f(L2, S1, R2) = S1 (not privileged in phase 2 before left fires)
                        # Check: f(L1, S1, R2) = S1 (not privileged in phase 2 after left fires)
                        #   After left fires in phase 2: L = 1-L2 = L1. Before right fires: R = R2.
                        #   Context: (L1, S1, R2). f(L1, S1, R2) = S1.

                        # The transition function constraints:
                        # f(L1, S1, R1) = S2
                        # f(L2, S2, R2) = S1
                        # f(L1, S2, R1) = S2
                        # f(L2, S2, R1) = S2
                        # f(L2, S1, R2) = S1
                        # f(L1, S1, R2) = S1

                        # Check consistency:
                        # From f(L1,S1,R1)=S2 and f(L1,S1,R2)=S1:
                        #   If R1 = R2: S2 = S1. Contradiction (S2 ≠ S1).
                        #   So R1 ≠ R2. Since binary: R2 = 1-R1. OK (always true).

                        # From f(L1,S2,R1)=S2 and f(L2,S2,R1)=S2:
                        #   f doesn't depend on L when S=S2, R=R1. Both map to S2.

                        # From f(L2,S2,R2)=S1 and f(L2,S2,R1)=S2:
                        #   If R1 = R2: S1 = S2. Contradiction.
                        #   So R1 ≠ R2. f(L2,S2,R1)=S2, f(L2,S2,R2)=S1. Different R, different output. OK.

                        # From f(L2,S1,R2)=S1 and f(L1,S1,R2)=S1:
                        #   f doesn't depend on L when S=S1, R=R2. Both map to S1.

                        # From f(L1,S1,R1)=S2 and f(L1,S1,R2)=S1:
                        #   f(L1,S1,*) depends on R: R1→S2, R2→S1. OK.

                        # All constraints are CONSISTENT! No contradiction!

                        # Can we construct a valid f?
                        f = {}
                        f[(L1,S1,R1)] = S2
                        f[(L2,S2,R2)] = S1
                        f[(L1,S2,R1)] = S2
                        f[(L2,S2,R1)] = S2
                        f[(L2,S1,R2)] = S1
                        f[(L1,S1,R2)] = S1

                        # Check for conflicts in f
                        conflict = False
                        for key in f:
                            # Check if same key maps to different values
                            pass  # No conflicts possible since we check each key once

                        # Check: are there any ENTRY CONFLICTS?
                        # EC = same (L,S,R) at mover and nonmover steps.
                        # Mover contexts: (L1,S1,R1) and (L2,S2,R2).
                        # Nonmover contexts: (L1,S2,R1), (L2,S2,R1), (L2,S1,R2), (L1,S1,R2).

                        mover_contexts = {(L1,S1,R1), (L2,S2,R2)}
                        nonmover_contexts = {(L1,S2,R1), (L2,S2,R1), (L2,S1,R2), (L1,S1,R2)}

                        ec = mover_contexts & nonmover_contexts
                        if not ec:
                            count_valid += 1
                            if count_valid <= 5:
                                print(f"VALID (no EC): m_t={m_t} L1={L1} R1={R1} S1={S1} S2={S2}")
                                print(f"  Mover: {mover_contexts}")
                                print(f"  Nonmover: {nonmover_contexts}")
                                print(f"  f assignments: {f}")
                        else:
                            pass  # EC exists — this config is killed

    print(f"\nTotal configs: {count_total}")
    print(f"Valid (no EC from phase analysis): {count_valid}")
    print(f"Killed by EC: {count_total - count_valid}")

    if count_valid > 0:
        print("\nSOME configs survive! The 2-phase kernel alone does NOT give contradiction.")
        print("Need additional constraints (convergence, sub-threshold, hno_safe).")
    else:
        print("\nALL configs killed! The 2-phase kernel IS contradictory!")
        print("native_decide WILL work!")

check_2phase_possible()
