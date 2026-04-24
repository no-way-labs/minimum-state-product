#!/usr/bin/env python3
"""Check hno_safe for KNOWN valid systems from the paper.

The M_5 = 96 witness has ms = (2,2,2,3,4), product = 96.
Does its good cycle have a safe processor?

Also check: what does the proof ACTUALLY need? The sorry's hypotheses
include hno_safe. But the callers might provide it from specific
conditions (zero winding, etc.) that are stronger.
"""
import sys
sys.path.insert(0, './claude')

# First, let's understand the call chain.
# binary_ring_impossibility is called from:
# 1. both_binary_neighbors_false (normal form phase)
# 2. no_firing_both_binary_neighbors_false (no pivot fires)
# Both go through subThreshold_binary_core_false.
#
# subThreshold_binary_core_false is called from:
# A. consecutiveBinary_globalMin_residual_false (zero winding, consecutive)
# B. gapDecisive_false (non-consecutive, any winding)
# C. sweep_sub_threshold_false (sweep, non-consecutive, isolated)
# D. oddWinding_nonUniform_sub_threshold_false (odd winding, non-consecutive, isolated)
#
# For paths A,B: these come from large_arc_zeroWinding_direct (zero winding + CW > 0 + no safe proc)
# The "no safe proc" condition IS hno_safe. It comes from the CALLER.
#
# For path C,D: hno_safe comes from non-zero winding (sweep/odd winding) via
# no_safeProcessor_of_nonZeroWinding. So for sweep/odd winding: hno_safe is
# DERIVED from non-zero winding. Any non-zero-winding cycle has no safe proc.
#
# For the zero-winding case: hno_safe is GIVEN as hypothesis to
# large_arc_zeroWinding_ec. It comes from subThreshold_obstruction:
#   by_cases hsafe : ∃ q, safe q
#   · safe proc → small_arc_contradicts_convergence → False
#   · no safe proc → large_arc_zeroWinding_ec (with hno_safe = hsafe)
#
# So the flow is:
# subThreshold_obstruction:
#   zero winding:
#     CW = 0 → all_stay_contradicts_convergence
#     safe proc exists → small_arc_contradicts_convergence
#     no safe proc, CW > 0 → large_arc_zeroWinding_ec [hits sorry]
#   non-zero winding:
#     → nonZeroWinding_shadow [uses sweep/odd-winding paths]
#     sweep: consecutive → handled, non-consecutive isolated → [hits sorry]
#     odd-winding: same pattern
#
# KEY INSIGHT: The sorry is ONLY reached when:
# 1. Zero winding + no safe proc + CW > 0 (the "large arc" case)
# 2. Non-zero winding + isolated firings (through sweep/odd-winding)
#
# For case 2: "isolated" means binary_isolated_firings_or_ec returned the
# "isolated" variant. What does "isolated" mean exactly?

# Let me check: what does binary_isolated_firings_or_ec give?
# It's a trichotomy: EC ∨ permanent ∨ isolated.
# EC → False (handled)
# Permanent → totalDisplacement = 0, contradicts non-zero winding (handled)
# Isolated → the proc has "isolated firings" meaning it doesn't fire
#           at consecutive steps (moverAt(k)=p → moverAt(k+1)≠p).
#
# For the isolated case: subThreshold_binary_core_false is called.
# This goes through both_binary_neighbors_false (if pivot) or
# no_firing_both_binary_neighbors_false (if no pivot).
#
# both_binary_neighbors_false extracts a TernaryPhase and checks mechanism.
# If mechanism fires → EC → False. If normal form → binary_ring_impossibility (sorry).
#
# So the sorry is reached ONLY when:
# - exists_ternaryPhase returns a phase where no mechanism fires
# - OR no pivot exists (no proc with both binary neighbors fires)
#
# Computationally: the mechanism ALWAYS fires (at least for the phases
# returned by exists_ternaryPhase). So the sorry might be dead code.
#
# But proving it's dead code requires showing: for ANY valid system
# satisfying the hypotheses, exists_ternaryPhase returns a phase where
# the mechanism fires.

# Let me try to understand what makes mechanisms fire.
# BothEven: J even, K even. This happens when left and right fire even
#   times in the phase. Since the full cycle has even fire counts (binary),
#   and the phase is a portion: the parity depends on the split.
#
# ToggleFR-L: J ≥ 2, K = 0. Right doesn't fire in the phase.
# ToggleFR-R: J = 0, K ≥ 2. Left doesn't fire in the phase.
#
# Normal form: at least one of J, K odd, and neither is 0 with the other ≥ 2.
# So: (J odd, K ≥ 1) or (J ≥ 1, K odd) or both odd.
# And: J ≥ 2 → K ≥ 1; K ≥ 2 → J ≥ 1.

# For normal form with J ≤ 1, K ≤ 1: (0,1), (1,0), or (1,1).
# These only occur at phase_len = 1 (confirmed computationally).
# Phase_len = 1 means t fires at consecutive-ish steps (gap of 1).

# For normal form with J ≥ 2 or K ≥ 2: e.g., (2,1), (1,2), (3,1), etc.
# These require phase_len ≥ 3.
# Computationally: NEVER occur.

# WHY don't they occur? Here's my hypothesis:
#
# In a good cycle, the mover sequence is deterministic. At each step,
# the unique privileged proc fires. The mover sequence depends on the
# transition functions.
#
# For a proc t with both binary neighbors: when t fires at step s,
# the transition function determines the new value of t. Then the
# unique privileged proc at config s+1 is determined.
#
# The key constraint: in a sub-threshold system with convergence,
# the transition functions must support self-stabilization from all
# initial states. This severely constrains what mover sequences are
# possible.
#
# But proving this constraint forces mechanisms to fire is a deep
# structural claim about self-stabilizing systems.

# BOTTOM LINE:
# The sorry is computationally dead code. But proving it requires either:
# 1. Showing the mechanism always fires (structural claim about transition functions)
# 2. Showing the hypothesis set is contradictory (no valid cycle exists)
# Both are deep mathematical claims.

print("=== ANALYSIS COMPLETE ===")
print()
print("The sorry binary_ring_impossibility is called from two paths:")
print("  1. Normal-form phase (mechanism doesn't fire)")
print("  2. No-pivot (no proc with both binary neighbors fires)")
print()
print("Both are computationally dead code (0 occurrences in millions of tests).")
print()
print("The fundamental challenge: proving that the mechanism ALWAYS fires")
print("for phases extracted by exists_ternaryPhase requires reasoning about")
print("the global cycle structure (fire count parity, mover sequence constraints)")
print("that goes beyond the local phase analysis.")
print()
print("DRAGONS found:")
print("  1. Circular dependency: both_binary_neighbors_false ↔ palindromic_phase_ec")
print("     (SLAIN: restructured definition order)")
print("  2. Normal form at phase_len=1: hno_safe prevents it but proof is global")
print("     (MAPPED: computationally confirmed, proof requires cycle-level reasoning)")
print("  3. No-pivot case: every both-binary-neighbor proc has fc=0")
print("     (MAPPED: contradicted by hno_safe computationally)")
print()
print("MIRES found:")
print("  1. Random search never finds cycles with hno_safe + ≥3 binary")
print("     (the hypothesis space is extremely constrained)")
print("  2. The known valid systems (M_5=96, M_9=8748) might not have")
print("     the sorry's exact hypothesis combo (they have safe procs)")
print("  3. Parity counting alone doesn't give contradictions")
print("     (|A|+|C| even, |A|+|B| even is satisfiable)")
