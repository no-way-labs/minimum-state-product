"""
Investigation part 3: Two questions:
1. Can we bypass zw_provider_ec entirely? If the existing archive theorems
   (palindromic_phase_ec_residual) already cover this case, we don't need it.
2. What's the actual mechanism for EC under fc >= 3?

Key insight: zw_provider_ec has hypotheses:
  - hconv (converges), hno_safe, hsub, h3bin
These are EXACTLY the hypotheses that palindromic_phase_ec_residual needs!
And palindromic_phase_ec_residual doesn't care about winding or fc — it
works for ANY good cycle with these base hypotheses plus a TernaryPhase.

So the question is: can we always extract a TernaryPhase when fc >= 3?
A TernaryPhase at proc t requires:
  - t is ternary (m_t >= 3)
  - There exist steps a, s where t fires at both and fc(t) in [a,s) >= 2

Under fc >= 3 at some proc q: if q is ternary, directly use q.
If q is binary, then fc(q) >= 3 means q fires 3+ times with m_q = 2.

Actually, let's check: under sub-threshold + >=3 binary, does there ALWAYS
exist a ternary proc t with fc(t) >= 2 that has binary neighbors?

Better yet: the file comment says "find a binary proc b with fc=2" —
but that's not actually needed. The real question is whether we can
extract a TernaryPhase and route through palindromic_phase_ec_residual.

Let me check: under ZW + cw > 0 + fc >= 2 for all + some fc >= 3:
- Sum of fc = CL > 2n (since some fc > 2)
- At least 3 binary procs
- Some ternary procs exist (product < 4*3^(n-2) requires not all binary)

Can we always find a ternary proc t with binary neighbors and fc(t) >= 2?
Under fc >= 2 for all, EVERY ternary proc has fc >= 2.
Under >= 3 binary, can we always find a ternary t with a binary neighbor?

With >= 3 binary procs in a ring of n >= 9, there must be at least one
ternary proc adjacent to a binary proc (unless all binary are isolated
with ternary buffers, but even then the ternary buffer has binary neighbor).

Wait — actually palindromic_phase_ec_residual needs BOTH left(t) and right(t)
to be binary. That's the "sandwich" requirement. With >= 3 binary,
do we always have a "sandwiched" ternary?

Only if there exist 3 consecutive binary (then the middle one is binary,
but its neighbors are binary, not ternary...). Hmm, the sandwich is
ternary proc with binary on both sides.

With 3 consecutive binary at positions i, i+1, i+2:
- proc i+1 is binary with binary neighbors — NOT a ternary sandwich target
- But proc i-1 (if ternary) has left=proc i-2, right=proc i (binary)
  Only one binary neighbor.

Actually, palindromic_phase_ec_residual needs left(t) binary AND right(t) binary.
With only 3 binary out of n >= 9 procs, this requires the 3 binary to be
non-consecutive (so some ternary is between two of them).

Wait, that's not right either. Let's just check the cases:

Case 1: 3 consecutive binary at i, i+1, i+2.
  Then left(i)=i-1 (ternary), right(i+2)=i+3 (ternary).
  No ternary proc has binary on BOTH sides within this group.
  But proc i+3 has left=i+2 (binary), right=i+4 (ternary) — only one side.

  For a sandwich, we need B-T-B. With 3 consecutive binary, the remaining
  n-3 are all ternary, forming a block. No ternary in that block has
  binary on both sides UNLESS there are more binary elsewhere.

Hmm, this is getting complicated. Let me just check the Lean code to see
what approach is actually being used.

Actually, the key realization: the file already handles consecutive vs
non-consecutive binary at lines 311-316:
  - consecutive binary: palindromic EC (after establishing fc=2)
  - non-consecutive: ShadowOrbit

And zw_provider_ec is used BEFORE the case split — it's needed to
establish fc=2 in the first place.

So the question is: can we prove fc >= 3 → EC without palindromic_phase_ec_residual?

Alternative approach: fc >= 3 → CL > 2n → not all fc = 2 →
but we need to PROVE EC to get the contradiction.

Actually, let me re-read the proof structure carefully.
The key is entryConflict_impossible: hasEntryConflict gc → False.
So if we can show EC from ANY of our existing theorems, we're done.

The most general EC theorem we have: if we have hconv, hsub, h3bin, hno_safe,
we should be able to route through the same machinery used by OddWinding and Sweep.

Let me check: does the Lean codebase have a theorem like
"sub_threshold_has_entry_conflict" that works for ANY good cycle?
"""

print("Checking if there's a universal EC theorem in the codebase...")
print("(This is a code analysis question, not computational)")
print()
print("Key insight from reading ZeroWinding.lean:")
print("1. zw_provider_ec proves: ZW + cw>0 + fc>=2 + some fc>=3 → EC")
print("2. This is used by zeroWinding_no_fireCount_ge3 to get False")
print("3. Which is used by allFireCount_eq_2_of_zeroWinding to establish all fc=2")
print("4. Then palindromic_walk_step_pair (another sorry) handles the fc=2 case")
print()
print("QUESTION: Can zw_provider_ec be proved by routing through existing infrastructure?")
print()
print("The hypotheses available: hconv, hno_safe, hsub, h3bin")
print("These are the SAME hypotheses used by Sweep.lean and OddWinding.lean")
print("to prove their cases. Both of those use phase extraction → dispatch or residual.")
print()
print("The approach should work: under fc>=2 + some fc>=3, we can:")
print("1. Find any ternary proc t with fc(t) >= 2 (guaranteed since all fc >= 2)")
print("2. Extract TernaryPhase at t")
print("3. Route through phase_dispatch_ec or palindromic_phase_ec_residual")
print()
print("BUT: palindromic_phase_ec_residual needs left(t) and right(t) both binary.")
print("With only 3 binary procs in a ring of 9+, this might not be satisfiable.")
print()
print("HOWEVER: phase_dispatch_ec handles the case where (J,K) satisfy one of:")
print("  - Even J, Even K")
print("  - J >= 2, K = 0")
print("  - J = 0, K >= 2")
print("and does NOT require binary neighbors!")
print()
print("So the question reduces to: can we always find a ternary proc t where")
print("the phase dispatch conditions hold?")
