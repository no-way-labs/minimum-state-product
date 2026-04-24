"""Analyze the exact local window around a seam step.
For each seam position p in {k-1, k, k+1}:
  - The seam step changes c(p) to TMidVal(c(p-1), c(p), c(p+1))
  - This changes fb at positions p-1 and p
  - Position p+1 might fire next (non-seam deep step) copying LEFT = c(p)_modified
  - This cascades: each subsequent position copies LEFT

For the fc comparison: what is the NET fc change from removing the seam step
AND all its cascading effects (which would also be different in the SA path)?

The key insight: the seam step + cascade creates copy pairs at the modified
positions. The ORIGINAL config has noDeepCopyPair (all adjacent pairs distinct,
fb = 1). The modified config has copy pairs (fb = 0) at the seam boundaries.

So the fc at the modified seam positions is LOWER than the original.
"""

# For a no-copy period-3 triple at positions (p-1, p, p+1):
# Values are all distinct: {a, b, c} with a != b != c.
# Seam step at p: output = TMidVal(a, b, c) = a (left copy in no-copy regime).
# After: (a, a, c). fb(p-1, p) = fb(a, a) = 0. fb(p, p+1) = fb(a, c).

# Original: fb(p-1, p) = fb(a, b) = 1. fb(p, p+1) = fb(b, c) = 1.
# Modified: fb(p-1, p) = fb(a, a) = 0. fb(p, p+1) = fb(a, c).

# fb(a, c): if a != c then 1 else 0. In period-3 cycling: a, b, c all distinct → a != c → fb = 1.
# So: original fb = 1 + 1 = 2. Modified fb = 0 + 1 = 1. Δfb = -1 at the seam window.

# But the seam step ALSO affects the cascade at p+1:
# If p+1 fires (non-seam deep step): copies LEFT = a (modified) instead of b (original).
# After cascade at p+1: (a, a, a, ...) creating more copy pairs.

# The LOCAL WINDOW analysis:
# Positions: p-1, p, p+1, p+2 (the 4-site window)
# Original values: a, b, c, d (all adjacent distinct in no-copy)
# After seam step at p: a, a, c, d (c(p) = a)
# After cascade at p+1 (if it fires): a, a, a, d (c(p+1) = a)
# After cascade at p+2 (if it fires): a, a, a, a (c(p+2) = a)
# ...until the cascade stops (hits a position where output = input, i.e., LEFT = SELF).

# fb values in the ORIGINAL window (no-copy, all adjacent distinct):
# fb(p-2, p-1) = 1 (but outside window), fb(p-1, p) = 1, fb(p, p+1) = 1, fb(p+1, p+2) = 1
# Total fb in window [p-1, p, p+1]: 3

# fb values AFTER seam step (just the seam, no cascade):
# fb(p-1, p) = 0, fb(p, p+1) = fb(a, c), fb(p+1, p+2) = 1
# If a != c (period-3): total = 0 + 1 + 1 = 2. Loss = 1.

# fb values AFTER seam + cascade at p+1:
# c(p+1) = a. fb(p, p+1) = fb(a, a) = 0. fb(p+1, p+2) = fb(a, d).
# Total = 0 + 0 + fb(a, d). If a != d: 1. If a = d: 0.
# In period-3: d = a (since the pattern cycles with period 3, and p+2 = p-1 mod 3...
# Actually in period 3: values at p-1, p, p+1, p+2 are a, b, c, a. So d = a.
# Then fb(a, d) = fb(a, a) = 0. Total = 0. Loss = 3.

# Hmm wait, let me check: in period-3, consecutive values are a, b, c, a, b, c, ...
# So p-1 = a, p = b, p+1 = c, p+2 = a. d = a.

# After seam at p: (a, a, c, a). fb = (0, fb(a,c)=1, fb(c,a)=1) = 2. Total loss = 1.
# After cascade at p+1: c(p+1) = a. (a, a, a, a). fb = (0, 0, 0) = 0. Total loss = 3.
# But cascade at p+1 costs Δfc ≤ -1 (from noCopy at p+1: c ≠ a and c ≠ a? After seam:
# c(p) = a, c(p+1) = c, c(p+2) = a. At position p+1: LEFT = a, SELF = c, RIGHT = a.
# LEFT ≠ SELF (a ≠ c). SELF ≠ RIGHT (c ≠ a). No copy → Δfc ≤ -1 ✓.
# After firing at p+1: c(p+1) = a. Now at position p+2: LEFT = a, SELF = a.
# LEFT = SELF → not privileged (output might = input). So cascade STOPS.

# So the cascade is just ONE step: p+1. Then p+2 has LEFT = SELF = a, not privileged.

# Total fc effect of seam step + cascade:
# seam at p: Δfc ≤ -1 (from noCopy_tpMid_fc_strict)
# cascade at p+1: Δfc ≤ -1 (from noCopy_tpMid_fc_strict)
# Total: Δfc ≤ -2

# In the SA path (no seam): the cascade at p+1 fires with LEFT = b (original), SELF = c, RIGHT = a.
# LEFT ≠ SELF (b ≠ c). SELF ≠ RIGHT (c ≠ a). Copies LEFT = b.
# After: c(p+1) = b. fb(p, p+1) = fb(b, b) = 0. fb(p+1, p+2) = fb(b, a).
# In period-3: b ≠ a → fb = 1.
# SA path at p+1: Δfc ≤ -1. fc lost = 1 at p+1.

# So: TP path loses ≥ 2 fc (seam + cascade). SA path loses ≥ 1 fc (just cascade).
# TP path loses 1 MORE fc than SA path.

# But the cascade OUTPUT differs: TP has c(p+1) = a, SA has c(p+1) = b.
# Subsequent steps at p+2 see different LEFT. But p+2 in the TP path: LEFT = a, SELF = a → not privileged.
# p+2 in the SA path: LEFT = b, SELF = a. If b ≠ a (period-3: yes) → privileged. Copies LEFT = b.
# After: c(p+2) = b. fb(p+1, p+2) = fb(b, b) = 0. fb(p+2, p+3) = fb(b, c).
# In period-3: b ≠ c → fb = 1. This cascade continues in the SA path but NOT in the TP path.

# So the SA path has a LONGER cascade (because b ≠ a at p+2) while the TP path cascade stopped
# (because a = a at p+2). But each cascade step in the SA path costs Δfc ≤ -1.

# The key: the TP path has FEWER cascade steps (cascade stopped earlier) but paid the seam cost.
# The SA path has MORE cascade steps but no seam cost.

# Net comparison: TP fc = original - seam_cost - TP_cascade_cost.
# SA fc = original - SA_cascade_cost.
# SA_cascade_cost ≥ TP_cascade_cost (SA cascade is longer or equal).
# And seam_cost ≥ 1.
# But SA_cascade_cost - TP_cascade_cost ≤ seam_cost? If the SA cascade is much longer...

# Wait, in the TP path: after seam at p and cascade at p+1, the cascade STOPPED (p+2 not privileged).
# The TP cascade cost = 1 (just p+1). Plus seam cost = 1. Total = 2.
# In the SA path: cascade at p+1 (cost 1), then p+2 (if b ≠ a, cost 1), then p+3 (if b ≠ c mod 3...)
# The SA cascade continues as long as LEFT ≠ SELF at each position.

# But each SA cascade step costs ≥ 1 fc. And the TP path paid 2 fc (seam + 1 cascade step).
# The SA path might pay more than 2 fc if the cascade is long (> 2 steps).
# In that case: SA fc < TP fc! The SA path is WORSE!

# Hmm, this contradicts the claim that max_SA ≥ PhiFull.

# But wait: the SA path doesn't HAVE to fire at p+1. It can choose NOT to fire there.
# SA-reachable = reachable via non-seam steps. The SA max includes choosing which non-seam steps to take.
# So max_SA includes the choice of NOT firing at p+1 (leaving c(p+1) unchanged).

# If the SA path doesn't fire at p+1: fc stays at the original level for the window.
# No cascade, no fc loss. fc = original.

# And: max_SA ≥ fc(c) = original. So max_SA ≥ original.
# And: fc(TP endpoint) = original - seam_cost - cascade_cost ≤ original - 2.
# So max_SA ≥ original ≥ fc(TP endpoint) + 2. ✓

# AH, this is the key insight! The SA path can choose NOT to fire the deep non-seam steps
# that are affected by the seam cascade. The SA max includes the EMPTY path (fc = fc(c)).
# And fc(c) ≥ any TP endpoint's fc (since every TP step is either seam or deep, costing ≥ 1 fc).

# Wait, that would mean PhiFull(c) = fc(c) for no-copy configs. But boundary steps can INCREASE fc!

# Hmm, boundary steps are at positions 0, 1, 2, 3, n-3, n-2, n-1. These are NOT deep.
# They use TBot, TLow, TMid (at 2,3), THigh (at n-2), TTop (at n-1).
# Their Δfc can be positive (increase fc).

# So PhiFull(c) > fc(c) is possible via boundary steps. And boundary steps are SA.
# So max_SA(c) ≥ PhiFull_boundary(c) ≥ PhiFull(c)? No, PhiFull includes seam steps too.

# Let me reconsider. PhiFull(c) = max over ALL TP-reachable. This includes:
# - boundary-only paths: all SA. max_SA includes these.
# - paths with non-seam deep steps: SA. max_SA includes these.
# - paths with seam steps: NOT SA. max_SA excludes these.

# For paths with seam steps: every seam step costs ≥ 1 fc. But subsequent boundary steps
# (which are SA) can recover fc. The question: does the boundary recovery + seam cost
# give higher fc than boundary recovery alone?

# Answer: NO! Because the boundary recovery is the same in both paths (boundary inputs unchanged
# for k ≤ n-6). The seam step only costs fc (≥ 1). So the TP path with seam has:
# fc = fc(c) + boundary_gain - seam_cost - deep_cascade_cost
# ≤ fc(c) + boundary_gain - 1 (at least 1 from seam)
# ≤ max_SA(c) - 1 (since max_SA includes the boundary-gain-only path)
# < max_SA(c). ✓

# BUT: the "deep_cascade_cost" in the TP path might be LESS than the cascade in the SA path
# (as I showed above: TP cascade is shorter). So:
# TP: fc = fc(c) + boundary_gain - 1 (seam) - 1 (TP cascade) = fc(c) + boundary_gain - 2
# SA (with cascade): fc = fc(c) + boundary_gain - SA_cascade_cost

# If SA_cascade_cost ≥ 2: SA fc ≤ fc(c) + boundary_gain - 2. Same as TP.
# If SA_cascade_cost = 0 (don't fire cascade): SA fc = fc(c) + boundary_gain. Better than TP.

# So max_SA ≥ fc(c) + boundary_gain ≥ fc(c) + boundary_gain - 2 = TP fc. ✓

# The key: max_SA includes the path with boundary steps ONLY (no deep steps at all).
# This path has: fc = fc(c) + boundary_gain.
# The TP path with seam has: fc ≤ fc(c) + boundary_gain - 1.
# So max_SA ≥ TP fc. ✓

# But wait: the "boundary_gain" might not be the same in both paths!
# The boundary gain depends on which boundary steps fire and their fc changes.
# If boundary steps fire at positions 0-3, n-3,...,n-1: their outputs depend on
# boundary values. For k ≤ n-6: boundary values are unchanged by seam steps.
# So the same boundary steps produce the same outputs.

# BUT: if the TP path fires boundary steps AFTER deep/seam steps that changed deep values,
# the deep values MIGHT affect boundary step outputs at position 3 (reads c(4)).
# For k ≤ n-6 and k = 5: c(4) is in the seam. After seam step: c(4) changes.
# Position 3's step reads c(4). But TMid copies LEFT = c(2), independent of c(4). ✓
# So output at position 3 is the same. ✓

# For position n-3: reads c(n-4). For k ≤ n-6: c(n-4) NOT in seam. Unchanged. ✓

# So boundary gain is IDENTICAL in both paths. ✓

# CONCLUSION:
# max_SA ≥ fc(c) + max_boundary_gain (from boundary-only path)
# TP fc ≤ fc(c) + max_boundary_gain - seam_cost ≤ max_SA - 1
# Therefore PhiFull ≤ max_SA. ✓

# THE PROOF: max_SA ≥ "boundary-only PhiFull" ≥ PhiFull - 1 ≥ PhiFull.
# Wait, I need max_SA ≥ PhiFull, not max_SA ≥ PhiFull - 1.

# Actually: any TP path with a seam step has fc ≤ fc(c) + boundary_gain - 1.
# Any TP path WITHOUT a seam step is SA. max_SA includes it.
# So: PhiFull = max(max over SA paths, max over non-SA paths)
#            = max(max_SA, max over paths with ≥ 1 seam step)
#            ≤ max(max_SA, fc(c) + boundary_gain - 1)
# And: max_SA ≥ fc(c) + boundary_gain (from boundary-only SA path).
# So: max over non-SA ≤ fc(c) + boundary_gain - 1 < max_SA.
# Therefore: PhiFull = max_SA. ✓

# But "boundary_gain" is the max over all boundary step sequences. The TP path
# might use a DIFFERENT boundary step sequence than the SA path. But all boundary
# step sequences are SA (boundary positions are not in the seam). So max_SA includes
# all possible boundary step sequences.

# And: the boundary step outputs don't depend on whether seam steps happened
# (for k ≤ n-6). So the same boundary step sequence produces the same fc contribution
# regardless of seam steps. Therefore: any boundary gain achievable in a TP path
# is also achievable in an SA path. ✓

print("CONCLUSION: The proof is that for k ≤ n-6:")
print("1. All TP paths decompose as: boundary steps + deep steps (seam and non-seam)")
print("2. Boundary step outputs are independent of seam step effects")
print("3. Every deep step (seam or non-seam) costs Δfc ≤ -1")
print("4. SA paths include all boundary steps and non-seam deep steps")
print("5. The boundary-only SA path achieves fc ≥ any TP path with seam steps")
print("   because the seam step costs ≥ 1 fc and the boundary gain is the same")
print()
print("The proof does NOT need path replay. It just needs:")
print("a. PhiFull = max over TP-reachable = max(max_SA, max_non_SA)")
print("b. max_non_SA ≤ max_SA - 1 (seam costs at least 1)")
print("c. Therefore PhiFull = max_SA. QED")
print()
print("But (b) requires: every non-SA path has fc ≤ max_SA - 1.")
print("This follows from: any non-SA path's fc = fc(c) + Σ boundary Δfc - Σ deep Δfc")
print("And: the corresponding boundary-only SA path has fc = fc(c) + Σ boundary Δfc")
print("Which is ≥ the non-SA path's fc + 1 (from the seam cost)")
