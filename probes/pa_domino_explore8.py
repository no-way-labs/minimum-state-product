#!/usr/bin/env python3
"""
PA Domino Exploration 8: Alternative proof route via counting.

Key insight: the sorry needs `hasEntryConflict gc` (or any route to False).

Alternative route: Instead of analyzing phases at t, use a global
counting/pigeonhole argument.

Idea 1: Under sub-threshold product, the TOTAL number of contexts is bounded.
The cycle length L gives L mover observations and L non-mover observations.
If L is large enough relative to the number of distinct contexts at any proc,
EC is forced.

For proc p with context space = m_{left(p)} * m_p * m_{right(p)}:
- p has fc(p) mover observations and (L - fc(p)) non-mover observations.
- If fc(p) > context space, pigeonhole forces repeated mover context.
  Repeated mover context + the mover changes p's value → different output
  on same input. But that's a transition function contradiction only if
  the context appears in BOTH mover and non-mover roles.

Actually for EC at p: we need one context appearing as both mover and non-mover.
Pigeonhole: if fc(p) + (L - fc(p)) = L > context_space, guaranteed overlap
of SOME kind. But we need mover∩nonmover overlap specifically.

Total observations at p: L observations total (one per step).
fc(p) are mover, L - fc(p) are non-mover.
Context space: C_p = m_{left(p)} * m_p * m_{right(p)}.

If fc(p) > C_p OR (L - fc(p)) > C_p: repeated contexts of same type.
But we need cross-type overlap.

If fc(p) + (L - fc(p)) = L > 2*C_p: pigeonhole gives overlap.
But 2*C_p could be large.

Hmm, this is too coarse. Let me think about what the actual tight constraint is.

Actually there's a much simpler argument. Consider proc i (boundary binary).
Context at i: (c_{left(i)}, c_i, c_{right(i)}) = (c_ternary, c_binary, c_binary).
But wait — c_{right(i)} = c_t which is also binary.

Context space at i: m_{left(i)} * 2 * 2 = 4 * m_{left(i)}.
If left(i) is ternary: context space = 12.
If left(i) is binary: context space = 8.

With 3 consecutive binary, left(i) is NOT binary (else we'd have 4 consecutive).
Actually, with EXACTLY 3 consecutive binary at {i, t, rr}, left(i) could be
binary too (giving ≥4 consecutive binary). The hypothesis is ≥3, not exactly 3.

But with n ≥ 9 and sub-threshold product: we can have at most a few binary.
Actually we proved that with sub-threshold, there are exactly 3 binary
(or more but that leads to other contradictions). Let me not worry about this.

For the sorry branch: left(i) is ternary (or higher). Context space at i ≤ 12
(if left(i) ternary) or ≤ 16 (if quaternary).

The cycle length L ≥ 3n - 3 (with minimum fc for all procs).
For n = 9: L ≥ 24.

fc(i) = fc of a binary proc = 2k ≥ 2.
Non-mover observations at i: L - fc(i) ≥ 24 - 2k.

With context space 12: we need to show that among the fc(i) mover
and (L - fc(i)) non-mover observations, there's overlap.

fc(i) mover observations use ≤ 12 distinct contexts.
(L - fc(i)) non-mover observations use ≤ 12 distinct contexts.
If mover contexts and non-mover contexts partition the 12 contexts,
then we need fc(i) ≤ 12 and L - fc(i) ≤ 12, so L ≤ 24.

For n = 9: L ≥ 24. So if L > 24, we get EC at i!
But L could be exactly 24.

For n = 10: L ≥ 27 > 24 > 2*12. EC at i!
Hmm, this only works for n large enough.

Wait, the constraint is tighter. At binary proc i:
Mover observations: at each mover step, c_i changes (binary toggle).
So at mover step k (0-indexed), c_i = (init + k) % 2.
For even k: c_i = init. For odd k: c_i = (init+1)%2.

So mover contexts all have c_i = init (for even-indexed firings) or
c_i = (init+1)%2 (for odd-indexed). This means:
- Even-indexed mover contexts: (*, init, *) — at most C_p/2 = 6 distinct
- Odd-indexed mover contexts: (*, (init+1)%2, *) — at most 6 distinct

Similarly for non-mover observations: between firing k and k+1,
c_i = (init + k + 1) % 2 (just fired). So c_i is constant within each gap.

Total distinct mover contexts: ≤ 12 (but really only 6 per parity of k).
Actually no, the L and R values vary. So up to 12 distinct mover contexts.

Hmm, this counting argument isn't tight enough for small n.
Let me try a different approach.
"""

# Let me look at this from the Lean proof perspective.
# The sorry has very specific hypotheses. Maybe there's a simpler route
# that uses the parity information more directly.

# The parity failure gives: odd number of i-fires OR odd number of rr-fires
# in the min gap of t.

# What if we use the phase extraction at a DIFFERENT processor?
# Instead of extracting phases at t, extract at the boundary binary i.

# At i: between consecutive i-fires, t fires some number of times,
# and left(i) fires some number of times.
# i is binary, so fc(i) is even ≥ 2.
# For EC at i: if between consecutive i-fires, t doesn't fire (J=0),
# then in that gap, c_t is constant. The context at i starts and ends with
# the same c_t. Since c_i alternates (fires at both ends), the two
# contexts are (L, c_i_old, c_t) and (L', c_i_new, c_t) — different S component.
# But between i-fires, the non-mover context at i has c_i = (c_i_old + 1)%2 = c_i_new.
# Hmm, getting complicated again.

# DIFFERENT APPROACH: What if the proof doesn't need EC at all?
# What if we can derive False directly from the hypotheses?

# The hypotheses include:
# - converges sys gc
# - subThreshold sys.rs
# - hasGe3Binary sys.rs
# - threeConsecutiveBinary sys.rs i
# - gc.fireCount (right i) ≥ 2
# - isolated firings at right(i)
# - hno_safe (no safe proc)
# - hparity failure
# - hmech failure

# Maybe we can show that the hypothesis set is inconsistent
# WITHOUT finding EC? E.g., showing that the cycle structure
# directly contradicts subThreshold or convergence?

# Actually, let me look at what existing proved lemmas are available
# in PhaseExtractionBase that work on the sorry's hypothesis set.

# The sweep_consec_normalform_route.md lists many lemmas.
# The key one: `sparse_phase_sum_ge` gives fc(left t) + fc(right t) ≥ fc(t)
# under ¬EC and all-normalForm.

# But we don't have ¬EC as a hypothesis — the sorry needs to PRODUCE EC (or False).

# Wait, the proof structure in Sweep.lean uses `entryConflict_impossible gc ...`
# to convert EC to False. So the sorry branch implicitly assumes there's no
# other way to get False. But the sorry itself just needs False.

# What if we use `hconv : converges sys gc` together with some structural
# impossibility? E.g., the cycle is too short to be a converging cycle?
# Or the cycle has a specific structure that contradicts convergence?

# Actually, I think the cleanest route is:
# 1. Extract phases at the boundary binary proc i (not at t)
# 2. Use the ternary neighbor left(i) to get a richer context space
# 3. Apply phase-based EC arguments at i

# Or even simpler: use the existing `phase_dispatch_ec` at i instead of t.
# The sorry extracts a phase at t and tries dispatch at t. What if we
# extract at i and try dispatch at i?

# Let me check: does phase dispatch at i always succeed?

from itertools import combinations
from collections import Counter

def check_dispatch_at_boundary(n, ms, binary_triple, max_cycles=3000):
    """Check if phase dispatch at boundary binary i always succeeds."""
    i_pos, t_pos, rr_pos = binary_triple
    start = tuple(0 for _ in range(n))
    results = []

    def dfs(word, fc, config):
        if len(results) >= max_cycles: return
        if len(word) > 6*n: return
        if len(word) >= n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
                return
        remaining = 6*n - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining: return
        for nxt in range(n):
            if abs(nxt - word[-1]) % n not in [1, n-1]: continue
            if len(results) >= max_cycles: return
            word.append(nxt)
            nf = list(fc); nf[nxt] += 1
            nc = list(config); nc[nxt] = (nc[nxt]+1) % ms[nxt]
            dfs(word, nf, tuple(nc))
            word.pop()

    for p in range(n):
        if len(results) >= max_cycles: break
        first = list(start); first[p] = (first[p]+1) % ms[p]
        dfs([p], [1 if j==p else 0 for j in range(n)], tuple(first))

    def winding(w):
        wd = 0
        for idx in range(len(w)):
            d = (w[(idx+1)%len(w)] - w[idx]) % n
            if d == 1: wd += 1
            elif d == n-1: wd -= 1
        return wd

    zw = [w for w in results if winding(w) == 0]

    sorry_and_dispatched = 0
    sorry_and_not_dispatched = 0
    sorry_count = 0

    for word in zw:
        ell = len(word)
        fc = Counter(word)
        if fc[t_pos] < 2: continue

        t_steps = [s for s in range(ell) if word[s] == t_pos]
        isolated = all(word[(s+1)%ell] != t_pos and word[(s-1)%ell] != t_pos for s in t_steps)
        if not isolated: continue

        # Min gap parity
        min_gap = float('inf')
        min_idx = 0
        for idx in range(len(t_steps)):
            a = t_steps[idx]
            b = t_steps[(idx+1) % len(t_steps)]
            if b <= a: b += ell
            gap = b - a
            if gap < min_gap:
                min_gap = gap
                min_idx = idx

        a = t_steps[min_idx]
        b = t_steps[(min_idx+1) % len(t_steps)]
        if b <= a: b += ell
        J_gap = sum(1 for s in range(a+1, b) if word[s%ell] == i_pos)
        K_gap = sum(1 for s in range(a+1, b) if word[s%ell] == rr_pos)
        if J_gap % 2 == 0 and K_gap % 2 == 0:
            continue

        # Phase dispatch at t fails?
        J_mg, K_mg = J_gap, K_gap
        dispatched_at_t = (J_mg % 2 == 0 and K_mg % 2 == 0) or (J_mg >= 2 and K_mg == 0) or (J_mg == 0 and K_mg >= 2)
        if dispatched_at_t:
            continue

        sorry_count += 1

        # Now check phases at boundary proc i
        i_steps = [s for s in range(ell) if word[s] == i_pos]
        if len(i_steps) < 2:
            sorry_and_not_dispatched += 1
            continue

        li_pos = (i_pos - 1) % n  # left(i) — ternary

        # For each phase of i
        any_dispatched = False
        for idx in range(len(i_steps)):
            a = i_steps[idx]
            b = i_steps[(idx+1) % len(i_steps)]
            if b <= a: b += ell

            J = sum(1 for s in range(a+1, b) if word[s%ell] == li_pos)
            K = sum(1 for s in range(a+1, b) if word[s%ell] == t_pos)

            dispatched = (J % 2 == 0 and K % 2 == 0) or (J >= 2 and K == 0) or (J == 0 and K >= 2)
            if dispatched:
                any_dispatched = True
                break

        if any_dispatched:
            sorry_and_dispatched += 1
        else:
            sorry_and_not_dispatched += 1
            if sorry_and_not_dispatched <= 3:
                i_phases = []
                for idx in range(len(i_steps)):
                    a = i_steps[idx]
                    b = i_steps[(idx+1) % len(i_steps)]
                    if b <= a: b += ell
                    J = sum(1 for s in range(a+1, b) if word[s%ell] == li_pos)
                    K = sum(1 for s in range(a+1, b) if word[s%ell] == t_pos)
                    i_phases.append((J, K))
                print(f"    No dispatch at i: word len={ell}, i-phases={i_phases}")

    return sorry_count, sorry_and_dispatched, sorry_and_not_dispatched

print("="*70)
print("CHECK: Does phase dispatch at boundary i always succeed?")
print("="*70)

for n, ms, bt in [
    (5, [2,2,2,3,3], (0,1,2)),
    (5, [3,2,2,2,3], (1,2,3)),
    (7, [3,3,2,2,2,3,3], (2,3,4)),
]:
    print(f"\nn={n}, ms={ms}, binary={bt}")
    total, dispatched, not_dispatched = check_dispatch_at_boundary(n, ms, bt)
    print(f"  Sorry branch: {total}")
    print(f"  Dispatch at i succeeds: {dispatched}")
    print(f"  Dispatch at i fails: {not_dispatched}")
