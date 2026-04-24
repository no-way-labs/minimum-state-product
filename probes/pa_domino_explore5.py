#!/usr/bin/env python3
"""
PA Domino Exploration 5: Understand the actual sorry branch precisely.

The sorry is in consec_isolated_false. After the branch falls through:
1. hn : n ≥ 9
2. 3 consecutive binary: i, right(i), right²(i)
3. t = right(i) has fc(t) ≥ 2
4. t fires in isolated fashion (never consecutive)
5. Some mover is outside the binary triple
6. Parity check failed (odd parity at SOME neighbor in min firing gap)
7. Phase extracted for t
8. Phase dispatch failed (the specific phase doesn't satisfy dispatch conditions)

The key question: what GLOBAL conclusion can we draw?

Actually, wait. The sorry needs to prove False. The whole structure is:
- Under ¬hasEntryConflict (from the surrounding proof structure)
- Under subThreshold
- Under isSweep
- With 3 consecutive binary

Does `converges sys gc` participate? Let me check.

Actually, re-reading the context: the sorry is inside `consec_isolated_false`
which has `hconv : converges sys gc`. And `hno_safe`. But NOT `hsweep` directly.

Hmm, but `consec_isolated_false` is only called from `sweep_false` where
`hsweep` gives `isSweep`. The key is: consec_isolated_false doesn't take
hsweep as input. It only gets the consequences that were derived from hsweep
before the call (like fc ≥ 2).

Let me look at what SWEEP actually gives us beyond fc ≥ 2 for the sorry.
The sorry has available:
- All the hypotheses of consec_isolated_false
- The derived variables: hbL, hbR, mg, hgap2, ¬hparity, phase, ¬hmech

The key: with n ≥ 9 and 3 consecutive binary and sub-threshold product,
we need to derive False. The Lean proof infrastructure provides various
lemmas about phases and entry conflict.

Instead of the domino argument at t, let me think about what's ACTUALLY true.

The whole lower bound proof shows: no valid system exists with sub-threshold
product. The SWEEP case shows: no sweep good cycle exists. The CONSECUTIVE
case shows: if 3 consecutive binary, no sweep good cycle exists.

The computational verification shows EC at 100% — meaning every sweep good
cycle with 3 consecutive binary sub-threshold DOES have entry conflict.

So the sorry needs to close False. The proof route is: derive contradiction
from the hypothesis set. The key tool is entry conflict at SOME processor.

But wait — the proof structure has ¬hasEntryConflict as a hypothesis?
Let me check. Looking at the outer structure: sweep_false proves False.
It uses entryConflict_impossible which converts hasEntryConflict → False.
So the proof doesn't assume ¬hasEntryConflict; instead, when a branch
produces hasEntryConflict, it closes with entryConflict_impossible.

The sorry branch: hmech fails, so phase_dispatch_ec can't fire.
The comment says "routing from binary isolated-odd to ternary normalForm EC".

So the plan was: find a TERNARY proc sandwiched between two binary,
extract phases at that ternary proc, show all phases are normalForm,
and use normalForm_gives_ec.

But we showed normalForm_gives_ec is disproved as standalone.

Alternative: the sorry could be closed by any argument that produces False
from the hypotheses. It doesn't need to go through normalForm.

Let me think about what makes this case impossible.
"""

# Let me reconsider the problem from scratch.
# 3 consecutive binary at {i, t, rr} where t = right(i), rr = right²(i).
# sub-threshold product < 4·3^(n-2).
# With ≥3 binary, all binary have m=2.
# The remaining n-3 processors are ternary (m=3) or higher.
# Sub-threshold: product < 4·3^(n-2) = 2² · 3^(n-2).
# With 3 binary (each m=2) and n-3 others:
#   product = 8 · prod(others) < 4·3^(n-2)
#   prod(others) < 3^(n-2)/2
# But others are all ≥ 3, so prod(others) ≥ 3^(n-3).
# Need 3^(n-3) ≤ prod(others) < 3^(n-2)/2.
# For n ≥ 9: 3^(n-3) < 3^(n-2)/2 iff 1 < 3/2 ✓.
# So some others are exactly 3 (ternary), all at most 4 (else product too large).

# Actually: the exact constraint is 8 · prod(m_j for j not binary) < 4 · 3^(n-2).
# prod(m_j for non-binary j) < 3^(n-2)/2.
# With n-3 non-binary, each ≥ 3:
# If all are 3: prod = 3^(n-3). Need 3^(n-3) < 3^(n-2)/2 iff 2 < 3. ✓
# So the generic case is all non-binary are ternary.
# If one is 4: 4·3^(n-4) < 3^(n-2)/2 iff 4/3 < 3/2 iff 8 < 9. ✓ (barely)
# If two are 4: 16·3^(n-5) < 3^(n-2)/2 iff 16/9 < 3/2 iff 32 < 27. ✗
# So at most one non-binary can be 4, rest are 3.

# Key structural fact: with 3 consecutive binary and sub-threshold,
# we have either:
# (a) all non-binary are ternary (product = 8 · 3^(n-3))
# (b) one non-binary is quaternary, rest ternary (product = 8 · 4 · 3^(n-4) = 32 · 3^(n-4))

# In the sweep case with isolated binary firings, the cycle structure is:
# Sweep means |total displacement| ≥ 2n. Binary procs fire ≥ 2 times.
# Ternary procs fire ≥ 3 times (since m=3, fc must be multiple of 3).
# Actually wait: fc must be positive but doesn't need to be a multiple of m.
# In a good cycle, fc(p) is a multiple of m_p (since the proc returns to its
# initial state). For binary: fc(p) is even, ≥ 2.
# For ternary: fc(p) is a multiple of 3, ≥ 3.

# In a sweep: fc(p) ≥ 2 for all p (from sweep_fireCount_ge2).
# For binary: fc ≥ 2 and even → fc = 2 or 4 or 6...
# For ternary: fc ≥ 3 (multiple of 3) → fc = 3 or 6 or 9...

# Cycle length L = sum of all fc(p).
# Minimum L with 3 binary fc=2 and (n-3) ternary fc=3:
# L = 3*2 + (n-3)*3 = 6 + 3n - 9 = 3n - 3.

# For n=9: L ≥ 24. With one quaternary: same (quaternary fc multiple of 4, ≥ 4).

# Now: the parity check at t. The min firing gap of t has at least gapSize ≥ 2
# steps (from isolated). In that gap, left(t)=i fires J times, right(t)=rr fires K times.

# Parity check: same parity of i-fires at gap endpoints? Same for rr-fires?
# If same parity at both → EC (from even parity lemma).
# If different at one → odd parity → phase extraction succeeds.

# The sorry is in the branch where parity check fails (odd at some neighbor)
# AND phase dispatch fails.

# Instead of the NormalForm route, let me think about a counting/pigeonhole argument.

# Actually, I think the key insight might be simpler. Let me reconsider.

# In a SWEEP cycle with 3 consecutive binary:
# The cycle visits processors in ring order. With 3 consecutive binary at {i, t, rr},
# the sweep structure constrains how these binary procs interact.

# For a CW sweep: ..., i-1, i, t, rr, rr+1, ...
# For a CCW sweep: ..., rr+1, rr, t, i, i-1, ...

# In a CW pass through {i, t, rr}: i fires, then t fires, then rr fires.
# Context at t when t fires (CW): left=i just fired, right=rr hasn't fired yet.
# In a CCW pass: rr fires, then t fires, then i fires.
# Context at t when t fires (CCW): right=rr just fired, left=i hasn't fired yet.

# For EC at t in a sweep: we need the same context at t at a mover and non-mover step.
# As shown by the parity obstruction: the S-component (t's own value) always
# distinguishes mover from non-mover.

# But in a SWEEP specifically: the non-mover observations at t are:
# 1. When some far-away proc fires: context at t hasn't changed since last neighbor fire.
# 2. When i fires (CW pass): context at t = (val_before_i_fires, t_val, rr_val).
#    But "val_before_i_fires" is i's value BEFORE i fires. After i fires, i's value changes.
#    And then t fires immediately after (in CW). So at the step when t fires,
#    i has already fired: context = (i_new_val, t_val, rr_val).
# 3. When rr fires (CW pass): this happens AFTER t fires in CW.
#    So rr fires with t already having a new value.

# Hmm, this is getting into the weeds. Let me write code that simulates
# actual sweep cycles and finds where EC comes from.

from itertools import product as iproduct
from collections import Counter
import random

def build_sweep_cycles(n, ms, max_count=10000):
    """Build sweep cycles by constructing CW+CCW passes."""
    # A simple sweep: CW pass (0,1,...,n-1) then CCW pass (n-2,n-3,...,1)
    # This gives each proc exactly 2 fires (once CW, once CCW) except
    # proc 0 and n-1 which fire once each. Not quite right.
    #
    # Actually for a zero-winding cycle to be a sweep with fc ≥ 2 for all:
    # Need CW pass(es) + CCW pass(es) giving each proc ≥ 2 fires.
    #
    # Standard sweep: CW_full + CCW_full = 0,1,...,n-1,n-2,...,0
    # fc(0) = 2 (start + end), fc(n-1) = 2 (end of CW, start of CCW)
    # fc(others) = 2 (once CW, once CCW).
    # Length = n + (n-1) - 1 = 2n - 2? Let me count:
    # CW: 0,1,...,n-1 → n steps
    # CCW from n-1: n-2,n-3,...,0 → n-1 steps (n-1 already counted)
    # Total: n + n - 1 = 2n - 1 steps, but proc n-1 fires once in CW, and proc 0 fires
    # once at start and once at end. Not standard.

    # A clean sweep: 0,1,...,n-1,n-2,...,1 (bounce, length 2n-2)
    # fc(0) = 1, fc(n-1) = 1, fc(others) = 2.
    # But fc=1 for binary gives odd → not a valid cycle return.
    # So this doesn't work for binary procs at endpoints.

    # For a valid cycle with binary at {i, t, rr}:
    # Need fc(p) multiple of m_p for all p.
    # Binary: fc even ≥ 2. Ternary: fc multiple of 3 ≥ 3.

    # Let me just enumerate directly.
    pass

# Let me try a different approach: use the verifier infrastructure.
# The key computational check: enumerate at n=9 and find EC.

# Actually, let me re-examine the problem statement.
# It says "100% computationally verified across 1.4M+ test cases at n=5,9."
# But my exploration 4 found ZERO normalForm residual cycles at n=5.
# This means either:
# (a) The normalForm residual is vacuously true at n=5 (no cycles satisfy it)
# (b) My enumeration is incomplete

# If (a): the sorry needs to prove False, but the hypothesis set is vacuously
# inconsistent! The phase dispatch might always succeed, making ¬hmech unsatisfiable.

# Let me check: does every sweep cycle with 3 consecutive binary, isolated t,
# odd parity, have a phase satisfying dispatch?

print("="*70)
print("CHECKING: Is the sorry branch VACUOUS?")
print("="*70)
print()
print("If the phase dispatch ALWAYS succeeds for cycles meeting the")
print("sorry's hypotheses, then ¬hmech is unsatisfiable and the sorry")
print("is trivially true (no instantiation reaches it).")
print()
print("But Lean doesn't know this — it needs a proof that closes False.")
print("If the branch is reachable, we need a real argument.")
print("If unreachable, we need to prove the dispatch always succeeds.")
print()

# Let me check at n=5 and n=7 whether dispatch always succeeds.

def check_dispatch_coverage(n, ms, binary_triple):
    """Check if phase_dispatch_ec always covers the odd-parity case."""
    i_pos, t_pos, rr_pos = binary_triple

    start = tuple(0 for _ in range(n))
    results = []

    def dfs(word, fc, config):
        if len(results) >= 5000: return
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
            if len(results) >= 5000: return
            word.append(nxt)
            nf = list(fc); nf[nxt] += 1
            nc = list(config); nc[nxt] = (nc[nxt]+1) % ms[nxt]
            dfs(word, nf, tuple(nc))
            word.pop()

    for p in range(n):
        if len(results) >= 5000: break
        first = list(start); first[p] = (first[p]+1) % ms[p]
        dfs([p], [1 if j==p else 0 for j in range(n)], tuple(first))

    # Filter: zero-winding
    def winding(word):
        w = 0
        for idx in range(len(word)):
            d = (word[(idx+1)%len(word)] - word[idx]) % n
            if d == 1: w += 1
            elif d == n-1: w -= 1
        return w

    zw = [w for w in results if winding(w) == 0]

    isolated_odd_parity = 0
    dispatch_fails = 0

    for word in zw:
        ell = len(word)
        fc = Counter(word)
        if fc[t_pos] < 2: continue

        # Check isolated at t
        t_steps = [s for s in range(ell) if word[s] == t_pos]
        isolated = True
        for s in t_steps:
            if word[(s+1) % ell] == t_pos or word[(s-1) % ell] == t_pos:
                isolated = False
                break
        if not isolated: continue

        # Build configs for prefix fire count
        cfgs = [list(start)]
        for idx in range(ell):
            c = list(cfgs[-1])
            c[word[idx]] = (c[word[idx]] + 1) % ms[word[idx]]
            cfgs.append(c)

        # Prefix fire counts
        pfc = [[0]*n]
        for idx in range(ell):
            row = list(pfc[-1])
            row[word[idx]] += 1
            pfc.append(row)

        # Min firing gap
        if len(t_steps) < 2: continue

        # Find min gap
        min_gap = float('inf')
        min_a, min_b = None, None
        for idx in range(len(t_steps)):
            a = t_steps[idx]
            b = t_steps[(idx+1) % len(t_steps)]
            if b <= a: b += ell
            gap = b - a
            if gap < min_gap:
                min_gap = gap
                min_a, min_b = a, b % ell

        # Parity check
        a_idx = min_a
        b_idx = min_b

        pfc_i_a = pfc[a_idx + 1][i_pos]
        pfc_i_b = pfc[b_idx][i_pos] if b_idx > a_idx else pfc[b_idx + ell][i_pos]

        # Hmm, prefix fire count needs to handle wrap-around.
        # Let me just compute interval fire counts directly.
        if min_b > min_a:
            J_gap = sum(1 for s in range(min_a + 1, min_b) if word[s] == i_pos)
            K_gap = sum(1 for s in range(min_a + 1, min_b) if word[s] == rr_pos)
        else:
            J_gap = sum(1 for s in range(min_a + 1, min_b + ell) if word[s % ell] == i_pos)
            K_gap = sum(1 for s in range(min_a + 1, min_b + ell) if word[s % ell] == rr_pos)

        # Parity: odd means J_gap % 2 == 1 or K_gap % 2 == 1
        if J_gap % 2 == 0 and K_gap % 2 == 0:
            continue  # Even parity → handled by different branch

        isolated_odd_parity += 1

        # Phase dispatch check for ALL phases (not just min gap)
        all_dispatched = True
        for idx in range(len(t_steps)):
            a = t_steps[idx]
            b = t_steps[(idx+1) % len(t_steps)]
            if b <= a: b += ell
            J = sum(1 for s in range(a+1, b) if word[s % ell] == i_pos)
            K = sum(1 for s in range(a+1, b) if word[s % ell] == rr_pos)

            dispatched = (J % 2 == 0 and K % 2 == 0) or (J >= 2 and K == 0) or (J == 0 and K >= 2)
            if not dispatched:
                all_dispatched = False
                break

        if not all_dispatched:
            dispatch_fails += 1
            # Show the phases
            phases = []
            for idx in range(len(t_steps)):
                a = t_steps[idx]
                b = t_steps[(idx+1) % len(t_steps)]
                if b <= a: b += ell
                J = sum(1 for s in range(a+1, b) if word[s % ell] == i_pos)
                K = sum(1 for s in range(a+1, b) if word[s % ell] == rr_pos)
                phases.append((J, K))
            if dispatch_fails <= 5:
                print(f"  Dispatch fail: word len={ell}, fc_t={fc[t_pos]}, phases={phases}")

    return len(zw), isolated_odd_parity, dispatch_fails

# Test at n=5
n = 5
ms = [2, 2, 2, 3, 3]
binary_triple = (0, 1, 2)
print(f"n={n}, ms={ms}, binary={binary_triple}")
zw_count, iop, df = check_dispatch_coverage(n, ms, binary_triple)
print(f"  ZW cycles: {zw_count}, isolated+odd: {iop}, dispatch fails: {df}")

ms = [3, 2, 2, 2, 3]
binary_triple = (1, 2, 3)
print(f"\nn={n}, ms={ms}, binary={binary_triple}")
zw_count, iop, df = check_dispatch_coverage(n, ms, binary_triple)
print(f"  ZW cycles: {zw_count}, isolated+odd: {iop}, dispatch fails: {df}")

# n=7
n = 7
ms = [3, 3, 2, 2, 2, 3, 3]
binary_triple = (2, 3, 4)
print(f"\nn={n}, ms={ms}, binary={binary_triple}")
zw_count, iop, df = check_dispatch_coverage(n, ms, binary_triple)
print(f"  ZW cycles: {zw_count}, isolated+odd: {iop}, dispatch fails: {df}")
