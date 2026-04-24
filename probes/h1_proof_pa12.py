#!/usr/bin/env python3
"""
THE PROOF: Entry conflict from (1,1) phases.

Strategy: Focus on the (1,1) phase ITSELF to derive EC.

In a (1,1) phase at sandwiched ternary t (m_t=3, m_{t-1}=m_{t+1}=2):
- t fires at beginning of next phase, say at step k.
- In the phase: bL fires once (at step u), bR fires once (at step v).
- t is non-mover in the phase.

Context at t during the phase: (c[bL], c[t], c[bR])
- c[t] stays fixed throughout the phase (t doesn't fire).
- c[bL] changes when bL fires at step u.
- c[bR] changes when bR fires at step v.

So in the phase, the context at t evolves:
  Before any neighbor fires: (a, x, b) where a=c[bL], x=c[t], b=c[bR]
  After bL fires (if bL fires first): (1-a, x, b)  [binary flip]
  After bR fires: eventually (a', x, b') where a' and b' reflect the firings.

Since bL fires exactly once: c[bL] changes from a to 1-a (mod 2).
Since bR fires exactly once: c[bR] changes from b to 1-b (mod 2).

Key: the ORDER of bL and bR firings matters.
If bL fires before bR: phase contexts at t are
  (..., x, ...) where first (a, x, b), then after bL: (1-a, x, b),
  then after bR: (1-a, x, 1-b)
If bR fires before bL: phase contexts at t are
  first (a, x, b), then after bR: (a, x, 1-b),
  then after bL: (1-a, x, 1-b)

Mover context at t (when t fires STARTING this phase): (a0, x0, b0)
where a0, x0, b0 are values at the step when t fires.

Non-mover contexts at t during the phase: the configs at each step in the phase.

For EC at t: need mover ctx = some non-mover ctx.

Actually, t fires at the START of the phase (or rather, the phase is between
two consecutive t-firings). Let me re-clarify:

Phase = interval between t firing at step k1 and t firing at step k2.
Steps in the phase: k1+1, k1+2, ..., k2-1.
At step k1: t fires (mover). Context at t before firing: (a, x, b).
After t fires: c[t] changes from x to (x+1) mod 3.
Steps k1+1 to k2-1: t is non-mover.
  c[t] stays at (x+1) mod 3 throughout.

At step k2: t fires again (mover). Context at t before firing: (a', (x+1)%3, b').

The non-mover contexts at t during the phase have middle value (x+1) mod 3.
The mover context at step k1 has middle value x.
The mover context at step k2 has middle value (x+1) mod 3.

So: mover at k2 has same middle value as all non-movers in this phase!
EC at t requires: (a', (x+1)%3, b') matches some non-mover context in this phase.

The non-mover contexts are: the contexts at t at steps k1+1, ..., k2-1.
These have middle value (x+1)%3 and L,R values determined by which neighbors fire.

Let me trace this precisely.
"""
from collections import Counter

def build_configs(ms, n, word):
    L = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(L):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:L])) != L:
        return None
    return configs[:L]

def enumerate_good_cycles(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
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

def is_wrap_adjacent(word, n):
    return abs(word[-1] - word[0]) % n in (1, n-1)

n = 5
ms = [2, 3, 2, 3, 2]  # Case B, alternating
sandwiched = [1, 3]  # both ternary are sandwiched

words = enumerate_good_cycles(ms, n, 20)

print("="*70)
print("(1,1) PHASE TRACE at sandwiched ternary")
print("="*70)

sample = 0
for word in words:
    configs = build_configs(ms, n, word)
    if configs is None:
        continue
    if not is_wrap_adjacent(word, n):
        continue

    L = len(word)
    t = 1  # sandwiched ternary
    bL, bR = 0, 2

    # Find phases
    t_steps = [s for s in range(L) if word[s] == t]
    fc_t = len(t_steps)

    for idx in range(fc_t):
        k1 = t_steps[idx]
        k2 = t_steps[(idx+1) % fc_t]

        # Phase steps
        phase_steps = []
        s = (k1+1) % L
        while s != k2:
            phase_steps.append(s)
            s = (s+1) % L

        J = sum(1 for s in phase_steps if word[s] == bL)
        K = sum(1 for s in phase_steps if word[s] == bR)

        if J != 1 or K != 1:
            continue

        # Mover context at k1 (start of this phase)
        mctx_k1 = (configs[k1][bL], configs[k1][t], configs[k1][bR])
        # Mover context at k2 (end of this phase / start of next)
        mctx_k2 = (configs[k2][bL], configs[k2][t], configs[k2][bR])

        # Non-mover contexts in phase
        nm_ctxs = []
        for s in phase_steps:
            ctx = (configs[s][bL], configs[s][t], configs[s][bR])
            nm_ctxs.append((s, word[s], ctx))

        # Check EC: does mctx_k2 match any nm_ctx?
        # mctx_k2 has middle = mctx_k1[1] + 1 mod 3 (after t fires at k1)
        # nm_ctxs all have middle = mctx_k1[1] + 1 mod 3

        x = mctx_k1[1]  # t's value before first fire
        x_plus = (x + 1) % 3  # t's value during phase

        ec_in_phase = mctx_k2 in [c for (_, _, c) in nm_ctxs]

        if sample < 10:
            print(f"\nword={word}, t={t}, phase {idx}: k1={k1}->k2={k2}")
            print(f"  mctx@k1 = {mctx_k1} (t fires: {x}->{x_plus})")
            print(f"  mctx@k2 = {mctx_k2} (middle should be {x_plus}: {'OK' if mctx_k2[1]==x_plus else 'WRONG'})")
            print(f"  nm_ctxs: (all should have middle={x_plus})")
            for (s, mover, ctx) in nm_ctxs:
                match = " <-- MATCHES mctx@k2" if ctx == mctx_k2 else ""
                print(f"    step {s}: mover={mover}, ctx@t={ctx}{match}")
            print(f"  EC in this phase: {ec_in_phase}")

            # Detailed analysis
            a0, b0 = mctx_k1[0], mctx_k1[2]  # neighbor values before phase
            a_end, b_end = mctx_k2[0], mctx_k2[2]  # neighbor values at end of phase
            print(f"  Neighbor evolution: bL: {a0}->...->{'?'}, bR: {b0}->...->{'?'}")
            print(f"  After phase: bL={a_end}, bR={b_end}")
            print(f"  bL fires once: should flip {a0}->{1-a0}")
            print(f"  bR fires once: should flip {b0}->{1-b0}")
            print(f"  Expected end: ({1-a0}, {x_plus}, {1-b0})")
            print(f"  Actual end:   ({a_end}, {x_plus}, {b_end})")

            # Other steps between k2 and k1 (non-mover at t) with middle value x_plus?
            # No -- after k2, t fires again, changing middle to (x_plus+1)%3.
            # Non-movers after k2 have middle (x_plus+1)%3 = (x+2)%3.
            # Non-movers in the PREVIOUS phase (before k1) have middle x (before t fired).
            # Wait no: the PREVIOUS phase has t's value at whatever it was before k1.

            sample += 1

# Now: the KEY insight.
# In a (1,1) phase:
# - Start: t fires at k1, context (a, x, b). After: c[t] = x+1.
# - bL fires once, bR fires once in some order.
# - End: t fires at k2, context (a', x+1, b').
# - Since bL fires once: a' = 1-a if no other proc changes bL.
#   But bL's only neighbors are bL-1 and bL+1=t.
#   Wait: bL has left neighbor bL-1 and right neighbor t.
#   When t fires at k1: that DOES change c[t], which is bR's LEFT neighbor...
#   No: bL = t-1, so bL's neighbors are (t-2, bL, t).
#   t fires at k1: changes c[t], but bL's left-right context is (c[t-2], c[t-1], c[t]).
#   c[t] changing affects bL's context but not bL's VALUE.
#   bL's VALUE only changes when bL fires.
#   Since bL fires once in the phase: c[bL] changes from a to (a+1)%2 = 1-a.
#   Similarly c[bR] changes from b to 1-b.

# But between the phase, other procs might fire too (not just bL and bR).
# J=1, K=1 means bL fires once and bR fires once.
# Other procs (not t, bL, bR) might fire too.
# Their firings don't affect c[bL] or c[bR] (those only change when bL or bR fire).
# But they DO affect the config at other positions.

# So: a' = 1-a, b' = 1-b. Confirmed.
print("\n" + "="*70)
print("VERIFICATION: end-of-phase context")
print("="*70)

mismatch = 0
total_phases = 0
for word in words:
    configs = build_configs(ms, n, word)
    if configs is None:
        continue
    if not is_wrap_adjacent(word, n):
        continue

    L = len(word)
    for t in sandwiched:
        bL, bR = (t-1)%n, (t+1)%n
        t_steps = [s for s in range(L) if word[s] == t]
        for idx in range(len(t_steps)):
            k1 = t_steps[idx]
            k2 = t_steps[(idx+1) % len(t_steps)]
            phase_steps = []
            s = (k1+1)%L
            while s != k2:
                phase_steps.append(s)
                s = (s+1)%L
            J = sum(1 for s in phase_steps if word[s] == bL)
            K = sum(1 for s in phase_steps if word[s] == bR)
            if J != 1 or K != 1:
                continue
            total_phases += 1

            a = configs[k1][bL]
            b = configs[k1][bR]
            x = configs[k1][t]
            x_plus = (x+1) % 3

            a_end = configs[k2][bL]
            b_end = configs[k2][bR]
            x_end = configs[k2][t]

            if a_end != 1-a or b_end != 1-b or x_end != x_plus:
                mismatch += 1
                print(f"MISMATCH: word={word}, t={t}, k1={k1}, k2={k2}")
                print(f"  start: ({a},{x},{b}), end: ({a_end},{x_end},{b_end}), expected: ({1-a},{x_plus},{1-b})")

print(f"Total (1,1) phases: {total_phases}, mismatches: {mismatch}")

# So: mover context at k2 = (1-a, x+1, 1-b).
# Non-mover contexts in phase: all have middle x+1.
# The 3 distinct L-R pairs possible in the phase are:
#   Before any fire: (a, x+1, b)
#   After bL only: (1-a, x+1, b)
#   After bR only: (a, x+1, 1-b)
#   After both: (1-a, x+1, 1-b)
# But only 3 of these 4 can appear in the phase (depends on order of bL, bR firings).

# If bL fires first (at step u), then bR (at step v), u < v:
#   Steps before u: (a, x+1, b) -- non-mover
#   Steps [u+1, v-1]: (1-a, x+1, b) -- non-mover
#   Steps after v: (1-a, x+1, 1-b) -- non-mover
# So non-mover LR pairs: {(a,b), (1-a,b), (1-a,1-b)} (3 pairs)
# Mover at k2: (1-a, x+1, 1-b) -- this IS in the non-mover set!
# The last non-mover context (1-a, x+1, 1-b) appears AFTER both fire.

# If bR fires first (at step v), then bL (at step u), v < u:
#   Steps before v: (a, x+1, b)
#   Steps [v+1, u-1]: (a, x+1, 1-b)
#   Steps after u: (1-a, x+1, 1-b)
# Non-mover LR pairs: {(a,b), (a,1-b), (1-a,1-b)} (3 pairs)
# Mover at k2: (1-a, x+1, 1-b) -- again in the set!

# In BOTH cases: the mover context at k2 = (1-a, x+1, 1-b) appears as non-mover!
# Because AFTER both bL and bR have fired (and before t fires again at k2),
# there must be at least one step where t is non-mover with context (1-a, x+1, 1-b).

# This IS the EC proof! The only question is: are there steps between the LAST
# binary firing and k2?

print("\n" + "="*70)
print("CRITICAL CHECK: steps between last binary fire and k2")
print("="*70)

# Need: at least one step s in (max(u,v), k2) where word[s] != t
# and the context at t is (1-a, x+1, 1-b).

no_gap = 0
for word in words:
    configs = build_configs(ms, n, word)
    if configs is None:
        continue
    if not is_wrap_adjacent(word, n):
        continue

    L = len(word)
    for t in sandwiched:
        bL, bR = (t-1)%n, (t+1)%n
        t_steps = [s for s in range(L) if word[s] == t]
        for idx in range(len(t_steps)):
            k1 = t_steps[idx]
            k2 = t_steps[(idx+1) % len(t_steps)]
            phase_steps = []
            s = (k1+1)%L
            while s != k2:
                phase_steps.append(s)
                s = (s+1)%L
            J = sum(1 for s in phase_steps if word[s] == bL)
            K = sum(1 for s in phase_steps if word[s] == bR)
            if J != 1 or K != 1:
                continue

            # Find last binary fire in phase
            last_binary = max(s for s in phase_steps if word[s] in (bL, bR))
            # But need to handle cyclic order
            # Actually: phase_steps is already in order. Last binary fire:
            binary_steps = [s for s in phase_steps if word[s] in (bL, bR)]
            last_bin = binary_steps[-1]

            # Steps between last_bin and k2
            gap_steps = []
            s = (last_bin + 1) % L
            while s != k2:
                gap_steps.append(s)
                s = (s+1)%L

            if len(gap_steps) == 0:
                no_gap += 1
                # In this case, the last binary fires right before t fires.
                # The context at t at step k2 (mover) is (1-a, x+1, 1-b).
                # Is there any non-mover step with this context?
                # Yes: the last binary fire step itself!
                # At step last_bin: mover is bL or bR, not t.
                # After the binary fires, the context at t becomes (1-a, x+1, 1-b).
                # But that's the config at step LAST_BIN+1, which is k2.
                # At step k2, t IS the mover. So the config AT step k2 is the mover context.
                # We need non-mover with same context.
                # At step last_bin: the config is BEFORE the binary fires.
                # If last_bin fires bR (the second to fire):
                #   config at last_bin: (1-a, x+1, b) [if bL fired earlier]
                #   or (a, x+1, b) [if bR fires first, but that contradicts last_bin being bR and last]
                # Hmm, this needs more care.

                # Actually: if the binary fires right before k2 (no gap), then:
                # At step last_bin: context at t is (a'', x+1, b'') [before binary fires]
                # After last_bin fires: one of a'', b'' flips.
                # Result: (1-a, x+1, 1-b) = config at k2 = mover context at t.
                # But at step last_bin, t is NON-MOVER with context (a'', x+1, b'').
                # That's not (1-a, x+1, 1-b). So no match at that step.

                # BUT: we also need to check earlier steps!
                # After the FIRST binary fires, there are steps where t is non-mover.
                # At those steps, one neighbor has flipped, the other hasn't.
                # Context at t: (1-a, x+1, b) or (a, x+1, 1-b) depending on order.
                # The mover context at k2 is (1-a, x+1, 1-b) -- different from both!

                # So if NO gap: EC might NOT occur at t from this phase.
                pass

            # But maybe EC occurs from a DIFFERENT phase or at a DIFFERENT proc.

print(f"Phases with no gap between last binary fire and k2: {no_gap}")
print(f"Total (1,1) phases: {total_phases}")

# Check: the case where last binary fires right before t.
# In this case, the step sequence at the end of the phase is:
# ..., last_bin fires, k2: t fires.
# Since word[last_bin] and word[k2] must be ring-adjacent: yes, bL and bR are both neighbors of t.

# The context (1-a, x+1, 1-b) only appears at step k2 (as mover).
# It does NOT appear as non-mover in THIS phase.
# But it might appear as non-mover in ANOTHER phase!

# Across the whole cycle: the mover context at k2 = (1-a, x+1, 1-b).
# This context (L, middle, R) might appear as non-mover at t in a different phase.
print("\n" + "="*70)
print("CROSS-PHASE EC: mover from one phase matches nonmover from another")
print("="*70)

cross_phase_ec = 0
for word in words:
    configs = build_configs(ms, n, word)
    if configs is None:
        continue
    if not is_wrap_adjacent(word, n):
        continue

    L = len(word)
    for t in sandwiched:
        bL, bR = (t-1)%n, (t+1)%n

        # All mover and nonmover contexts at t
        mover_set = set()
        nonmover_set = set()
        for s in range(L):
            ctx = (configs[s][bL], configs[s][t], configs[s][bR])
            if word[s] == t:
                mover_set.add(ctx)
            else:
                nonmover_set.add(ctx)

        overlap = mover_set & nonmover_set
        if overlap:
            # Is this overlap from a (1,1) phase mover matching cross-phase nonmover?
            # Check: find which mover step matches
            for s in range(L):
                if word[s] == t:
                    ctx = (configs[s][bL], configs[s][t], configs[s][bR])
                    if ctx in nonmover_set:
                        # Find which non-mover step
                        for s2 in range(L):
                            if word[s2] != t and (configs[s2][bL], configs[s2][t], configs[s2][bR]) == ctx:
                                # Are s and s2 in the same phase?
                                # Don't need to check, just count
                                break
            cross_phase_ec += 1

print(f"Cycles with EC at t via cross-phase: {cross_phase_ec} (out of 854 with (1,1))")
