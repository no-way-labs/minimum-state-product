#!/usr/bin/env python3
"""RA12 Part 9: Return EC mechanism.

KEY DISCOVERY: EC at t is ALWAYS intra-phase. Cross-phase EC = 0.

Categories with 100% EC rate:
- (0, 2, other>=1): tR fires 2x, with non-neighbor step(s)
- (2, 0, other>=1): tL fires 2x, with non-neighbor step(s)
- (0, 3+, *): any 3+ same-side neighbor firings

Categories with 0% EC rate:
- (0, 1, 0): only 1 tR firing, no other steps
- (1, 0, 0): only 1 tL firing, no other steps
- (1, 1, *): one tL and one tR firing (no same-side double)
- (2, 1, 8): tL fires 2x, tR fires 1x, 8 others — 0% EC!

Wait, (2, 1, 8) has 0% EC? That's surprising given tL fires 2x.

Let me understand the RETURN MECHANISM:
If tR fires at step s_a and then at s_b (both in the phase),
at s_a: R toggles from R_0 to 1-R_0
at s_b: R toggles from 1-R_0 to R_0 (returns!)

Between s_a and s_b, any non-neighbor step has R = 1-R_0.
After s_b, R = R_0 (same as at mover step).

So the question is: after the SECOND tR firing (s_b), is there a
non-neighbor step before the mover step (or between phase entry and s_a)?
If so: at that step, R = R_0, and if L also = L_m at that step, then EC.

But L might have changed too! If tL also fires, L might be different.

KEY INSIGHT: With only same-side double firing (e.g., 2 tR firings, 0 tL firings),
after the second tR firing, L hasn't changed since the phase entry.
So L = L_m iff L at phase entry = L_m.

Actually: the mover step is the LAST step of the phase (or rather, the only t-firing).
The phase starts when t was last set to pv (by t's previous firing).

Wait - let me reconsider. The steps in the phase are NOT necessarily contiguous
in time. They're just the steps where c[t] = pv. But they ARE contiguous:
between two consecutive firings of t, t's value doesn't change, so all steps
in that interval have the same t-value.

So the (1,1) phase IS a contiguous interval from the previous t-firing (exclusive)
to the current t-firing (inclusive). The non-mover steps come BEFORE the mover step.

This means: within the phase, the TEMPORAL ORDER is:
[non-mover steps in order] ... [mover step at the end]

Now: the mover step fires with context (L_m, pv, R_m).
Step sm-1 fires a neighbor (ring walk) and is in the phase.

RETURN MECHANISM:
If tR fires at steps s_a, s_b (s_a < s_b < sm, temporal):
- Between s_a and s_b, R = 1-R_0 (toggled once)
- After s_b, R = R_0 (toggled back)
- At the mover step, R = R_m
- So R_0 = R_m (the double firing restored R to its mover value)

For EC: need a non-neighbor step after s_b where L = L_m.
Since tL didn't fire (in the (0, 2, *) case), L hasn't changed since phase entry.
So L = L_m at ALL steps in the phase.

Therefore: ANY non-neighbor step after the second tR firing has
(L, R) = (L_m, R_m). EC guaranteed!

But wait: is there always such a step? Yes, because:
- The second tR firing is s_b
- The walk is at tR at s_b
- Step s_b+1 is at a neighbor of tR = tR-1 or tR+1
- tR-1 = t (but that's the mover step, not yet)
- Actually: s_b could be followed by the mover step directly!
  If word[s_b] = tR and word[s_b+1] = t, then s_b+1 = sm and there's no
  non-neighbor step between s_b and sm.

Let me check: in the (0, 2, other>=1) category, is it always the case
that the non-neighbor step comes after the SECOND tR firing?

Actually the "other" count means there ARE non-neighbor steps.
The question is their temporal position relative to the tR firings.
"""

from collections import Counter

def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= 2*n and config == start:
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

# ===== TEMPORAL STRUCTURE WITHIN (1,1) PHASE =====
print("=" * 70)
print("RETURN EC: Temporal structure within (1,1) phase")
print("=" * 70)

for n, ms, max_len, label in [
    (5, [2,2,2,3,2], 16, "n=5"),
    (7, [2,2,2,3,2,3,3], 24, "n=7"),
]:
    print(f"\n{'='*70}")
    print(f"  {label}: ms={ms}")
    print(f"{'='*70}")

    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [t for t in range(n)
                  if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

    # For each (1,1) phase with a double same-side firing:
    # Check whether non-neighbor step exists AFTER the second same-side firing

    double_same_total = 0
    nn_after_second = 0
    nn_only_before_second = 0
    nn_between_firings = 0

    # Also: for phases with NO double same-side firing:
    # What's the mechanism for EC?
    no_double_total = 0
    no_double_ec = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue

        ell = len(word)
        fc = Counter(word)

        for t in sandwiched:
            if fc[t] != 3:
                continue
            tL = (t - 1) % n
            tR = (t + 1) % n

            for pv in range(3):
                phase_steps = [s for s in range(ell) if cycle[s][t] == pv]
                t_mover = [s for s in phase_steps if word[s] == t]
                t_nonmover = [s for s in phase_steps if word[s] != t]

                if len(t_mover) != 1 or len(t_nonmover) < 1:
                    continue

                sm = t_mover[0]

                # Separate nm steps by type
                tL_steps = sorted([s for s in t_nonmover if word[s] == tL],
                                  key=lambda s: (s - sm) % ell)
                tR_steps = sorted([s for s in t_nonmover if word[s] == tR],
                                  key=lambda s: (s - sm) % ell)
                other_steps = sorted([s for s in t_nonmover if word[s] not in (tL, tR)],
                                     key=lambda s: (s - sm) % ell)

                # Phase starts right after previous t-firing
                # Steps are temporally ordered within the phase
                # mover step is LAST

                # Double same-side?
                has_double_L = len(tL_steps) >= 2
                has_double_R = len(tR_steps) >= 2

                if has_double_L or has_double_R:
                    double_same_total += 1

                    # For the double side, find the second firing
                    if has_double_R:
                        second_R = tR_steps[1]
                        # Non-neighbor steps after second_R?
                        after = [s for s in other_steps if (s - second_R) % ell < (sm - second_R) % ell]
                        if after:
                            nn_after_second += 1
                        else:
                            nn_only_before_second += 1
                            # Check between first and second
                            first_R = tR_steps[0]
                            between = [s for s in other_steps if
                                       (s - first_R) % ell < (second_R - first_R) % ell]
                            if between:
                                nn_between_firings += 1

                    elif has_double_L:
                        second_L = tL_steps[1]
                        after = [s for s in other_steps if (s - second_L) % ell < (sm - second_L) % ell]
                        if after:
                            nn_after_second += 1
                        else:
                            nn_only_before_second += 1
                            first_L = tL_steps[0]
                            between = [s for s in other_steps if
                                       (s - first_L) % ell < (second_L - first_L) % ell]
                            if between:
                                nn_between_firings += 1
                else:
                    no_double_total += 1
                    # Check if EC exists at t from this phase
                    ctx_m = (cycle[sm][tL], cycle[sm][t], cycle[sm][tR])
                    nm_ctxs = {(cycle[s][tL], cycle[s][t], cycle[s][tR]) for s in t_nonmover}
                    if ctx_m in nm_ctxs:
                        no_double_ec += 1

    print(f"Phases with double same-side firing: {double_same_total}")
    print(f"  Non-neighbor step AFTER second same-side: {nn_after_second}")
    print(f"  Non-neighbor step only BEFORE second: {nn_only_before_second}")
    print(f"    Of those, non-neighbor BETWEEN the two firings: {nn_between_firings}")

    print(f"\nPhases WITHOUT double same-side: {no_double_total}")
    print(f"  Direct EC: {no_double_ec}")
    print(f"  No direct EC: {no_double_total - no_double_ec}")

# ===== CHECK: (1,1) phases with no direct EC — what about OTHER phases? =====
print("\n" + "=" * 70)
print("PHASES WITHOUT DIRECT EC: Do other phases compensate?")
print("=" * 70)

n = 7
ms = [2, 2, 2, 3, 2, 3, 3]
max_len = 24

words = enumerate_mover_words(ms, n, max_len)
sandwiched = [t for t in range(n)
              if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

# For each cycle: check if ALL 3 phases have no direct EC.
# If so, EC at t must be cross-phase (but we showed cross-phase = 0!)
# So: cycles where NO phase has direct EC -> no EC at t.

no_ec_at_t_cycles = 0
some_ec_at_t = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    ell = len(word)
    fc = Counter(word)

    for t in sandwiched:
        if fc[t] != 3:
            continue
        tL = (t - 1) % n
        tR = (t + 1) % n

        any_phase_ec = False
        for pv in range(3):
            phase_steps = [s for s in range(ell) if cycle[s][t] == pv]
            t_mover = [s for s in phase_steps if word[s] == t]
            t_nonmover = [s for s in phase_steps if word[s] != t]

            if len(t_mover) != 1:
                continue

            sm = t_mover[0]
            ctx_m = (cycle[sm][tL], cycle[sm][t], cycle[sm][tR])
            nm_ctxs = {(cycle[s][tL], cycle[s][t], cycle[s][tR]) for s in t_nonmover}
            if ctx_m in nm_ctxs:
                any_phase_ec = True
                break

        if any_phase_ec:
            some_ec_at_t += 1
        else:
            no_ec_at_t_cycles += 1

print(f"Cycles with fc(t)=3:")
print(f"  Some phase gives direct EC at t: {some_ec_at_t}")
print(f"  NO phase gives direct EC: {no_ec_at_t_cycles}")

# ===== PRECISE: for non-neighbor nm steps, trace L,R evolution =====
print("\n" + "=" * 70)
print("L,R EVOLUTION at non-neighbor nm steps")
print("=" * 70)

# For each (1,1) phase with EC:
# Identify the matching non-neighbor step
# Check: did a double same-side firing create the match?
# Or: does L already = L_m from phase entry?

match_types = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    ell = len(word)
    fc = Counter(word)

    for t in sandwiched:
        if fc[t] != 3:
            continue
        tL = (t - 1) % n
        tR = (t + 1) % n

        for pv in range(3):
            phase_steps = [s for s in range(ell) if cycle[s][t] == pv]
            t_mover = [s for s in phase_steps if word[s] == t]
            t_nonmover = [s for s in phase_steps if word[s] != t]

            if len(t_mover) != 1 or len(t_nonmover) < 1:
                continue

            sm = t_mover[0]
            lr_m = (cycle[sm][tL], cycle[sm][tR])

            # Find matching non-neighbor step (first one)
            nn_nm = [s for s in t_nonmover if word[s] not in (tL, tR)]
            matching_nn = [s for s in nn_nm if (cycle[s][tL], cycle[s][tR]) == lr_m]

            if matching_nn:
                s_match = matching_nn[0]

                # Count tL and tR firings between s_match and sm
                between_tL = 0
                between_tR = 0
                s = (s_match + 1) % ell
                while s != sm:
                    if word[s] == tL:
                        between_tL += 1
                    elif word[s] == tR:
                        between_tR += 1
                    s = (s + 1) % ell

                # For the match to hold: tL fires between must be EVEN, tR fires must be EVEN
                match_types[(between_tL % 2, between_tR % 2)] += 1

print(f"Neighbor firings between matching step and mover (mod 2):")
for (pL, pR), cnt in sorted(match_types.items(), key=lambda x: -x[1]):
    print(f"  tL_fires_mod2={pL}, tR_fires_mod2={pR}: {cnt}")
    # If both even: L and R returned to their values at s_match -> confirms EC
