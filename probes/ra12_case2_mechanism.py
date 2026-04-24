#!/usr/bin/env python3
"""RA12 Part 5: Pin down the EC mechanism.

KEY INSIGHT from Part 4:
- (1,1) phase directly gives EC at t for 70% of instances (LR match)
- 30% have LR mismatch in the (1,1) phase, but EC comes from other phases
- 48 exceptions have no EC at t at all

The (1,1) phase has:
- Mover step: t fires with context (L_m, v, R_m)
- Non-mover steps: t doesn't fire, context (L_nm, v, R_nm)

EC from (1,1) phase requires: L_m = L_nm AND R_m = R_nm at some non-mover step.

Since t's neighbors are binary (m_{tL}=m_{tR}=2):
- L_m, R_m, L_nm, R_nm all in {0,1}
- The walk fires tL and tR some number of times in the phase
- Key: at the mover step, what are the neighbor values? At non-mover steps?

NEW APPROACH: Instead of proving EC at q or t, investigate a SIMPLER claim:
- The (1,1) phase has at least 2 non-mover steps (since fc(t)=3 and cycle length >= 2n)
- In the (1,1) phase, the walk must cross the t-neighborhood
- The ring-walk constraint forces specific patterns

Let me check: for the (1,1) phase with value v, what is the distribution of
(L_m, R_m) vs non-mover (L,R) pairs? Is there a pigeonhole argument?
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

def has_ec_at_proc(word, cycle, ms, n, p):
    ell = len(word)
    pL = (p - 1) % n
    pR = (p + 1) % n
    mover_ctx = set()
    nonmover_ctx = set()
    for s in range(ell):
        ctx = (cycle[s][pL], cycle[s][p], cycle[s][pR])
        if word[s] == p:
            mover_ctx.add(ctx)
        else:
            nonmover_ctx.add(ctx)
    return bool(mover_ctx & nonmover_ctx)

# ===== DETAILED (1,1) PHASE STRUCTURE =====
print("=" * 70)
print("(1,1) PHASE: Detailed neighbor firing structure")
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

    # For each (1,1) phase: count neighbor firings within the phase
    neighbor_firing_counts = Counter()  # (firings of tL, firings of tR)
    nm_step_counts = Counter()  # number of non-mover steps

    # Whether the non-mover step(s) include a step where the mover is
    # NOT a neighbor of t (so both L and R are stable at that step)
    has_non_neighbor_nm = 0
    total_phases = 0

    # Direct EC from (1,1) phase
    direct_ec = 0
    no_direct_ec = 0

    # Detailed: what is the mover at each non-mover step relative to t?
    nm_mover_patterns = Counter()

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue

        ell = len(word)
        fc = Counter(word)

        for t in sandwiched:
            tL = (t - 1) % n
            tR = (t + 1) % n

            for pv in range(3):
                phase_steps = [s for s in range(ell) if cycle[s][t] == pv]
                t_mover = [s for s in phase_steps if word[s] == t]
                t_nonmover = [s for s in phase_steps if word[s] != t]

                if len(t_mover) == 1 and len(t_nonmover) >= 1:
                    total_phases += 1

                    sm = t_mover[0]
                    ctx_m = (cycle[sm][tL], cycle[sm][t], cycle[sm][tR])

                    # Count neighbor firings in phase
                    nL = sum(1 for s in phase_steps if word[s] == tL)
                    nR = sum(1 for s in phase_steps if word[s] == tR)
                    neighbor_firing_counts[(nL, nR)] += 1
                    nm_step_counts[len(t_nonmover)] += 1

                    # Non-neighbor non-mover steps?
                    non_neighbor_nm = [s for s in t_nonmover if word[s] not in (tL, tR)]
                    if non_neighbor_nm:
                        has_non_neighbor_nm += 1

                    # Direct EC?
                    nm_ctxs = {(cycle[s][tL], cycle[s][t], cycle[s][tR]) for s in t_nonmover}
                    if ctx_m in nm_ctxs:
                        direct_ec += 1
                    else:
                        no_direct_ec += 1

                    # What movers appear at non-mover steps?
                    nm_movers = tuple(sorted(set(
                        ('tL' if word[s] == tL else 'tR' if word[s] == tR else 'other')
                        for s in t_nonmover
                    )))
                    nm_mover_patterns[nm_movers] += 1

    print(f"Total (1,1) phases: {total_phases}")
    print(f"\nNeighbor firing counts in phase (fires_L, fires_R):")
    for key, cnt in sorted(neighbor_firing_counts.items(), key=lambda x: -x[1]):
        print(f"  {key}: {cnt}")

    print(f"\nNon-mover step count distribution:")
    for key, cnt in sorted(nm_step_counts.items()):
        print(f"  {key} non-mover steps: {cnt}")

    print(f"\nHas non-neighbor non-mover step: {has_non_neighbor_nm}/{total_phases}")

    print(f"\nDirect EC from (1,1) phase: {direct_ec}/{total_phases}")
    print(f"No direct EC: {no_direct_ec}")

    print(f"\nNon-mover step mover types:")
    for pat, cnt in sorted(nm_mover_patterns.items(), key=lambda x: -x[1]):
        print(f"  {pat}: {cnt}")

# ===== KEY QUESTION: When nm has ONLY neighbor movers, can we still get EC? =====
print("\n" + "=" * 70)
print("When ALL non-mover steps have neighbor movers: EC analysis")
print("=" * 70)

n = 7
ms = [2, 2, 2, 3, 2, 3, 3]
max_len = 24

words = enumerate_mover_words(ms, n, max_len)
sandwiched = [t for t in range(n)
              if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

only_neighbor_nm = 0
only_neighbor_nm_ec = 0
only_neighbor_nm_no_ec = 0

has_other_nm = 0
has_other_nm_ec = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    ell = len(word)
    fc = Counter(word)

    for t in sandwiched:
        tL = (t - 1) % n
        tR = (t + 1) % n

        for pv in range(3):
            phase_steps = [s for s in range(ell) if cycle[s][t] == pv]
            t_mover = [s for s in phase_steps if word[s] == t]
            t_nonmover = [s for s in phase_steps if word[s] != t]

            if len(t_mover) != 1 or len(t_nonmover) < 1:
                continue

            sm = t_mover[0]
            ctx_m = (cycle[sm][tL], cycle[sm][t], cycle[sm][tR])
            nm_ctxs = {(cycle[s][tL], cycle[s][t], cycle[s][tR]) for s in t_nonmover}
            direct_ec = ctx_m in nm_ctxs

            non_neighbor_nm = [s for s in t_nonmover if word[s] not in (tL, tR)]

            if not non_neighbor_nm:
                # ALL non-mover steps are neighbor firings
                only_neighbor_nm += 1
                if direct_ec:
                    only_neighbor_nm_ec += 1
                else:
                    only_neighbor_nm_no_ec += 1
            else:
                has_other_nm += 1
                if direct_ec:
                    has_other_nm_ec += 1

print(f"Only-neighbor non-mover steps: {only_neighbor_nm}")
print(f"  Direct EC: {only_neighbor_nm_ec}")
print(f"  No direct EC: {only_neighbor_nm_no_ec}")
print(f"Has non-neighbor non-mover: {has_other_nm}")
print(f"  Direct EC: {has_other_nm_ec}")

# ===== THE STEP-BEFORE AND STEP-AFTER PATTERN =====
print("\n" + "=" * 70)
print("Step-before and step-after t's mover in (1,1) phase")
print("=" * 70)

# In a ring walk, the step BEFORE t fires must be at tL or tR
# And the step AFTER t fires must be at tL or tR
# This means: at step sm-1, mover is tL or tR (one of the non-mover steps)
# At step sm+1, mover is tL or tR (but this is in the NEXT phase)

before_after = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    ell = len(word)
    fc = Counter(word)

    for t in sandwiched:
        tL = (t - 1) % n
        tR = (t + 1) % n

        for pv in range(3):
            phase_steps = [s for s in range(ell) if cycle[s][t] == pv]
            t_mover = [s for s in phase_steps if word[s] == t]
            t_nonmover = [s for s in phase_steps if word[s] != t]

            if len(t_mover) != 1 or len(t_nonmover) < 1:
                continue

            sm = t_mover[0]
            s_before = (sm - 1) % ell
            s_after = (sm + 1) % ell

            before = 'tL' if word[s_before] == tL else ('tR' if word[s_before] == tR else 'other')
            after = 'tL' if word[s_after] == tL else ('tR' if word[s_after] == tR else 'other')

            before_after[(before, after)] += 1

print("(step before mover, step after mover):")
for pat, cnt in sorted(before_after.items(), key=lambda x: -x[1]):
    print(f"  {pat}: {cnt}")

# ===== THE KEY INSIGHT: step sm-1 is a non-mover step in the SAME phase =====
print("\n" + "=" * 70)
print("CRITICAL: step sm-1 as non-mover step in (1,1) phase")
print("=" * 70)

# Step sm-1 fires tL or tR. Is sm-1 in the same phase (value pv)?
# If so, sm-1 is a non-mover step of the (1,1) phase.
# At sm-1: mover fires a neighbor. What is t's value? It's pv (same phase).
# At sm: mover fires t with context (L_m, pv, R_m).
# At sm-1: t's context is (L_{sm-1}, pv, R_{sm-1}).
#
# The neighbor that fires at sm-1 changes ONE of L or R.
# So exactly one of (L_{sm-1}, R_{sm-1}) differs from (L_m, R_m) by a toggle.
# Specifically: if word[sm-1] = tL, then L changes (tL fires), R stays.
# So L_{sm-1} = 1-L_m, R_{sm-1} = R_m. Context is (1-L_m, pv, R_m).
# This matches mover context (L_m, pv, R_m) only if L_m = 1-L_m, impossible for binary.
#
# Similarly if word[sm-1] = tR: L_{sm-1} = L_m, R_{sm-1} = 1-R_m.
# Context (L_m, pv, 1-R_m) ≠ (L_m, pv, R_m).
#
# So: sm-1 is ALWAYS in the phase (since t doesn't fire between sm-1 and sm),
# and it NEVER matches the mover context (because the neighbor that just fired
# has a different value than at sm).
#
# BUT: what about sm-2, sm-3, etc.? Those might match!
# And what about steps AFTER the previous mover step?

# Let's check: is step sm-1 ALWAYS in the same phase?
same_phase = 0
diff_phase = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    ell = len(word)

    for t in sandwiched:
        tL = (t - 1) % n
        tR = (t + 1) % n

        for pv in range(3):
            phase_steps = set(s for s in range(ell) if cycle[s][t] == pv)
            t_mover = [s for s in phase_steps if word[s] == t]
            t_nonmover = [s for s in phase_steps if word[s] != t]

            if len(t_mover) != 1 or len(t_nonmover) < 1:
                continue

            sm = t_mover[0]
            s_before = (sm - 1) % ell

            if s_before in phase_steps:
                same_phase += 1
            else:
                diff_phase += 1

print(f"step sm-1 in same phase: {same_phase}")
print(f"step sm-1 in different phase: {diff_phase}")

# ===== DEEPER: Trace the FULL non-mover step sequence in the (1,1) phase =====
print("\n" + "=" * 70)
print("Full non-mover step sequence in (1,1) phase")
print("=" * 70)

# For each (1,1) phase, list all non-mover steps in temporal order
# and show which ones have the same LR as the mover context
n = 7
ms = [2, 2, 2, 3, 2, 3, 3]
max_len = 24

words = enumerate_mover_words(ms, n, max_len)
sandwiched = [t for t in range(n)
              if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

match_positions = Counter()  # which temporal position (relative to mover) has the match
no_match_detail = []

shown = 0
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    ell = len(word)
    fc = Counter(word)

    for t in sandwiched:
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

            # Temporal order: put mover step in the sequence
            # and find relative positions
            found_match = False
            for i, s in enumerate(t_nonmover):
                lr_nm = (cycle[s][tL], cycle[s][tR])
                if lr_nm == lr_m:
                    # Position relative to mover step
                    rel = (s - sm) % ell
                    match_positions[rel] += 1
                    found_match = True

            if not found_match and shown < 5:
                shown += 1
                no_match_detail.append({
                    'word': word, 't': t, 'pv': pv, 'sm': sm,
                    'lr_m': lr_m,
                    'nm_details': [(s, (cycle[s][tL], cycle[s][tR]), word[s]) for s in t_nonmover]
                })

print(f"Match position distribution (step relative to mover, mod ell):")
for pos in sorted(match_positions.keys()):
    print(f"  rel={pos}: {match_positions[pos]}")

if no_match_detail:
    print(f"\nExamples with no LR match in (1,1) phase:")
    for detail in no_match_detail[:3]:
        print(f"\n  t={detail['t']}, phase={detail['pv']}, mover_step={detail['sm']}")
        print(f"  Mover LR = {detail['lr_m']}")
        for s, lr, mover in detail['nm_details']:
            rel = 'tL' if mover == (detail['t']-1)%n else ('tR' if mover == (detail['t']+1)%n else f'p{mover}')
            print(f"    s={s}: LR={lr}, fires={rel}")
