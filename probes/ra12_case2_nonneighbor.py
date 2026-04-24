#!/usr/bin/env python3
"""RA12 Part 6: Non-neighbor non-mover step analysis.

KEY DISCOVERY: Direct EC from (1,1) phase REQUIRES a non-neighbor non-mover step.
When all nm steps are neighbor firings, the L or R value toggled at sm-1 makes
the context at sm-1 differ from mover context.

CONJECTURE: If there's a non-neighbor nm step where L and R are BOTH at their
mover values, then EC. This happens iff neither L nor R was "just toggled".

Question: when does this condition hold? The non-neighbor nm steps are steps
where the walk is far from t. At those steps, L and R haven't been recently
changed. So we need to check: after ALL neighbor firings in the phase complete,
is there a non-neighbor step?

CRITICAL CHECK: For phases where the walk departs t-neighborhood, does the
walk cross through t-neighborhood later (toggling L or R), then depart again?
If the departure is AFTER the last neighbor firing, the L,R are stable = mover values.

Actually the question is simpler:
- Between the (1,1) phase's last NON-t-neighboring step and the mover step,
  are there neighbor firings that change L or R?
- If the last non-neighbor step S_other has L_m and R_m at that time, then EC.
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

print("=" * 70)
print("NON-NEIGHBOR NM STEP: When does (L_nm, R_nm) = (L_m, R_m)?")
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

    total_phases = 0
    phases_with_non_neighbor_nm = 0
    phases_with_matching_nn_nm = 0  # non-neighbor nm step with (L_m, R_m)
    phases_no_nn_nm = 0  # only neighbor nm steps
    phases_nn_nm_but_no_match = 0

    # For phases with non-neighbor nm but no LR match:
    # what's the relationship between the nn nm LR and mover LR?
    nn_nm_lr_vs_mover = Counter()

    # DEEPER: for each non-neighbor nm step, trace what happened to L and R
    # between it and the mover step
    between_analysis = Counter()

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

                total_phases += 1
                sm = t_mover[0]
                lr_m = (cycle[sm][tL], cycle[sm][tR])

                # Non-neighbor non-mover steps
                nn_nm_steps = [s for s in t_nonmover if word[s] not in (tL, tR)]

                if not nn_nm_steps:
                    phases_no_nn_nm += 1
                    continue

                phases_with_non_neighbor_nm += 1

                # Check each non-neighbor nm step
                found_match = False
                for s in nn_nm_steps:
                    lr_s = (cycle[s][tL], cycle[s][tR])
                    if lr_s == lr_m:
                        found_match = True
                        break

                if found_match:
                    phases_with_matching_nn_nm += 1
                else:
                    phases_nn_nm_but_no_match += 1

                    # Analyze: what LR pairs appear at non-neighbor nm steps?
                    nn_nm_lrs = {(cycle[s][tL], cycle[s][tR]) for s in nn_nm_steps}
                    nn_nm_lr_vs_mover[f"mover={lr_m}, nn_nm={sorted(nn_nm_lrs)}"] += 1

                    # What happens between last nn_nm step and mover step?
                    # Find the last non-neighbor step (closest to sm going backward)
                    last_nn = max(nn_nm_steps, key=lambda s: -(sm - s) % ell)
                    # Steps between last_nn and sm
                    between = []
                    s = (last_nn + 1) % ell
                    while s != sm:
                        between.append(word[s])
                        s = (s + 1) % ell
                    # Classify
                    n_tL = sum(1 for m in between if m == tL)
                    n_tR = sum(1 for m in between if m == tR)
                    between_analysis[(n_tL, n_tR)] += 1

    print(f"Total (1,1) phases: {total_phases}")
    print(f"  No non-neighbor nm step: {phases_no_nn_nm}")
    print(f"  Has non-neighbor nm step: {phases_with_non_neighbor_nm}")
    print(f"    With LR match (direct EC): {phases_with_matching_nn_nm} ({100*phases_with_matching_nn_nm/max(1,phases_with_non_neighbor_nm):.1f}%)")
    print(f"    Without LR match: {phases_nn_nm_but_no_match}")

    if nn_nm_lr_vs_mover:
        print(f"\n  No-match details (nn_nm LR vs mover LR):")
        for desc, cnt in sorted(nn_nm_lr_vs_mover.items(), key=lambda x: -x[1]):
            print(f"    {desc}: {cnt}")

    if between_analysis:
        print(f"\n  Between last nn_nm and mover (neighbor firings):")
        for (nL, nR), cnt in sorted(between_analysis.items(), key=lambda x: -x[1]):
            print(f"    tL_fires={nL}, tR_fires={nR}: {cnt}")

# ===== PHASE STRUCTURE: What determines the non-mover steps? =====
print("\n" + "=" * 70)
print("PHASE STRUCTURE: Step classification within (1,1) phase")
print("=" * 70)

n = 7
ms = [2, 2, 2, 3, 2, 3, 3]
max_len = 24
words = enumerate_mover_words(ms, n, max_len)
sandwiched = [t for t in range(n)
              if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

# For phases WITHOUT non-neighbor nm steps: analyze why
# The phase has only sm, tL-firings, tR-firings
# With 1 tL and 1 tR firing, the phase has exactly 3 steps

only_neighbor_analysis = Counter()
only_neighbor_lengths = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    ell = len(word)

    for t in sandwiched:
        tL = (t - 1) % n
        tR = (t + 1) % n

        for pv in range(3):
            phase_steps = [s for s in range(ell) if cycle[s][t] == pv]
            t_mover = [s for s in phase_steps if word[s] == t]
            t_nonmover = [s for s in phase_steps if word[s] != t]

            if len(t_mover) != 1 or len(t_nonmover) < 1:
                continue

            nn_nm_steps = [s for s in t_nonmover if word[s] not in (tL, tR)]
            if not nn_nm_steps:
                # Only neighbor nm steps
                nm_movers = tuple(sorted([
                    'tL' if word[s] == tL else 'tR'
                    for s in t_nonmover
                ]))
                only_neighbor_analysis[nm_movers] += 1
                only_neighbor_lengths[len(t_nonmover)] += 1

print("Phases with ONLY neighbor non-mover steps:")
print(f"  Mover patterns: {dict(sorted(only_neighbor_analysis.items(), key=lambda x: -x[1]))}")
print(f"  Non-mover count: {dict(sorted(only_neighbor_lengths.items()))}")

# ===== OVERALL EC CHECK BY PHASE TYPE =====
print("\n" + "=" * 70)
print("OVERALL: Does EVERY cycle have EC at t or EC at some binary?")
print("=" * 70)

for n, ms, max_len, label in [
    (5, [2,2,2,3,2], 16, "n=5"),
    (7, [2,2,2,3,2,3,3], 24, "n=7"),
]:
    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [t for t in range(n)
                  if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

    total = 0
    ec_at_t = 0
    ec_nowhere = 0
    ec_somewhere = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        total += 1

        # EC at sandwiched t?
        found_t = any(has_ec_at_proc(word, cycle, ms, n, t) for t in sandwiched)
        if found_t:
            ec_at_t += 1

        # EC anywhere?
        found_any = any(has_ec_at_proc(word, cycle, ms, n, p) for p in range(n))
        if found_any:
            ec_somewhere += 1
        else:
            ec_nowhere += 1

    print(f"\n{label}: {total} cycles")
    print(f"  EC at sandwiched t: {ec_at_t} ({100*ec_at_t/total:.1f}%)")
    print(f"  EC somewhere: {ec_somewhere} ({100*ec_somewhere/total:.1f}%)")
    print(f"  EC nowhere: {ec_nowhere}")
