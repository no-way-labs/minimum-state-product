#!/usr/bin/env python3
"""RA12 Part 8: Final synthesis — what universal mechanism guarantees EC?

KEY FINDINGS SO FAR:
1. Case 2 ((a1,b1) != (a2,b2) at q) occurs 66% at n=7, q has NO EC in these cases
2. EC at sandwiched t with fc(t)=3: 99.3% at n=7 (48 exceptions)
3. EC at sandwiched t with fc(t)=6: 0% (but these have EC elsewhere)
4. ALL cycles have EC at SOME processor (verified n=5, n=7)

The question is: what's the proof architecture?

APPROACH 1: EC at sandwiched t (non-universal, 95.1%)
APPROACH 2: Prove something about the specific case structure

Let me investigate the most promising angle: the (1,1) phase directly.

THEOREM ATTEMPT: If t is sandwiched ternary with fc(t)=3 (i.e., each phase has
exactly 1 mover step), and the (1,1) phase has >= 2 non-mover steps including
at least one non-neighbor non-mover step, then EC at t from the (1,1) phase.

CHECK: When does the (1,1) phase have a non-neighbor non-mover step with
the right (L,R) values?

The analysis so far showed: between the last non-neighbor step and the mover,
there is ALWAYS exactly 1 neighbor firing. This neighbor firing toggles one
of L or R.

So at the non-neighbor step just before the mover (going backward):
- If the intermediate step fires tL: L was toggled, so L_nn = 1-L_m, R_nn = R_m
- If the intermediate step fires tR: R was toggled, so L_nn = L_m, R_nn = 1-R_m

Neither matches (L_m, R_m) at the last non-neighbor step.

But what about EARLIER non-neighbor steps? If there's a non-neighbor step
where the L and R happen to match, that's also fine.

ACTUALLY: Let me reconsider. The key insight is about the ENTRY into the phase.
When the walk enters the phase from the previous phase, t's value changes from
pv-1 to pv (when t fires). Then the walk continues. The NON-MOVER steps in the
phase are the steps BEFORE the mover step (cyclically).

Let me trace the COMPLETE structure within each (1,1) phase.
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

# ===== COMPREHENSIVE: Check all (M_0, N_0, M_1, N_1, M_2, N_2) phase types =====
print("=" * 70)
print("COMPLETE PHASE STRUCTURE AT SANDWICHED t (fc(t)=3)")
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

    total = 0
    ec_at_t = 0

    # For fc(t)=3 with (1,1) phase: detailed neighbor firing analysis
    # In each (1,1) phase, categorize by:
    # - Number of tL firings in phase
    # - Number of tR firings in phase
    # - Number of non-neighbor non-mover steps
    # - Whether direct EC occurs

    category_ec = Counter()
    category_no_ec = Counter()

    # SPECIFIC CHECK: Does the mover context EVER appear at ANY earlier non-mover step?
    # This is the direct (1,1) phase EC.
    # When it doesn't: can we prove EC from cross-phase argument?

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        total += 1

        ell = len(word)
        fc = Counter(word)

        for t in sandwiched:
            if fc[t] != 3:
                continue

            tL = (t - 1) % n
            tR = (t + 1) % n

            has_ec = has_ec_at_proc(word, cycle, ms, n, t)
            if has_ec:
                ec_at_t += 1

            for pv in range(3):
                phase_steps = [s for s in range(ell) if cycle[s][t] == pv]
                t_mover = [s for s in phase_steps if word[s] == t]
                t_nonmover = [s for s in phase_steps if word[s] != t]

                if len(t_mover) != 1:
                    continue

                sm = t_mover[0]
                lr_m = (cycle[sm][tL], cycle[sm][tR])

                # Count firings
                n_tL = sum(1 for s in t_nonmover if word[s] == tL)
                n_tR = sum(1 for s in t_nonmover if word[s] == tR)
                n_other = len(t_nonmover) - n_tL - n_tR

                # Direct EC from this phase?
                nm_ctxs = {(cycle[s][tL], cycle[s][t], cycle[s][tR]) for s in t_nonmover}
                ctx_m = (cycle[sm][tL], cycle[sm][t], cycle[sm][tR])
                direct_ec = ctx_m in nm_ctxs

                cat = (n_tL, n_tR, n_other)
                if direct_ec:
                    category_ec[cat] += 1
                else:
                    category_no_ec[cat] += 1

    print(f"Total cycles: {total}")
    print(f"EC at sandwiched t (fc=3): {ec_at_t}")

    print(f"\nCategory (tL_fires, tR_fires, other_nm) -> direct EC rate:")
    all_cats = sorted(set(list(category_ec.keys()) + list(category_no_ec.keys())))
    for cat in all_cats:
        ec_c = category_ec.get(cat, 0)
        no_ec_c = category_no_ec.get(cat, 0)
        total_c = ec_c + no_ec_c
        pct = 100 * ec_c / total_c if total_c > 0 else 0
        print(f"  {cat}: EC={ec_c}, no_EC={no_ec_c}, rate={pct:.1f}%")

# ===== THE KEY: 2-phase interaction =====
print("\n" + "=" * 70)
print("2-PHASE INTERACTION: Mover from phase A, non-mover from phase B")
print("=" * 70)

n = 7
ms = [2, 2, 2, 3, 2, 3, 3]
max_len = 24

words = enumerate_mover_words(ms, n, max_len)
sandwiched = [t for t in range(n)
              if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

# For each cycle with fc(t)=3:
# 3 mover contexts: one per phase
# All non-mover contexts from all 3 phases
# Which cross-phase overlaps exist?

cross_phase_analysis = Counter()  # (mover_phase, nonmover_phase_where_match) counts

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

        # Organize by phase
        phase_mover_ctx = {}
        phase_nonmover_ctxs = {}
        for pv in range(3):
            phase_steps = [s for s in range(ell) if cycle[s][t] == pv]
            for s in phase_steps:
                ctx = (cycle[s][tL], cycle[s][t], cycle[s][tR])
                if word[s] == t:
                    phase_mover_ctx[pv] = ctx
                else:
                    if pv not in phase_nonmover_ctxs:
                        phase_nonmover_ctxs[pv] = set()
                    phase_nonmover_ctxs[pv].add(ctx)

        # Check cross-phase overlaps
        for m_phase in range(3):
            if m_phase not in phase_mover_ctx:
                continue
            m_ctx = phase_mover_ctx[m_phase]
            for nm_phase in range(3):
                if nm_phase not in phase_nonmover_ctxs:
                    continue
                if m_ctx in phase_nonmover_ctxs[nm_phase]:
                    cross_phase_analysis[(m_phase == nm_phase,)] += 1

print(f"Cross-phase EC occurrences:")
print(f"  Same phase (intra-phase EC): {cross_phase_analysis.get((True,), 0)}")
print(f"  Different phase (cross-phase EC): {cross_phase_analysis.get((False,), 0)}")

# ===== FINAL: n=5 trace to understand cross-phase =====
print("\n" + "=" * 70)
print("n=5: Complete 3-phase structure at sandwiched t")
print("=" * 70)

n = 5
ms = [2, 2, 2, 3, 2]
max_len = 16

words = enumerate_mover_words(ms, n, max_len)
sandwiched = [t for t in range(n)
              if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

shown = 0
for word in words:
    if shown >= 5:
        break
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

        print(f"\nCycle #{shown+1}: word_len={ell}, t={t}")
        print(f"  word = {word}")

        for pv in range(3):
            phase_steps = [s for s in range(ell) if cycle[s][t] == pv]
            t_mover = [s for s in phase_steps if word[s] == t]
            t_nonmover = [s for s in phase_steps if word[s] != t]
            print(f"\n  Phase {pv} ({len(t_mover)}M, {len(t_nonmover)}NM):")
            for s in sorted(phase_steps):
                ctx = (cycle[s][tL], cycle[s][t], cycle[s][tR])
                is_m = "MOVER" if word[s] == t else f"nm(fires={word[s]})"
                print(f"    s={s:2d}: ctx={ctx} {is_m}")

        # Show EC
        mover_ctx = set()
        nonmover_ctx = set()
        for s in range(ell):
            ctx = (cycle[s][tL], cycle[s][t], cycle[s][tR])
            if word[s] == t:
                mover_ctx.add(ctx)
            else:
                nonmover_ctx.add(ctx)
        overlap = mover_ctx & nonmover_ctx
        print(f"\n  EC at t: mover={sorted(mover_ctx)}")
        print(f"           nonm ={sorted(nonmover_ctx)}")
        print(f"           overlap={sorted(overlap)}")

        shown += 1
