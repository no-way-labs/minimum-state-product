#!/usr/bin/env python3
"""RA12 SYNTHESIS: Comprehensive EC universality check.

PROVED MECHANISM: Within any (1,1) phase at sandwiched ternary t (fc=3):
If the phase has a double same-side neighbor firing AND a non-neighbor
non-mover step (between the two firings or after the second),
then direct EC at t from this phase.

REMAINING QUESTION: What about the 48 cycles where no phase gives direct EC?
These cycles have EC elsewhere. But for a clean proof, we need a universal argument.

THIS SCRIPT: Check the COMPLETE picture at n=5, n=7, n=8:
1. Universal EC at some proc (already confirmed)
2. For cycles without EC at sandwiched t: analyze the phase structure
3. Determine if a different proof architecture handles these cases
4. Check whether phase structure universally guarantees the "double+nn" condition
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

def phase_gives_ec(word, cycle, ms, n, t, pv):
    """Check if phase pv at processor t gives direct EC."""
    ell = len(word)
    tL = (t - 1) % n
    tR = (t + 1) % n
    phase_steps = [s for s in range(ell) if cycle[s][t] == pv]
    t_mover = [s for s in phase_steps if word[s] == t]
    t_nonmover = [s for s in phase_steps if word[s] != t]

    if len(t_mover) != 1 or len(t_nonmover) < 1:
        return False

    sm = t_mover[0]
    ctx_m = (cycle[sm][tL], cycle[sm][t], cycle[sm][tR])
    nm_ctxs = {(cycle[s][tL], cycle[s][t], cycle[s][tR]) for s in t_nonmover}
    return ctx_m in nm_ctxs

# ===== COMPLETE ANALYSIS =====
print("=" * 70)
print("RA12 SYNTHESIS: Complete EC analysis")
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
    ternary = [t for t in range(n) if ms[t] == 3]

    total = 0
    ec_at_sandwiched = 0
    ec_at_other_ternary = 0
    ec_only_at_binary = 0
    ec_nowhere = 0

    # For each ternary proc: check (1,1) phase with double+nn mechanism
    double_nn_covers = 0
    double_nn_fails = 0

    exceptions = []

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        total += 1
        ell = len(word)
        fc = Counter(word)

        # Check EC at each proc type
        ec_sand = any(has_ec_at_proc(word, cycle, ms, n, t) for t in sandwiched)
        ec_other_t = any(has_ec_at_proc(word, cycle, ms, n, t)
                         for t in ternary if t not in sandwiched)
        ec_binary = any(has_ec_at_proc(word, cycle, ms, n, p)
                        for p in range(n) if ms[p] == 2)
        ec_any = any(has_ec_at_proc(word, cycle, ms, n, p) for p in range(n))

        if ec_sand:
            ec_at_sandwiched += 1
        elif ec_other_t:
            ec_at_other_ternary += 1
        elif ec_binary:
            ec_only_at_binary += 1
        elif not ec_any:
            ec_nowhere += 1

        # Check double+nn mechanism at sandwiched t
        for t in sandwiched:
            if fc[t] != 3:
                continue
            tL = (t - 1) % n
            tR = (t + 1) % n

            any_phase_has_double_nn = False
            for pv in range(3):
                phase_steps = [s for s in range(ell) if cycle[s][t] == pv]
                t_mover_s = [s for s in phase_steps if word[s] == t]
                t_nonmover_s = [s for s in phase_steps if word[s] != t]

                if len(t_mover_s) != 1 or len(t_nonmover_s) < 1:
                    continue

                sm = t_mover_s[0]
                tL_steps = [s for s in t_nonmover_s if word[s] == tL]
                tR_steps = [s for s in t_nonmover_s if word[s] == tR]
                other_steps = [s for s in t_nonmover_s if word[s] not in (tL, tR)]

                has_double = len(tL_steps) >= 2 or len(tR_steps) >= 2
                has_nn = len(other_steps) >= 1

                if has_double and has_nn:
                    any_phase_has_double_nn = True
                    break

            if any_phase_has_double_nn:
                double_nn_covers += 1
            else:
                double_nn_fails += 1
                if not ec_sand:
                    exceptions.append((word, t))

    print(f"Total cycles: {total}")
    print(f"\nEC location:")
    print(f"  At sandwiched t: {ec_at_sandwiched} ({100*ec_at_sandwiched/total:.1f}%)")
    print(f"  At other ternary: {ec_at_other_ternary}")
    print(f"  Only at binary: {ec_only_at_binary}")
    print(f"  NOWHERE: {ec_nowhere}")

    print(f"\nDouble+NN mechanism at sandwiched t:")
    print(f"  Covers: {double_nn_covers}")
    print(f"  Fails: {double_nn_fails}")

    if exceptions:
        print(f"\nExceptions (double+nn fails AND no EC at t): {len(exceptions)}")
        # Analyze phase structure for exceptions
        for word, t in exceptions[:5]:
            cycle = build_cycle(ms, n, word)
            ell = len(word)
            fc = Counter(word)
            tL = (t - 1) % n
            tR = (t + 1) % n

            print(f"\n  word_len={ell}, t={t}")
            for pv in range(3):
                phase_steps = [s for s in range(ell) if cycle[s][t] == pv]
                t_mover_s = [s for s in phase_steps if word[s] == t]
                t_nonmover_s = [s for s in phase_steps if word[s] != t]

                if len(t_mover_s) != 1:
                    print(f"    Phase {pv}: fc_in_phase={len(t_mover_s)} (not (1,1))")
                    continue

                sm = t_mover_s[0]
                nL = sum(1 for s in t_nonmover_s if word[s] == tL)
                nR = sum(1 for s in t_nonmover_s if word[s] == tR)
                nO = len(t_nonmover_s) - nL - nR
                ctx_m = (cycle[sm][tL], cycle[sm][t], cycle[sm][tR])
                nn_steps = [s for s in t_nonmover_s if word[s] not in (tL, tR)]
                nn_lrs = [(cycle[s][tL], cycle[s][tR]) for s in nn_steps]

                print(f"    Phase {pv}: (tL={nL}, tR={nR}, other={nO}), "
                      f"mover_ctx={ctx_m}, nn_LRs={nn_lrs}")

            # Where IS ec?
            ep = [p for p in range(n) if has_ec_at_proc(word, cycle, ms, n, p)]
            print(f"    EC procs: {ep}")

# ===== KEY QUESTION: For the failing cycles, is there a (1,1) phase =====
# at ANY ternary proc (not just sandwiched) that gives EC?
print("\n" + "=" * 70)
print("CHECK: (1,1) phase at ANY ternary proc")
print("=" * 70)

n = 7
ms = [2, 2, 2, 3, 2, 3, 3]
max_len = 24

words = enumerate_mover_words(ms, n, max_len)
ternary = [t for t in range(n) if ms[t] == 3]

total = 0
ec_via_any_ternary_phase = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    total += 1
    ell = len(word)

    found = False
    for t in ternary:
        for pv in range(3):
            if phase_gives_ec(word, cycle, ms, n, t, pv):
                found = True
                break
        if found:
            break

    if found:
        ec_via_any_ternary_phase += 1

print(f"Total cycles: {total}")
print(f"EC via (1,1) phase at SOME ternary: {ec_via_any_ternary_phase} ({100*ec_via_any_ternary_phase/total:.1f}%)")
print(f"Not covered: {total - ec_via_any_ternary_phase}")

# ===== What about LARGER phases (2,M) etc? =====
print("\n" + "=" * 70)
print("CHECK: ANY phase at ANY proc gives EC")
print("=" * 70)

ec_via_any_phase_any_proc = 0
not_covered_words = []

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)

    found = False
    for p in range(n):
        pL = (p - 1) % n
        pR = (p + 1) % n
        for pv in range(ms[p]):
            phase_steps = [s for s in range(ell) if cycle[s][p] == pv]
            p_mover = [s for s in phase_steps if word[s] == p]
            p_nonmover = [s for s in phase_steps if word[s] != p]

            if len(p_mover) < 1 or len(p_nonmover) < 1:
                continue

            # Check if any mover context matches any non-mover context in THIS phase
            mover_ctxs = {(cycle[s][pL], cycle[s][p], cycle[s][pR]) for s in p_mover}
            nonmover_ctxs = {(cycle[s][pL], cycle[s][p], cycle[s][pR]) for s in p_nonmover}
            if mover_ctxs & nonmover_ctxs:
                found = True
                break
        if found:
            break

    if found:
        ec_via_any_phase_any_proc += 1
    else:
        not_covered_words.append(word)

print(f"EC via intra-phase match at SOME proc: {ec_via_any_phase_any_proc} ({100*ec_via_any_phase_any_proc/total:.1f}%)")
print(f"Not covered (EC must be cross-phase): {len(not_covered_words)}")

if not_covered_words:
    print(f"\nExamples requiring cross-phase EC:")
    for word in not_covered_words[:3]:
        cycle = build_cycle(ms, n, word)
        ell = len(word)
        fc = Counter(word)
        print(f"  word_len={ell}, fc={dict(fc)}")
        for p in range(n):
            if has_ec_at_proc(word, cycle, ms, n, p):
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
                overlap = mover_ctx & nonmover_ctx
                # Find which phases the overlapping triples come from
                for ctx in overlap:
                    m_phases = set()
                    nm_phases = set()
                    for s in range(ell):
                        if (cycle[s][pL], cycle[s][p], cycle[s][pR]) == ctx:
                            if word[s] == p:
                                m_phases.add(cycle[s][p])
                            else:
                                nm_phases.add(cycle[s][p])
                    print(f"    p={p}: overlap={ctx}, mover_phases={m_phases}, nm_phases={nm_phases}")
