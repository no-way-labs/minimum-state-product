#!/usr/bin/env python3
"""RA12 Part 4: Investigate EC at the sandwiched ternary t.

Finding: EC at all-binary-context q FAILS for Case 2 (66% of instances at n=7).
EC at sandwiched ternary t works for 99.3%.

Questions:
1. The 48 cycles (0.7%) without EC at t: what ARE they? Where is their EC?
2. Does EC at t come from the (1,1) phase directly?
3. Can we use the (1,1) phase structure to PROVE EC at t?
4. What's the mechanism for EC at t?
5. Check n=9 to see if t-EC remains near-universal.

CRITICAL: Maybe the right approach is:
- The (1,1) phase at t guarantees EC at t (not at q)
- Prove this directly using the (1,1) phase structure
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

def ec_overlaps_at(word, cycle, ms, n, p):
    """Return the set of overlapping (L,S,R) triples at processor p."""
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
    return mover_ctx & nonmover_ctx

# ===== (1,1) PHASE EC MECHANISM =====
print("=" * 70)
print("(1,1) PHASE EC MECHANISM AT SANDWICHED TERNARY t")
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
    ec_at_t_total = 0
    no_ec_at_t = []

    # For cycles with EC at t: analyze WHICH (1,1) phase creates the overlap
    phase_creates_ec = Counter()  # which phase value creates EC at t
    ec_triple_types = Counter()

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        total += 1

        ell = len(word)
        fc = Counter(word)

        for t in sandwiched:
            tL = (t - 1) % n
            tR = (t + 1) % n

            overlaps = ec_overlaps_at(word, cycle, ms, n, t)
            if overlaps:
                ec_at_t_total += 1

                # Which phase does the overlap belong to?
                for (L, S, R) in overlaps:
                    phase_creates_ec[S] += 1
                    ec_triple_types[(L, S, R)] += 1
            else:
                no_ec_at_t.append((word, t))

    print(f"Total cycles: {total}")
    print(f"EC at sandwiched t: {ec_at_t_total}/{total} ({100*ec_at_t_total/total:.1f}%)")
    print(f"No EC at t: {len(no_ec_at_t)}")
    print(f"\nPhase value creating EC: {dict(phase_creates_ec)}")
    print(f"EC triple types (L,S,R): {dict(sorted(ec_triple_types.items(), key=lambda x: -x[1]))}")

    # Analyze the (1,1) phase structure in detail
    print(f"\nDetailed (1,1) phase analysis:")

    # For the first N cycles, show the (1,1) phase structure
    shown = 0
    for word in words:
        if shown >= 3:
            break
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
                    # This is a (1,1) phase
                    sm = t_mover[0]
                    snm = t_nonmover[0]  # First non-mover step

                    ctx_mover = (cycle[sm][tL], cycle[sm][t], cycle[sm][tR])
                    ctx_nonmover = (cycle[snm][tL], cycle[snm][t], cycle[snm][tR])

                    if shown < 3:
                        print(f"\n  Cycle #{shown+1}, t={t}, phase={pv}:")
                        print(f"    Mover step s={sm}: ctx={ctx_mover}, mover={word[sm]}")
                        for s in t_nonmover:
                            ctx = (cycle[s][tL], cycle[s][t], cycle[s][tR])
                            print(f"    Non-mover step s={s}: ctx={ctx}, mover={word[s]}")

                        # Is the mover context also a non-mover context?
                        nm_ctxs = {(cycle[s][tL], cycle[s][t], cycle[s][tR]) for s in t_nonmover}
                        if ctx_mover in nm_ctxs:
                            print(f"    *** EC from (1,1) phase: mover ctx {ctx_mover} matches non-mover ***")
                        else:
                            print(f"    No direct EC from this (1,1) phase")
                            print(f"    Mover L,R = ({ctx_mover[0]}, {ctx_mover[2]})")
                            print(f"    Non-mover L,R = {[(cycle[s][tL], cycle[s][tR]) for s in t_nonmover]}")

                    shown += 1
                    break

    # ===== CRITICAL: Analyze why (1,1) phase gives EC at t =====
    print(f"\n{'='*70}")
    print(f"WHY does (1,1) phase give EC at t?")
    print(f"{'='*70}")

    # In a (1,1) phase at t with value v:
    # - 1 mover step: t fires, context (L_m, v, R_m), value goes v -> v+1
    # - 1+ non-mover steps: t doesn't fire, context (L_nm, v, R_nm)
    # EC requires: (L_m, v, R_m) appears at some non-mover step
    # i.e., at some non-mover step, t's neighbors have values (L_m, R_m)

    # Key: t's neighbors are BINARY (m_{tL} = m_{tR} = 2)
    # So L_m, R_m in {0,1} and L_nm, R_nm in {0,1}

    phase_ec_direct = 0    # EC directly from (1,1) phase
    phase_ec_indirect = 0  # EC from another phase
    phase_no_ec_but_other = 0
    phase_match_analysis = Counter()  # What (L_m,R_m) vs (L_nm,R_nm) combinations appear

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
                    sm = t_mover[0]
                    ctx_m = (cycle[sm][tL], cycle[sm][t], cycle[sm][tR])

                    nm_ctxs = {(cycle[s][tL], cycle[s][t], cycle[s][tR]) for s in t_nonmover}

                    if ctx_m in nm_ctxs:
                        phase_ec_direct += 1
                    else:
                        # Check if EC exists from OTHER phases
                        if has_ec_at_proc(word, cycle, ms, n, t):
                            phase_ec_indirect += 1
                        else:
                            phase_no_ec_but_other += 1

                    # Track L,R match pattern
                    lr_m = (ctx_m[0], ctx_m[2])
                    lr_nms = {(cycle[s][tL], cycle[s][tR]) for s in t_nonmover}
                    if lr_m in lr_nms:
                        phase_match_analysis['LR_match'] += 1
                    else:
                        phase_match_analysis['LR_mismatch'] += 1
                        # What pairs appear?
                        phase_match_analysis[f'mover_LR={lr_m}_nm_LRs={sorted(lr_nms)}'] += 1

    print(f"\n(1,1) phase EC analysis:")
    print(f"  Direct EC from (1,1) phase: {phase_ec_direct}")
    print(f"  EC at t from other phase: {phase_ec_indirect}")
    print(f"  No EC at t at all: {phase_no_ec_but_other}")

    print(f"\nLR match analysis:")
    for key, cnt in sorted(phase_match_analysis.items(), key=lambda x: -x[1]):
        print(f"  {key}: {cnt}")

# ===== 48 EXCEPTIONAL CYCLES =====
print("\n" + "=" * 70)
print("THE 48 EXCEPTIONS: cycles with (1,1) phase but no EC at t")
print("=" * 70)

n = 7
ms = [2, 2, 2, 3, 2, 3, 3]
max_len = 24

words = enumerate_mover_words(ms, n, max_len)
sandwiched = [t for t in range(n)
              if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

exceptions = []
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    ell = len(word)
    fc = Counter(word)

    has_11 = False
    for t in sandwiched:
        for pv in range(3):
            phase_steps = [s for s in range(ell) if cycle[s][t] == pv]
            t_mover = [s for s in phase_steps if word[s] == t]
            t_nonmover = [s for s in phase_steps if word[s] != t]
            if len(t_mover) == 1 and len(t_nonmover) >= 1:
                has_11 = True
                break
        if has_11:
            break
    if not has_11:
        continue

    ec_t = any(has_ec_at_proc(word, cycle, ms, n, t) for t in sandwiched)
    if not ec_t:
        exceptions.append(word)

print(f"Total exceptions: {len(exceptions)}")

if exceptions:
    # Analyze first few
    for idx, word in enumerate(exceptions[:5]):
        cycle = build_cycle(ms, n, word)
        ell = len(word)
        fc = Counter(word)
        print(f"\n  Exception #{idx+1}: word_len={ell}, fc={dict(fc)}")

        for t in sandwiched:
            tL = (t - 1) % n
            tR = (t + 1) % n
            print(f"    t={t} (sandwiched ternary):")
            for pv in range(3):
                phase_steps = [s for s in range(ell) if cycle[s][t] == pv]
                t_mover = [s for s in phase_steps if word[s] == t]
                t_nonmover = [s for s in phase_steps if word[s] != t]
                print(f"      phase={pv}: mover_steps={len(t_mover)}, nonmover_steps={len(t_nonmover)}")
                for s in t_mover:
                    ctx = (cycle[s][tL], cycle[s][t], cycle[s][tR])
                    print(f"        MOVER s={s}: ctx={ctx}")
                for s in t_nonmover[:3]:
                    ctx = (cycle[s][tL], cycle[s][t], cycle[s][tR])
                    print(f"        non-m s={s}: ctx={ctx}, mover={word[s]}")

        # Where IS ec?
        ec_procs = [p for p in range(n) if has_ec_at_proc(word, cycle, ms, n, p)]
        print(f"    EC at procs: {ec_procs}")
        for p in ec_procs[:2]:
            overlaps = ec_overlaps_at(word, cycle, ms, n, p)
            print(f"      p={p}: overlapping triples = {overlaps}")
