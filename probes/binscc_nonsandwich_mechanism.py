#!/usr/bin/env python3
"""Investigate WHY non-sandwiched ternary always has entry conflict at n=7.

Architecture: n=7, ms=[2,3,2,3,2,3,3]
Ring: P0(2)-P1(3)-P2(2)-P3(3)-P4(2)-P5(3)-P6(3)
Sandwiched ternary: P1 (btwn P0,P2), P3 (btwn P2,P4)
Non-sandwiched: P5 (btwn P4=bin,P6=tern), P6 (btwn P5=tern,P0=bin)

When sandwiched FR fails (1,208 cycles), P5 and P6 ALWAYS rescue.
WHY? What mechanism drives entry conflict at non-sandwiched ternary?
"""
import sys, time
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

def has_fr_at(ms, n, word, cycle, p):
    """Full (L,R)-Return at processor p: same (c[bL],c[p],c[bR]) at mover and nonmover."""
    ell = len(word)
    bL = (p - 1) % n
    bR = (p + 1) % n
    mover_lsr = set()
    nonmover_lsr = set()
    for s in range(ell):
        lsr = (cycle[s][bL], cycle[s][p], cycle[s][bR])
        if word[s] == p:
            mover_lsr.add(lsr)
        else:
            nonmover_lsr.add(lsr)
    return bool(mover_lsr & nonmover_lsr)

def get_fr_details(ms, n, word, cycle, p):
    """Get detailed FR info: which phases have conflict, mechanism."""
    ell = len(word)
    bL = (p - 1) % n
    bR = (p + 1) % n

    # Group by phase of p
    phase_info = {}
    for k in range(ms[p]):
        steps = [s for s in range(ell) if cycle[s][p] == k]
        mover_steps = [s for s in steps if word[s] == p]
        nonmover_steps = [s for s in steps if word[s] != p]

        # (bL, bR) values at mover and nonmover steps
        mover_lr = set()
        nonmover_lr = set()
        for s in mover_steps:
            mover_lr.add((cycle[s][bL], cycle[s][bR]))
        for s in nonmover_steps:
            nonmover_lr.add((cycle[s][bL], cycle[s][bR]))

        # Firing counts
        bLf = sum(1 for s in steps if word[s] == bL)
        bRf = sum(1 for s in steps if word[s] == bR)

        overlap = mover_lr & nonmover_lr

        phase_info[k] = {
            'dur': len(steps),
            'mover_count': len(mover_steps),
            'nonmover_count': len(nonmover_steps),
            'bLf': bLf, 'bRf': bRf,
            'mover_lr': mover_lr,
            'nonmover_lr': nonmover_lr,
            'overlap': overlap,
            'has_fr': bool(overlap)
        }
    return phase_info

print("=" * 70)
print("NON-SANDWICHED TERNARY ENTRY CONFLICT MECHANISM (n=7)")
print("=" * 70)

n, ms = 7, [2, 3, 2, 3, 2, 3, 3]
max_len = 28

t0 = time.time()
words = enumerate_mover_words(ms, n, max_len)
print(f"Words: {len(words)} ({time.time()-t0:.1f}s)")

# Identify sandwiched and non-sandwiched ternary
sandwiched = [1, 3]  # between binary neighbors
nonsandwiched = [5, 6]  # P5: btwn P4(bin), P6(tern); P6: btwn P5(tern), P0(bin)

# PART 1: Overall entry conflict rates
print(f"\n{'='*60}")
print("PART 1: ENTRY CONFLICT AT EACH PROCESSOR")

total = 0
ec_by_proc = Counter()
ec_ternary_only = 0
sandwiched_fr = Counter()  # which sandwiched have FR

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    total += 1

    ec_procs = set()
    for p in range(n):
        if has_fr_at(ms, n, word, cycle, p):
            ec_procs.add(p)
            ec_by_proc[p] += 1

    # Check ternary-only coverage
    tern_ec = ec_procs & {1, 3, 5, 6}
    if tern_ec:
        ec_ternary_only += 1

    # Track sandwiched FR
    for t in sandwiched:
        if t in ec_procs:
            sandwiched_fr[t] += 1

print(f"Total wrap-adjacent cycles: {total}")
for p in range(n):
    rate = 100 * ec_by_proc.get(p, 0) / total if total > 0 else 0
    ptype = "bin" if ms[p] == 2 else ("sand" if p in sandwiched else "nsand")
    print(f"  P{p} [ms={ms[p]}, {ptype}]: {ec_by_proc.get(p,0)}/{total} ({rate:.1f}%)")
print(f"  Ternary only: {ec_ternary_only}/{total} ({100*ec_ternary_only/total:.1f}%)")

# PART 2: When sandwiched FR fails, analyze non-sandwiched
print(f"\n{'='*60}")
print("PART 2: SANDWICHED FR FAIL → NON-SANDWICHED RESCUE")

sw_fail_count = 0
ns_rescue = Counter()
ns_both_rescue = 0
ns_p5_only = 0
ns_p6_only = 0
ns_neither = 0

# Phase mechanism at P5 when it rescues
p5_rescue_mechanism = Counter()
p5_rescue_phase_dur = Counter()
p5_rescue_bLf_bRf = Counter()
p5_rescue_both_return = 0  # bLf % 2 == 0 and bRf % 3 == 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    # Check sandwiched FR
    sw_fr = [has_fr_at(ms, n, word, cycle, t) for t in sandwiched]
    if all(sw_fr):
        continue  # sandwiched covers it

    sw_fail_count += 1

    # Check non-sandwiched
    p5_ec = has_fr_at(ms, n, word, cycle, 5)
    p6_ec = has_fr_at(ms, n, word, cycle, 6)

    if p5_ec and p6_ec:
        ns_both_rescue += 1
    elif p5_ec:
        ns_p5_only += 1
    elif p6_ec:
        ns_p6_only += 1
    else:
        ns_neither += 1

    ns_rescue[5] += int(p5_ec)
    ns_rescue[6] += int(p6_ec)

    # Analyze P5's mechanism when it rescues
    if p5_ec:
        details = get_fr_details(ms, n, word, cycle, 5)
        for k, info in details.items():
            if info['has_fr']:
                p5_rescue_phase_dur[info['dur']] += 1
                p5_rescue_bLf_bRf[(info['bLf'], info['bRf'])] += 1
                # Generalized return: bLf even AND bRf % 3 == 0
                if info['bLf'] % 2 == 0 and info['bRf'] % ms[(5+1)%n] == 0:
                    p5_rescue_both_return += 1
                    p5_rescue_mechanism['both_return'] += 1
                elif info['bLf'] % 2 == 0:
                    p5_rescue_mechanism['bL_return_only'] += 1
                elif info['bRf'] % ms[(5+1)%n] == 0:
                    p5_rescue_mechanism['bR_return_only'] += 1
                else:
                    p5_rescue_mechanism['value_match'] += 1

print(f"Sandwiched FR fails: {sw_fail_count}")
print(f"  P5 rescues: {ns_rescue.get(5,0)}/{sw_fail_count}")
print(f"  P6 rescues: {ns_rescue.get(6,0)}/{sw_fail_count}")
print(f"  Both rescue: {ns_both_rescue}")
print(f"  P5 only: {ns_p5_only}")
print(f"  P6 only: {ns_p6_only}")
print(f"  Neither (BUG!): {ns_neither}")

print(f"\n  P5 rescue mechanism (per-phase):")
for mech, cnt in sorted(p5_rescue_mechanism.items(), key=lambda x: -x[1]):
    print(f"    {mech}: {cnt}")

print(f"\n  P5 rescue phase durations:")
for dur, cnt in sorted(p5_rescue_phase_dur.items()):
    print(f"    dur={dur}: {cnt}")

print(f"\n  P5 rescue (bLf, bRf) patterns:")
for (bLf, bRf), cnt in sorted(p5_rescue_bLf_bRf.items(), key=lambda x: -x[1])[:15]:
    bL_ret = "even" if bLf % 2 == 0 else "odd"
    bR_ret = f"≡0 mod {ms[6]}" if bRf % ms[6] == 0 else f"≡{bRf % ms[6]} mod {ms[6]}"
    print(f"    bLf={bLf}({bL_ret}), bRf={bRf}({bR_ret}): {cnt}")

# PART 3: Does entry conflict ALWAYS come from ternary? Or do binary procs matter?
print(f"\n{'='*60}")
print("PART 3: TERNARY-ONLY VS BINARY NEEDED")

ternary_covers = 0
binary_needed = 0
binary_needed_examples = []

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    tern_ec = any(has_fr_at(ms, n, word, cycle, t) for t in [1, 3, 5, 6])
    if tern_ec:
        ternary_covers += 1
    else:
        binary_needed += 1
        if len(binary_needed_examples) < 3:
            binary_needed_examples.append(word[:20])

print(f"Ternary covers: {ternary_covers}/{total} ({100*ternary_covers/total:.1f}%)")
print(f"Binary needed: {binary_needed}/{total}")
if binary_needed_examples:
    print(f"Examples needing binary:")
    for ex in binary_needed_examples:
        print(f"  {list(ex)}...")

# PART 4: Generalized FR at non-sandwiched — the "mod m" return
# At P5: bL=P4(mod 2), bR=P6(mod 3).
# "Return" = bLf ≡ 0 mod 2 AND bRf ≡ 0 mod 3
# How often does non-sandwiched ternary have this vs value-match?
print(f"\n{'='*60}")
print("PART 4: GENERALIZED RETURN VS VALUE MATCH AT P5 (ALL CYCLES)")

p5_all_mechanisms = Counter()
p5_phases_total = 0
p5_phases_fr = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    details = get_fr_details(ms, n, word, cycle, 5)
    for k, info in details.items():
        p5_phases_total += 1
        if info['has_fr']:
            p5_phases_fr += 1
            bLf, bRf = info['bLf'], info['bRf']
            # Classify mechanism
            bL_ret = bLf % 2 == 0
            bR_ret = bRf % ms[6] == 0
            if bL_ret and bR_ret:
                p5_all_mechanisms['both_return'] += 1
            elif bLf == 0 and bRf >= 2:
                p5_all_mechanisms['osb_bR'] += 1
            elif bRf == 0 and bLf >= 2:
                p5_all_mechanisms['osb_bL'] += 1
            elif bL_ret:
                p5_all_mechanisms['bL_return_partial'] += 1
            elif bR_ret:
                p5_all_mechanisms['bR_return_partial'] += 1
            else:
                p5_all_mechanisms['value_match'] += 1

print(f"P5 phases: {p5_phases_total}, with FR: {p5_phases_fr} ({100*p5_phases_fr/p5_phases_total:.1f}%)")
print(f"Mechanism breakdown:")
for mech, cnt in sorted(p5_all_mechanisms.items(), key=lambda x: -x[1]):
    print(f"  {mech}: {cnt} ({100*cnt/p5_phases_fr:.1f}%)")

# PART 5: Context budget analysis
# At P5: context space = m_4 × m_5 × m_6 = 2 × 3 × 3 = 18
# At sandwiched P1: context space = m_0 × m_1 × m_2 = 2 × 3 × 2 = 12
# Larger context at non-sandwiched makes overlap HARDER per phase
# But does the overall cycle structure compensate?
print(f"\n{'='*60}")
print("PART 5: CONTEXT SPACE ANALYSIS")

p5_context_space = ms[4] * ms[5] * ms[6]  # 2*3*3=18
p1_context_space = ms[0] * ms[1] * ms[2]  # 2*3*2=12

print(f"P1 (sandwiched) context space: {p1_context_space}")
print(f"P5 (non-sandwiched) context space: {p5_context_space}")

# For each cycle, count distinct mover vs nonmover contexts at P5
p5_mover_ctx_sizes = Counter()
p5_nonmover_ctx_sizes = Counter()
p5_mover_nonmover_gap = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    ell = len(word)
    m_ctx = set()
    nm_ctx = set()
    for s in range(ell):
        ctx = (cycle[s][4], cycle[s][5], cycle[s][6])
        if word[s] == 5:
            m_ctx.add(ctx)
        else:
            nm_ctx.add(ctx)

    p5_mover_ctx_sizes[len(m_ctx)] += 1
    p5_nonmover_ctx_sizes[len(nm_ctx)] += 1
    gap = len(m_ctx) + len(nm_ctx) - p5_context_space
    p5_mover_nonmover_gap[gap] += 1

print(f"\nP5 distinct mover context sizes:")
for sz, cnt in sorted(p5_mover_ctx_sizes.items()):
    print(f"  |M|={sz}: {cnt}")

print(f"\nP5 distinct nonmover context sizes:")
for sz, cnt in sorted(p5_nonmover_ctx_sizes.items()):
    print(f"  |N|={sz}: {cnt}")

print(f"\n|M|+|N|-{p5_context_space} (positive → forced overlap):")
for gap, cnt in sorted(p5_mover_nonmover_gap.items()):
    print(f"  gap={gap}: {cnt}")

elapsed = time.time() - t0
print(f"\nTotal: {elapsed:.1f}s")
