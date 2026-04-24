#!/usr/bin/env python3
"""RA12 Part 7: Check ALL (1,M) phases at ALL ternary processors for EC.

The (1,1) phase at the SANDWICHED ternary gives EC 95.1% of time at n=7.
But what about (1,M) phases at OTHER ternary processors?

Key question: does the EXISTENCE of a (1,1) phase at any sandwiched ternary
guarantee EC at that SPECIFIC processor?

Or better: for EVERY ternary processor t with a (1,M) phase (M>=1),
does the phase give EC at t? (More non-mover steps = more chances for match)

Actually let me step back and check the simplest universal claim:
- EVERY good cycle has EC at some processor
- The (1,1) phase at sandwiched ternary gives EC 95.1%
- The remaining 4.9% have EC elsewhere

The REAL question for the proof: what UNIVERSAL mechanism guarantees EC?

Let me check: for the 336 exception cycles at n=7 (no EC at sandwiched t),
where does EC live? Is it at another ternary?
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

# ===== CHECK: Does the phase distribution at t determine EC? =====
print("=" * 70)
print("PHASE DISTRIBUTION vs EC at each ternary processor")
print("=" * 70)

n = 7
ms = [2, 2, 2, 3, 2, 3, 3]
max_len = 24

words = enumerate_mover_words(ms, n, max_len)
ternary_procs = [p for p in range(n) if ms[p] == 3]
sandwiched = [t for t in range(n)
              if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

total = 0
phase_dist_ec = Counter()  # phase distribution -> has EC
phase_dist_no_ec = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    total += 1
    ell = len(word)
    fc = Counter(word)

    for t in ternary_procs:
        # Phase distribution: (mover_count, nonmover_count) for each phase
        phase_dist = []
        for pv in range(3):
            phase_steps = [s for s in range(ell) if cycle[s][t] == pv]
            m_count = sum(1 for s in phase_steps if word[s] == t)
            nm_count = len(phase_steps) - m_count
            phase_dist.append((m_count, nm_count))
        phase_dist = tuple(sorted(phase_dist))

        has_ec = has_ec_at_proc(word, cycle, ms, n, t)
        if has_ec:
            phase_dist_ec[phase_dist] += 1
        else:
            phase_dist_no_ec[phase_dist] += 1

print(f"\nPhase distributions at ternary procs:")
all_dists = set(phase_dist_ec.keys()) | set(phase_dist_no_ec.keys())
for dist in sorted(all_dists):
    ec = phase_dist_ec.get(dist, 0)
    no_ec = phase_dist_no_ec.get(dist, 0)
    total_d = ec + no_ec
    pct = 100 * ec / total_d if total_d > 0 else 0
    print(f"  {dist}: EC={ec}, no_EC={no_ec}, rate={pct:.1f}%")

# ===== REFINED: For sandwiched t with (1,1,1) phase distribution =====
print("\n" + "=" * 70)
print("Sandwiched t: phase distribution and EC rate")
print("=" * 70)

ec_by_fc = Counter()
no_ec_by_fc = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    fc = Counter(word)

    for t in sandwiched:
        has_ec = has_ec_at_proc(word, cycle, ms, n, t)
        if has_ec:
            ec_by_fc[fc[t]] += 1
        else:
            no_ec_by_fc[fc[t]] += 1

print(f"EC rate by fire count at sandwiched t:")
for fc_val in sorted(set(list(ec_by_fc.keys()) + list(no_ec_by_fc.keys()))):
    ec = ec_by_fc.get(fc_val, 0)
    no_ec = no_ec_by_fc.get(fc_val, 0)
    total_d = ec + no_ec
    print(f"  fc={fc_val}: EC={ec}, no_EC={no_ec}, rate={100*ec/total_d:.1f}%")

# ===== THE 336 EXCEPTIONS at n=7: detailed analysis =====
print("\n" + "=" * 70)
print("THE 336 EXCEPTIONS: No EC at sandwiched t")
print("=" * 70)

exceptions = []
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    fc = Counter(word)

    ec_t = any(has_ec_at_proc(word, cycle, ms, n, t) for t in sandwiched)
    if not ec_t:
        exceptions.append(word)

print(f"Total exceptions: {len(exceptions)}")

# Where is EC for these?
ec_proc_types = Counter()
for word in exceptions:
    cycle = build_cycle(ms, n, word)
    for p in range(n):
        if has_ec_at_proc(word, cycle, ms, n, p):
            ec_proc_types[f"p{p}(m={ms[p]})"] += 1

print(f"EC processor distribution for exceptions:")
for proc, cnt in sorted(ec_proc_types.items(), key=lambda x: -x[1]):
    print(f"  {proc}: {cnt}")

# Phase distribution at t for exceptions
print(f"\nPhase distributions at sandwiched t for exceptions:")
exc_phase_dist = Counter()
for word in exceptions:
    cycle = build_cycle(ms, n, word)
    ell = len(word)
    for t in sandwiched:
        for pv in range(3):
            phase_steps = [s for s in range(ell) if cycle[s][t] == pv]
            m_count = sum(1 for s in phase_steps if word[s] == t)
            nm_count = len(phase_steps) - m_count
        # Full distribution
        dist = []
        for pv in range(3):
            phase_steps = [s for s in range(ell) if cycle[s][t] == pv]
            m_count = sum(1 for s in phase_steps if word[s] == t)
            nm_count = len(phase_steps) - m_count
            dist.append((m_count, nm_count))
        exc_phase_dist[tuple(sorted(dist))] += 1

for dist, cnt in sorted(exc_phase_dist.items(), key=lambda x: -x[1]):
    print(f"  {dist}: {cnt}")

# ===== NEW APPROACH: Check whether CROSS-PHASE EC works =====
print("\n" + "=" * 70)
print("CROSS-PHASE EC: mover in one phase, non-mover in another")
print("=" * 70)

# At proc t: mover contexts from ALL phases vs non-mover from ALL phases
# This is what has_ec_at_proc already checks. So the 336 exceptions have
# no overlap between ANY mover context and ANY non-mover context at t.

# Let me check: for exceptions, what are the mover and non-mover contexts?
for word in exceptions[:3]:
    cycle = build_cycle(ms, n, word)
    ell = len(word)
    for t in sandwiched:
        tL = (t-1)%n
        tR = (t+1)%n
        mover_ctx = set()
        nonmover_ctx = set()
        for s in range(ell):
            ctx = (cycle[s][tL], cycle[s][t], cycle[s][tR])
            if word[s] == t:
                mover_ctx.add(ctx)
            else:
                nonmover_ctx.add(ctx)
        print(f"\n  word_len={ell}, t={t}:")
        print(f"    Mover contexts: {sorted(mover_ctx)}")
        print(f"    Non-mover contexts: {sorted(nonmover_ctx)}")
        print(f"    Overlap: {mover_ctx & nonmover_ctx}")

# ===== CHECK: with 3-consecutive binary, does the problem even have exceptions? =====
print("\n" + "=" * 70)
print("CHECK: Different architectures")
print("=" * 70)

# ms=[2,2,2,3,3,2,3] — different placement
for n, ms, max_len, label in [
    (7, [2,2,2,3,3,2,3], 24, "n=7: [2,2,2,3,3,2,3]"),
    (7, [2,2,2,3,2,3,3], 24, "n=7: [2,2,2,3,2,3,3]"),
    # (9, [2,2,2,3,2,3,3,3,3], 30, "n=9: too slow"),
]:
    words = enumerate_mover_words(ms, n, max_len)
    sandwiched_local = [t for t in range(n)
                  if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

    total_c = 0
    ec_t_c = 0
    ec_any_c = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        total_c += 1

        ec_t = any(has_ec_at_proc(word, cycle, ms, n, t) for t in sandwiched_local)
        if ec_t:
            ec_t_c += 1

        ec_any = any(has_ec_at_proc(word, cycle, ms, n, p) for p in range(n))
        if ec_any:
            ec_any_c += 1

    print(f"\n{label}: {total_c} cycles")
    print(f"  EC at sandwiched t: {ec_t_c} ({100*ec_t_c/max(1,total_c):.1f}%)")
    print(f"  EC anywhere: {ec_any_c} ({100*ec_any_c/max(1,total_c):.1f}%)")
    if ec_any_c < total_c:
        print(f"  *** {total_c - ec_any_c} CYCLES WITH NO EC ANYWHERE ***")
