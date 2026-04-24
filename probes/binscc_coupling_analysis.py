#!/usr/bin/env python3
"""Analyze the coupling structure that prevents all-ternary FR failure.

Key insight: on n=6 alternating ring, B-T alternate → walk alternates binary/ternary.
This forces structural constraints on displacement patterns.

Questions:
1. What are the firing distributions in wrap-adjacent cycles?
2. Does the 2-round ternary (6 firings) always have FR?
3. What coupling through shared binaries prevents all-fail?
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

def has_full_return_at(ms, n, word, cycle, t):
    ell = len(cycle)
    bL = (t - 1) % n
    bR = (t + 1) % n
    for k in range(ms[t]):
        ps = [s for s in range(ell) if cycle[s][t] == k]
        if len(ps) <= 1:
            continue
        mlrs = set()
        nmlrs = set()
        for s in ps:
            lr = (cycle[s][bL], cycle[s][bR])
            if word[s] == t:
                mlrs.add(lr)
            else:
                nmlrs.add(lr)
        if mlrs & nmlrs:
            return True
    return False

print("=" * 70)
print("COUPLING ANALYSIS: WHY ALL-TERNARY-FAIL IS IMPOSSIBLE")
print("=" * 70)

# n=6 alternating
n, ms = 6, [2, 3, 2, 3, 2, 3]
tern = [1, 3, 5]
binn = [0, 2, 4]

t0 = time.time()
words = enumerate_mover_words(ms, n, 24)
print(f"\nn={n} ms={ms}: {len(words)} words")

# PART 1: Firing distributions for wrap-adjacent cycles
print(f"\n{'='*60}")
print("PART 1: FIRING DISTRIBUTIONS")

wrap_lens = Counter()
wrap_fire_dists = Counter()
wrap_fire_tern = Counter()  # (t1_fires, t3_fires, t5_fires)
wrap_fire_bin = Counter()   # (b0_fires, b2_fires, b4_fires)
total_wrap = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None:
        continue
    if not is_wrap_adjacent(word, n):
        continue
    total_wrap += 1
    ell = len(word)
    wrap_lens[ell] += 1

    # Count firings per proc
    fc = Counter(word)
    t_fires = tuple(fc.get(t, 0) for t in tern)
    b_fires = tuple(fc.get(b, 0) for b in binn)
    wrap_fire_tern[t_fires] += 1
    wrap_fire_bin[b_fires] += 1

print(f"  Wrap-adjacent: {total_wrap} ({time.time()-t0:.1f}s)")
print(f"\n  Cycle lengths: {dict(sorted(wrap_lens.items()))}")
print(f"\n  Ternary firing distributions (P1,P3,P5):")
for dist, cnt in sorted(wrap_fire_tern.items(), key=lambda x: -x[1]):
    print(f"    {dist}: {cnt} ({100*cnt/total_wrap:.1f}%)")
print(f"\n  Binary firing distributions (P0,P2,P4):")
for dist, cnt in sorted(wrap_fire_bin.items(), key=lambda x: -x[1]):
    print(f"    {dist}: {cnt} ({100*cnt/total_wrap:.1f}%)")

# PART 2: B-T alternation verification
print(f"\n{'='*60}")
print("PART 2: B-T ALTERNATION CHECK")
non_alt = 0
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None:
        continue
    if not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    for i in range(ell):
        p1, p2 = word[i], word[(i+1) % ell]
        if (p1 in tern) == (p2 in tern):  # same type consecutive
            non_alt += 1
            break

print(f"  Cycles with same-type consecutive firings: {non_alt}/{total_wrap}")

# PART 3: FR at 2-round ternary
print(f"\n{'='*60}")
print("PART 3: FULL RETURN AT MULTI-ROUND TERNARY")

multi_round_fr = Counter()  # (has_fr,) per multi-round ternary
multi_round_count = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None:
        continue
    if not is_wrap_adjacent(word, n):
        continue
    fc = Counter(word)
    for t in tern:
        if fc[t] > ms[t]:  # multi-round
            multi_round_count += 1
            fr = has_full_return_at(ms, n, word, cycle, t)
            multi_round_fr[fr] += 1

print(f"  Multi-round ternary instances: {multi_round_count}")
print(f"  FR at multi-round: {multi_round_fr}")

# PART 4: Which ternary fails FR most often?
print(f"\n{'='*60}")
print("PART 4: PER-TERNARY FR FAILURE RATES")

per_tern_fail = {t: 0 for t in tern}
per_tern_total = {t: 0 for t in tern}
fail_combo = Counter()  # which subsets of ternary fail

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None:
        continue
    if not is_wrap_adjacent(word, n):
        continue
    fails = []
    for t in tern:
        per_tern_total[t] += 1
        if not has_full_return_at(ms, n, word, cycle, t):
            per_tern_fail[t] += 1
            fails.append(t)
    fail_combo[tuple(fails)] += 1

for t in tern:
    pct = 100 * per_tern_fail[t] / per_tern_total[t] if per_tern_total[t] > 0 else 0
    print(f"  P{t}: {per_tern_fail[t]}/{per_tern_total[t]} FR-fail ({pct:.2f}%)")

print(f"\n  FR failure combinations:")
for combo, cnt in sorted(fail_combo.items(), key=lambda x: -x[1]):
    pct = 100 * cnt / total_wrap
    label = "none" if not combo else "+".join(f"P{t}" for t in combo)
    print(f"    {label}: {cnt} ({pct:.1f}%)")

# PART 5: Coupling through shared binaries
print(f"\n{'='*60}")
print("PART 5: BINARY PHASE COUPLING")
print("When binary b fires, it sees (c[t_left], c[t_right]) of its ternary neighbors.")
print("For all-ternary-fail, b's 2+ firings must hit different phases of BOTH neighbors.")

coupling_possible = Counter()
coupling_data = []
sample = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None:
        continue
    if not is_wrap_adjacent(word, n):
        continue

    # For each binary, get the (t_left_phase, t_right_phase) at each firing
    fc = Counter(word)
    ell = len(word)
    for b in binn:
        tL = (b - 1) % n  # left ternary neighbor
        tR = (b + 1) % n  # right ternary neighbor
        # Get phases at each binary firing
        fire_phases = []
        for s in range(ell):
            if word[s] == b:
                fire_phases.append((cycle[s][tL], cycle[s][tR]))
        # Check separation
        tL_phases = set(p[0] for p in fire_phases)
        tR_phases = set(p[1] for p in fire_phases)
        both_sep = len(tL_phases) >= 2 and len(tR_phases) >= 2
        coupling_possible[(b, both_sep)] += 1

        if sample < 5 and fc[b] == 2:
            print(f"    B{b}: fires={fire_phases}, tL_sep={len(tL_phases)>=2}, tR_sep={len(tR_phases)>=2}")
            sample += 1

print(f"\n  Binary coupling (both-separated means b's firings hit ≥2 phases of BOTH neighbors):")
for (b, sep), cnt in sorted(coupling_possible.items()):
    pct = 100 * cnt / total_wrap
    print(f"    B{b} both-separated={sep}: {cnt} ({pct:.1f}%)")

# PART 6: Joint coupling — can all 3 binaries be both-separated simultaneously?
print(f"\n{'='*60}")
print("PART 6: JOINT COUPLING")

all_sep = 0
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None:
        continue
    if not is_wrap_adjacent(word, n):
        continue
    ell = len(word)

    all_binary_sep = True
    for b in binn:
        tL = (b - 1) % n
        tR = (b + 1) % n
        fire_phases = []
        for s in range(ell):
            if word[s] == b:
                fire_phases.append((cycle[s][tL], cycle[s][tR]))
        tL_phases = set(p[0] for p in fire_phases)
        tR_phases = set(p[1] for p in fire_phases)
        if len(tL_phases) < 2 or len(tR_phases) < 2:
            all_binary_sep = False
            break
    if all_binary_sep:
        all_sep += 1

print(f"  All 3 binaries both-separated: {all_sep}/{total_wrap} ({100*all_sep/total_wrap:.1f}%)")
print(f"  → If 0%: proves all-ternary-fail impossible via coupling!")
print(f"  → If >0%: coupling alone insufficient, need additional constraint")

# PART 7: Check if ternary with single-round always has FR
print(f"\n{'='*60}")
print("PART 7: SINGLE-ROUND TERNARY FR")
single_fr = 0
single_total = 0
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None:
        continue
    if not is_wrap_adjacent(word, n):
        continue
    fc = Counter(word)
    for t in tern:
        if fc[t] == ms[t]:  # exactly one round
            single_total += 1
            if has_full_return_at(ms, n, word, cycle, t):
                single_fr += 1

print(f"  Single-round ternary: {single_fr}/{single_total} have FR ({100*single_fr/single_total:.1f}%)")
print(f"  Single-round without FR: {single_total - single_fr}")

elapsed = time.time() - t0
print(f"\nTotal time: {elapsed:.1f}s")
sys.stdout.flush()
