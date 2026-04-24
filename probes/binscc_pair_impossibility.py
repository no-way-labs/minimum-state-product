#!/usr/bin/env python3
"""Investigate why no pair of ternary procs can simultaneously fail Full Return.

At n=6 alternating, firing dist is always (3,3,6) for ternary.
The 6-time ternary connects the other two.

Key questions:
1. When P1 fails FR, what's the displacement pattern at P3 and P5?
2. Is there a parity/winding constraint that forces FR at the partner?
3. Check the DIRECTION structure: how does the walk traverse the ring?
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

def get_displacement_detail(ms, n, word, cycle, t):
    """Get full displacement info for ternary t."""
    ell = len(cycle)
    bL = (t - 1) % n
    bR = (t + 1) % n
    fc = Counter(word)
    rounds = fc[t] // ms[t]

    # Gather mover info per (round, phase)
    mover_data = {}  # (round, phase) -> (c[bL], c[bR])
    round_count = {}
    for s in range(ell):
        if word[s] == t:
            k = cycle[s][t]
            r = round_count.get(k, 0)
            mover_data[(r, k)] = (cycle[s][bL], cycle[s][bR])
            round_count[k] = r + 1

    return {
        'fires': fc[t],
        'rounds': rounds,
        'bL': bL,
        'bR': bR,
        'mover_data': mover_data,
    }

print("=" * 70)
print("PAIR-IMPOSSIBILITY ANALYSIS")
print("=" * 70)

n, ms = 6, [2, 3, 2, 3, 2, 3]
tern = [1, 3, 5]

t0 = time.time()
words = enumerate_mover_words(ms, n, 24)

# PART 1: When one ternary fails, analyze the other two
print("\nPART 1: DISPLACEMENT PATTERNS WHEN ONE TERNARY FAILS FR")

fail_partner_disp = Counter()
fail_partner_detail = []

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    fc = Counter(word)
    fr_status = {t: has_full_return_at(ms, n, word, cycle, t) for t in tern}

    fails = [t for t in tern if not fr_status[t]]
    if len(fails) != 1:
        continue

    t_fail = fails[0]
    # Which ternary is the 6-time one?
    t6 = max(tern, key=lambda t: fc[t])

    for t_ok in tern:
        if t_ok == t_fail:
            continue
        # Get displacement info
        detail = get_displacement_detail(ms, n, word, cycle, t_ok)

        # Check what kind of FR t_ok has
        bL = (t_ok - 1) % n
        bR = (t_ok + 1) % n
        ell = len(cycle)

        fr_phases = []  # which phases have mover-nonmover overlap
        for k in range(ms[t_ok]):
            ps = [s for s in range(ell) if cycle[s][t_ok] == k]
            if len(ps) <= 1:
                continue
            mlrs = set()
            nmlrs = set()
            for s in ps:
                lr = (cycle[s][bL], cycle[s][bR])
                if word[s] == t_ok:
                    mlrs.add(lr)
                else:
                    nmlrs.add(lr)
            if mlrs & nmlrs:
                fr_phases.append(k)

        tag = f"fail=P{t_fail},ok=P{t_ok}"
        is_6time = "6x" if fc[t_ok] > ms[t_ok] else "3x"
        fail_partner_disp[(tag, is_6time, len(fr_phases))] += 1

        if len(fail_partner_detail) < 5:
            fail_partner_detail.append({
                'fail': t_fail, 'ok': t_ok,
                't6': t6, 'fires': fc[t_ok],
                'fr_phases': fr_phases,
            })

for key, cnt in sorted(fail_partner_disp.items()):
    print(f"  {key}: {cnt}")

print(f"\n  Sample details:")
for d in fail_partner_detail:
    print(f"    fail=P{d['fail']}, ok=P{d['ok']}, "
          f"fires={d['fires']}, t6=P{d['t6']}, fr_phases={d['fr_phases']}")

# PART 2: Walk direction analysis
print(f"\n{'='*60}")
print("PART 2: WALK DIRECTION (WINDING) ANALYSIS")

winding_dist = Counter()
winding_vs_fail = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)

    # Compute winding number
    total_disp = 0
    for i in range(ell):
        step = (word[(i+1) % ell] - word[i]) % n
        if step == 1:
            total_disp += 1
        elif step == n - 1:
            total_disp -= 1

    winding = total_disp // n  # should be exact
    winding_dist[winding] += 1

    fr_status = {t: has_full_return_at(ms, n, word, cycle, t) for t in tern}
    fails = [t for t in tern if not fr_status[t]]
    winding_vs_fail[(winding, len(fails))] += 1

print(f"  Winding number distribution:")
for w, cnt in sorted(winding_dist.items()):
    print(f"    winding={w}: {cnt}")

print(f"\n  Winding vs FR failures:")
for (w, nf), cnt in sorted(winding_vs_fail.items()):
    print(f"    winding={w}, num_fail={nf}: {cnt}")

# PART 3: Phase gap structure at failing ternary
print(f"\n{'='*60}")
print("PART 3: PHASE GAP STRUCTURE")

# For the failing ternary, what are the gaps between its 3 firings?
# And how do the binary firings distribute in these gaps?

gap_patterns = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)

    fc = Counter(word)
    fr_status = {t: has_full_return_at(ms, n, word, cycle, t) for t in tern}
    fails = [t for t in tern if not fr_status[t]]
    if len(fails) != 1:
        continue

    t_fail = fails[0]
    if fc[t_fail] > ms[t_fail]:
        continue  # skip multi-round failures for now

    bL = (t_fail - 1) % n
    bR = (t_fail + 1) % n

    # Find firing positions of t_fail
    t_pos = [s for s in range(ell) if word[s] == t_fail]
    assert len(t_pos) == 3

    # Gaps between firings
    gaps = []
    for j in range(3):
        s1 = t_pos[j]
        s2 = t_pos[(j+1) % 3]
        gap_len = (s2 - s1) % ell
        # Count bL and bR firings in this gap
        bL_count = 0
        bR_count = 0
        for k in range(1, gap_len):
            s = (s1 + k) % ell
            if word[s] == bL:
                bL_count += 1
            elif word[s] == bR:
                bR_count += 1
        gaps.append((gap_len, bL_count, bR_count))

    gap_patterns[tuple(sorted(gaps))] += 1

print(f"  Gap patterns (gap_len, bL_fires, bR_fires) for failing single-round ternary:")
for pat, cnt in gap_patterns.most_common(20):
    print(f"    {pat}: {cnt}")

# PART 4: The key coupling constraint - when P1 fails, what does P2 see?
print(f"\n{'='*60}")
print("PART 4: SHARED BINARY PHASE ANALYSIS")
print("When P1 fails FR, P2 is shared between P1 and P3.")
print("P2's firings see (c[P1], c[P3]). Does this force FR at P3?")

p2_joint = Counter()  # (c[P1], c[P3]) pairs at P2 firings when P1 fails
p2_detail = []

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)

    fc = Counter(word)
    fr_status = {t: has_full_return_at(ms, n, word, cycle, t) for t in tern}

    if not fr_status[1] and fr_status[3]:  # P1 fails, P3 ok
        # P2 firings: (c[P1], c[P3])
        p2_phases = []
        for s in range(ell):
            if word[s] == 2:  # P2 fires
                p2_phases.append((cycle[s][1], cycle[s][3]))

        p2_joint[tuple(sorted(p2_phases))] += 1

        if len(p2_detail) < 3:
            # Also get P0 and P4 phases
            p0_phases = [(cycle[s][5], cycle[s][1]) for s in range(ell) if word[s] == 0]
            p4_phases = [(cycle[s][3], cycle[s][5]) for s in range(ell) if word[s] == 4]
            p2_detail.append({
                'P2': p2_phases, 'P0': p0_phases, 'P4': p4_phases,
                'fc': dict(fc),
            })

print(f"\n  P2 (c[P1],c[P3]) patterns when P1 fails, P3 ok:")
for phases, cnt in p2_joint.most_common(15):
    print(f"    {list(phases)}: {cnt}")

print(f"\n  Sample details (P1 fails, P3 ok):")
for d in p2_detail:
    print(f"    fc={d['fc']}")
    print(f"      P0 (c[P5],c[P1]): {d['P0']}")
    print(f"      P2 (c[P1],c[P3]): {d['P2']}")
    print(f"      P4 (c[P3],c[P5]): {d['P4']}")

# PART 5: n=5 comparison - do pairs exist for wrap-adjacent?
print(f"\n{'='*60}")
print("PART 5: n=5 COMPARISON")

n5, ms5 = 5, [2, 3, 2, 3, 2]
tern5 = [1, 3]
words5 = enumerate_mover_words(ms5, n5, 21)

pair_fail5 = 0
total5 = 0

for word in words5:
    cycle = build_cycle(ms5, n5, word)
    if cycle is None:
        continue
    total5 += 1
    wrap = is_wrap_adjacent(word, n5)

    fr1 = has_full_return_at(ms5, n5, word, cycle, 1)
    fr3 = has_full_return_at(ms5, n5, word, cycle, 3)

    if not fr1 and not fr3:
        if wrap:
            pair_fail5 += 1

print(f"  n=5 wrap-adjacent pair-failures (P1+P3 both fail FR): {pair_fail5}")

elapsed = time.time() - t0
print(f"\nTotal: {elapsed:.1f}s")
sys.stdout.flush()
