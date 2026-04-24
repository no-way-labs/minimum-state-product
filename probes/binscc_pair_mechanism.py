#!/usr/bin/env python3
"""When P1 fails FR, what mechanism guarantees FR at P3?

Key question: does P1 failing FR force P3 to have a dur-4 phase (toggle-back)?
If yes, pair-failure impossibility follows from the toggle-back lemma.
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

def get_phase_durations(ms, n, word, cycle, t):
    """Get duration of each phase of ternary t."""
    ell = len(cycle)
    durations = []
    for k in range(ms[t]):
        ps = [s for s in range(ell) if cycle[s][t] == k]
        durations.append(len(ps))
    return durations

def fr_mechanism_at(ms, n, word, cycle, t):
    """Identify which phase gives FR and what mechanism."""
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
            dur = len(ps)
            # Count binary neighbor firings in this phase
            bL_fires = sum(1 for s in ps if word[s] == bL)
            bR_fires = sum(1 for s in ps if word[s] == bR)
            return (k, dur, bL_fires, bR_fires)
    return None

print("=" * 70)
print("PAIR-FAILURE MECHANISM ANALYSIS")
print("=" * 70)

n, ms = 6, [2, 3, 2, 3, 2, 3]
tern = [1, 3, 5]

t0 = time.time()
words = enumerate_mover_words(ms, n, 24)

# PART 1: When P1 fails, does P3 always have a dur-4 phase?
print("\nPART 1: P1-FAIL → P3 DUR-4 PHASE?")

p1_fail_count = 0
p3_has_dur4 = 0
p3_fr_mechanism = Counter()
p3_dur_at_fr = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    fc = Counter(word)

    # Check all ternary pairs (not just P1,P3)
    for t_fail in tern:
        if has_full_return_at(ms, n, word, cycle, t_fail):
            continue
        # t_fail does NOT have FR
        p1_fail_count += 1

        # Check neighbors
        for t_ok in tern:
            if t_ok == t_fail:
                continue
            if not has_full_return_at(ms, n, word, cycle, t_ok):
                continue  # both fail = should be 0

            durations = get_phase_durations(ms, n, word, cycle, t_ok)
            has_d4 = any(d == 4 for d in durations)
            if has_d4:
                p3_has_dur4 += 1

            mech = fr_mechanism_at(ms, n, word, cycle, t_ok)
            if mech:
                k, dur, bLf, bRf = mech
                p3_fr_mechanism[(dur, bLf, bRf)] += 1
                p3_dur_at_fr[dur] += 1

print(f"  Ternary-fails-FR instances: {p1_fail_count}")
print(f"  Partner with FR has dur-4 phase: {p3_has_dur4}/{p1_fail_count*2} "
      f"({100*p3_has_dur4/(p1_fail_count*2):.1f}%)")

print(f"\n  FR mechanism at partner (dur, bL_fires, bR_fires):")
for mech, cnt in sorted(p3_fr_mechanism.items(), key=lambda x: -x[1]):
    print(f"    dur={mech[0]}, bL={mech[1]}, bR={mech[2]}: {cnt}")

print(f"\n  FR phase duration at partner:")
for dur, cnt in sorted(p3_dur_at_fr.items()):
    print(f"    dur={dur}: {cnt}")

# PART 2: Sharper question - does EVERY FR-failing ternary's
# NEIGHBOR have a dur-4 phase?
print(f"\n{'='*60}")
print("PART 2: DOES FAILING TERNARY'S NEIGHBOR ALWAYS HAVE DUR-4?")

fail_neighbor_dur4 = Counter()  # (has_dur4_at_left_neighbor, has_dur4_at_right_neighbor)
any_neighbor_dur4 = 0
no_neighbor_dur4_count = 0
no_neighbor_dur4_examples = []

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    fc = Counter(word)

    for t_fail in tern:
        if has_full_return_at(ms, n, word, cycle, t_fail):
            continue

        # Check BOTH ternary neighbors of t_fail
        # On n=6 alternating, ternary neighbors are at distance 2
        t_left = (t_fail - 2) % n  # left ternary neighbor
        t_right = (t_fail + 2) % n  # right ternary neighbor

        dur_left = get_phase_durations(ms, n, word, cycle, t_left)
        dur_right = get_phase_durations(ms, n, word, cycle, t_right)

        has_d4_left = any(d == 4 for d in dur_left)
        has_d4_right = any(d == 4 for d in dur_right)

        fail_neighbor_dur4[(has_d4_left, has_d4_right)] += 1

        if has_d4_left or has_d4_right:
            any_neighbor_dur4 += 1
        else:
            no_neighbor_dur4_count += 1
            if len(no_neighbor_dur4_examples) < 3:
                no_neighbor_dur4_examples.append({
                    't_fail': t_fail,
                    'dur_left': dur_left, 'dur_right': dur_right,
                    't_left': t_left, 't_right': t_right,
                    'word': word[:20],
                    'fc': dict(fc),
                })

total_fails = sum(fail_neighbor_dur4.values())
print(f"  Total failing-ternary instances: {total_fails}")
for (dl, dr), cnt in sorted(fail_neighbor_dur4.items(), key=lambda x: -x[1]):
    print(f"    left_dur4={dl}, right_dur4={dr}: {cnt}")
print(f"  ANY neighbor has dur-4: {any_neighbor_dur4}/{total_fails}")
print(f"  NO neighbor has dur-4: {no_neighbor_dur4_count}")

if no_neighbor_dur4_examples:
    print(f"\n  Examples where no neighbor has dur-4:")
    for ex in no_neighbor_dur4_examples:
        print(f"    fail=P{ex['t_fail']}, left=P{ex['t_left']} dur={ex['dur_left']}, "
              f"right=P{ex['t_right']} dur={ex['dur_right']}")
        print(f"      fc={ex['fc']}")

# PART 3: For those without neighbor dur-4, what mechanism gives FR?
print(f"\n{'='*60}")
print("PART 3: NO-NEIGHBOR-DUR4 CASES - FR MECHANISM")

no_d4_mechanisms = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    fc = Counter(word)

    for t_fail in tern:
        if has_full_return_at(ms, n, word, cycle, t_fail):
            continue

        t_left = (t_fail - 2) % n
        t_right = (t_fail + 2) % n

        dur_left = get_phase_durations(ms, n, word, cycle, t_left)
        dur_right = get_phase_durations(ms, n, word, cycle, t_right)

        if any(d == 4 for d in dur_left) or any(d == 4 for d in dur_right):
            continue  # already covered

        # Neither neighbor has dur-4. What mechanism gives FR?
        for t_ok in [t_left, t_right]:
            if not has_full_return_at(ms, n, word, cycle, t_ok):
                continue
            mech = fr_mechanism_at(ms, n, word, cycle, t_ok)
            if mech:
                k, dur, bLf, bRf = mech
                is_multi = fc[t_ok] > ms[t_ok]
                no_d4_mechanisms[(dur, bLf, bRf, "multi" if is_multi else "single")] += 1

print(f"  FR mechanisms when no neighbor has dur-4:")
for mech, cnt in sorted(no_d4_mechanisms.items(), key=lambda x: -x[1]):
    print(f"    dur={mech[0]}, bL={mech[1]}, bR={mech[2]}, {mech[3]}: {cnt}")

# PART 4: Check if the FAILING ternary itself always has dur-4 at SOME phase
print(f"\n{'='*60}")
print("PART 4: DOES THE FAILING TERNARY ITSELF HAVE DUR-4?")

fail_self_dur4 = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    for t_fail in tern:
        if has_full_return_at(ms, n, word, cycle, t_fail):
            continue
        durations = get_phase_durations(ms, n, word, cycle, t_fail)
        has_d4 = any(d == 4 for d in durations)
        fail_self_dur4[has_d4] += 1

print(f"  Failing ternary has dur-4 phase: {fail_self_dur4}")

# PART 5: For ALL cycles (not just fails), does every cycle have SOME
# ternary with a dur-4 phase?
print(f"\n{'='*60}")
print("PART 5: DOES EVERY CYCLE HAVE SOME TERNARY WITH DUR-4?")

no_dur4_anywhere = 0
total_cycles = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    total_cycles += 1

    any_dur4 = False
    for t in tern:
        durations = get_phase_durations(ms, n, word, cycle, t)
        if any(d == 4 for d in durations):
            any_dur4 = True
            break
    if not any_dur4:
        no_dur4_anywhere += 1

print(f"  Cycles with no dur-4 phase at ANY ternary: {no_dur4_anywhere}/{total_cycles}")
print(f"  Coverage of dur-4 somewhere: {100*(total_cycles-no_dur4_anywhere)/total_cycles:.1f}%")

# PART 6: For the no-dur4-anywhere cycles, how does FR hold?
print(f"\n{'='*60}")
print("PART 6: NO-DUR4-ANYWHERE CYCLES - FR ANALYSIS")

no_dur4_fr = Counter()
no_dur4_all_fail = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    fc = Counter(word)

    any_dur4 = False
    for t in tern:
        durations = get_phase_durations(ms, n, word, cycle, t)
        if any(d == 4 for d in durations):
            any_dur4 = True
            break
    if any_dur4:
        continue

    # No dur-4 anywhere. Check FR at each ternary.
    fr_count = 0
    for t in tern:
        if has_full_return_at(ms, n, word, cycle, t):
            fr_count += 1
            mech = fr_mechanism_at(ms, n, word, cycle, t)
            if mech:
                k, dur, bLf, bRf = mech
                is_multi = fc[t] > ms[t]
                no_dur4_fr[(dur, bLf, bRf, "multi" if is_multi else "single")] += 1

    if fr_count == 0:
        no_dur4_all_fail += 1

print(f"  No-dur4 cycles with ALL ternary failing FR: {no_dur4_all_fail}")
print(f"\n  FR mechanisms in no-dur4 cycles:")
for mech, cnt in sorted(no_dur4_fr.items(), key=lambda x: -x[1]):
    print(f"    dur={mech[0]}, bL={mech[1]}, bR={mech[2]}, {mech[3]}: {cnt}")

elapsed = time.time() - t0
print(f"\nTotal: {elapsed:.1f}s")
sys.stdout.flush()
