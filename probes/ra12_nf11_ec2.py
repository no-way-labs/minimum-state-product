#!/usr/bin/env python3
"""RA12 Phase 2: Structural analysis of (1,1) EC failure.

Key finding from Phase 1:
- Systems with ONLY 1 sandwiched ternary (rest binary, like [2,2,2,2,3]):
  EC FAILS for all 108 cycles with (1,1) phases. 0% EC.
- Systems with 2 sandwiched ternaries (like [2,3,2,3,2]):
  EC HOLDS for all 854 cycles with (1,1) phases. 100% EC.

Question: WHY does having a single ternary avoid EC while two ternaries force it?

Hypothesis: With 1 ternary, the ternary's 3 mover contexts use 3 distinct values
of t (0,1,2), while non-mover contexts also use all 3 values. But the binary
neighbor values are arranged so mover and non-mover contexts never collide.

With 2 ternaries, the second ternary constrains the binary neighbors differently,
forcing overlap.

This script:
1. Analyzes the counterexample structure in detail
2. Checks whether EC exists at ANY processor (not just the sandwiched ternary)
3. Determines if these cycles can actually be realized as valid systems
"""

from collections import Counter, defaultdict
from itertools import product as iproduct
import time


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


def get_phases(word, cycle, t, n):
    ell = len(word)
    bL = (t - 1) % n
    bR = (t + 1) % n
    t_steps = [s for s in range(ell) if word[s] == t]
    if len(t_steps) == 0:
        return []
    phases = []
    for idx in range(len(t_steps)):
        start = t_steps[idx]
        end = t_steps[(idx + 1) % len(t_steps)]
        phase_steps = []
        s = (start + 1) % ell
        while s != end:
            phase_steps.append(s)
            s = (s + 1) % ell
        J = sum(1 for s in phase_steps if word[s] == bL)
        K = sum(1 for s in phase_steps if word[s] == bR)
        phases.append({
            't_fire_step': start,
            't_fire_end': end,
            'steps': phase_steps,
            'J': J, 'K': K,
        })
    return phases


def check_ec_all_procs(word, cycle, ms, n):
    """Check EC at EVERY processor. Return dict proc -> (has_ec, overlap)."""
    ell = len(word)
    result = {}
    for p in range(n):
        bL = (p - 1) % n
        bR = (p + 1) % n
        mover = set()
        nonmover = set()
        for s in range(ell):
            ctx = (cycle[s][bL], cycle[s][p], cycle[s][bR])
            if word[s] == p:
                mover.add(ctx)
            else:
                nonmover.add(ctx)
        overlap = mover & nonmover
        result[p] = (len(overlap) > 0, overlap, mover, nonmover)
    return result


def check_consistency(word, cycle, ms, n):
    """Check if the cycle is consistent: no conflicting transition entries.

    For each proc p, collect all (L,S,R) -> S' entries:
    - When p is mover: (L,S,R) -> S' (where S' != S, the new value)
    - When p is non-mover: (L,S,R) -> S (identity)

    Conflict = same (p, L, S, R) maps to different outputs.
    """
    ell = len(word)
    entries = {}  # (proc, L, S, R) -> set of outputs
    for s in range(ell):
        for p in range(n):
            L = cycle[s][(p-1) % n]
            S = cycle[s][p]
            R = cycle[s][(p+1) % n]
            key = (p, L, S, R)
            if word[s] == p:
                # Mover: S changes
                S_new = cycle[(s+1) % ell][p]
                out = S_new
            else:
                # Non-mover: S stays
                out = S
            if key not in entries:
                entries[key] = set()
            entries[key].add(out)

    conflicts = []
    for key, vals in entries.items():
        if len(vals) > 1:
            conflicts.append((key, vals))
    return conflicts


# =====================================================================
# ANALYSIS 1: EC at ALL processors for the counterexample systems
# =====================================================================

print("=" * 70)
print("ANALYSIS 1: EC at ALL processors (not just sandwiched ternary)")
print("=" * 70)

n = 5

# The counterexample systems: 1 sandwiched ternary, rest binary
single_ternary_systems = [
    [2, 2, 2, 2, 3],
    [2, 2, 2, 3, 2],
    [2, 2, 3, 2, 2],
    [2, 3, 2, 2, 2],
    [3, 2, 2, 2, 2],
]

for ms in single_ternary_systems:
    sandwiched = [p for p in range(n) if ms[p] == 3 and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]
    prod = 1
    for m in ms:
        prod *= m
    print(f"\nms={ms}, prod={prod}, sandwiched_ternary={sandwiched}")

    words = enumerate_mover_words(ms, n, max_length=20)

    total = 0
    ec_at_any = 0
    no_ec_anywhere = 0
    ec_by_proc = Counter()
    consistency_failures = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue

        # Check for (1,1) phases
        has_11 = False
        for t in sandwiched:
            phases = get_phases(word, cycle, t, n)
            if any(p['J'] == 1 and p['K'] == 1 for p in phases):
                has_11 = True
                break
        if not has_11:
            continue

        total += 1

        # Check EC at ALL procs
        ec_result = check_ec_all_procs(word, cycle, ms, n)
        any_ec = False
        for p, (has_ec, overlap, _, _) in ec_result.items():
            if has_ec:
                any_ec = True
                ec_by_proc[p] += 1

        if any_ec:
            ec_at_any += 1
        else:
            no_ec_anywhere += 1

            # Check consistency
            conflicts = check_consistency(word, cycle, ms, n)
            if conflicts:
                consistency_failures += 1

    print(f"  Total cycles with (1,1) phase: {total}")
    print(f"  EC at any proc: {ec_at_any}")
    print(f"  NO EC anywhere: {no_ec_anywhere}")
    print(f"  EC by proc: {dict(ec_by_proc)}")
    if no_ec_anywhere > 0:
        print(f"  Consistency failures among no-EC cycles: {consistency_failures}")
    break  # Just first one for now


# =====================================================================
# ANALYSIS 2: Deep dive into a single counterexample
# =====================================================================

print("\n" + "=" * 70)
print("ANALYSIS 2: Deep dive into counterexample structure")
print("=" * 70)

ms = [2, 2, 2, 2, 3]
n = 5
sandwiched = [4]

words = enumerate_mover_words(ms, n, max_length=20)
count = 0
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    phases = get_phases(word, cycle, 4, n)
    has_11 = any(p['J'] == 1 and p['K'] == 1 for p in phases)
    if not has_11:
        continue

    if count >= 2:
        break
    count += 1

    ell = len(word)
    print(f"\n--- Counterexample {count} ---")
    print(f"Word: {word}")
    print(f"Cycle length: {ell}")

    # Full step-by-step trace
    print(f"\nStep-by-step trace:")
    for s in range(ell):
        mover = word[s]
        c = cycle[s]
        c_next = cycle[(s+1) % ell]
        ctx_at_4 = (c[3], c[4], c[0])  # L=proc3, S=proc4, R=proc0 (ring)
        print(f"  Step {s:2d}: config={c}, mover={mover}, "
              f"ctx@4=(c[3]={c[3]}, c[4]={c[4]}, c[0]={c[0]})")

    # EC analysis at proc 4
    ec_result = check_ec_all_procs(word, cycle, ms, n)
    print(f"\nEC at each proc:")
    for p in range(n):
        has_ec, overlap, mctx, nmctx = ec_result[p]
        print(f"  Proc {p} (m={ms[p]}): EC={has_ec}")
        print(f"    Mover contexts:    {sorted(mctx)}")
        print(f"    NonMover contexts: {sorted(nmctx)}")
        if overlap:
            print(f"    Overlap: {sorted(overlap)}")

    # Consistency check
    conflicts = check_consistency(word, cycle, ms, n)
    print(f"\nConsistency conflicts: {len(conflicts)}")
    for (proc, L, S, R), vals in conflicts:
        print(f"  Proc {proc}: ({L},{S},{R}) -> {vals}")


# =====================================================================
# ANALYSIS 3: Compare single-ternary vs two-ternary
# =====================================================================

print("\n" + "=" * 70)
print("ANALYSIS 3: WHY does having 2 sandwiched ternaries force EC?")
print("=" * 70)

# Two-ternary system
ms_2t = [2, 3, 2, 3, 2]
n = 5
sandwiched_2t = [1, 3]

print(f"ms={ms_2t}, sandwiched={sandwiched_2t}")
words_2t = enumerate_mover_words(ms_2t, n, max_length=20)

count_2t = 0
for word in words_2t:
    cycle = build_cycle(ms_2t, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    has_11 = False
    for t in sandwiched_2t:
        phases = get_phases(word, cycle, t, n)
        if any(p['J'] == 1 and p['K'] == 1 for p in phases):
            has_11 = True
            break
    if not has_11:
        continue

    if count_2t >= 1:
        break
    count_2t += 1

    ell = len(word)
    print(f"\n--- Two-ternary example ---")
    print(f"Word: {word}")
    print(f"Cycle length: {ell}")

    ec_result = check_ec_all_procs(word, cycle, ms_2t, n)
    print(f"\nEC at each proc:")
    for p in range(n):
        has_ec, overlap, mctx, nmctx = ec_result[p]
        print(f"  Proc {p} (m={ms_2t[p]}): EC={has_ec}")
        print(f"    Mover contexts:    {sorted(mctx)}")
        print(f"    NonMover contexts: {sorted(nmctx)}")
        if overlap:
            print(f"    Overlap: {sorted(overlap)}")


# =====================================================================
# ANALYSIS 4: Number of ternaries as the distinguishing feature
# =====================================================================

print("\n" + "=" * 70)
print("ANALYSIS 4: EC rate vs number of ternary processors")
print("=" * 70)

n = 5
threshold = 4 * (3 ** (n - 2))

for ms_tuple in iproduct(*[range(2, 4) for _ in range(n)]):
    ms = list(ms_tuple)
    prod = 1
    for m in ms:
        prod *= m
    if prod >= threshold:
        continue

    num_binary = sum(1 for m in ms if m == 2)
    if num_binary < 3:
        continue

    sandwiched = [p for p in range(n) if ms[p] == 3 and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]
    if not sandwiched:
        continue

    num_ternary = n - num_binary

    words = enumerate_mover_words(ms, n, max_length=20)
    total = 0
    ec_count = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue

        has_11 = False
        for t in sandwiched:
            phases = get_phases(word, cycle, t, n)
            if any(p['J'] == 1 and p['K'] == 1 for p in phases):
                has_11 = True
                break
        if not has_11:
            continue
        total += 1

        # Check EC at sandwiched ternary only
        has_ec = False
        for t in sandwiched:
            bL, bR = (t-1)%n, (t+1)%n
            mover, nonmover = set(), set()
            for s in range(len(word)):
                ctx = (cycle[s][bL], cycle[s][t], cycle[s][bR])
                if word[s] == t:
                    mover.add(ctx)
                else:
                    nonmover.add(ctx)
            if mover & nonmover:
                has_ec = True
                break
        if has_ec:
            ec_count += 1

    if total > 0:
        rate = ec_count / total
        status = "ALL EC" if ec_count == total else f"FAIL {total - ec_count}"
        print(f"  ms={ms}, #ternary={num_ternary}, #sandwiched={len(sandwiched)}: "
              f"{ec_count}/{total} EC ({100*rate:.0f}%) [{status}]")


# =====================================================================
# ANALYSIS 5: Do NO-EC cycles actually have VALID completions?
# =====================================================================

print("\n" + "=" * 70)
print("ANALYSIS 5: Can no-EC cycles be completed to valid systems?")
print("=" * 70)

ms = [2, 2, 2, 2, 3]
n = 5
sandwiched = [4]

words = enumerate_mover_words(ms, n, max_length=20)
no_ec_count = 0
completable_count = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    phases = get_phases(word, cycle, 4, n)
    has_11 = any(p['J'] == 1 and p['K'] == 1 for p in phases)
    if not has_11:
        continue

    # Check EC at all procs
    ec_result = check_ec_all_procs(word, cycle, ms, n)
    any_ec = any(has_ec for has_ec, _, _, _ in ec_result.values())

    if not any_ec:
        no_ec_count += 1
        # Check consistency
        conflicts = check_consistency(word, cycle, ms, n)
        if not conflicts:
            completable_count += 1
            if completable_count <= 3:
                print(f"  Completable cycle: word={word}")

print(f"\nNo-EC cycles: {no_ec_count}")
print(f"Of those, consistent (potentially completable): {completable_count}")
if completable_count == 0:
    print("*** ALL no-EC cycles have consistency conflicts elsewhere ***")
    print("*** (1,1) cycles that avoid EC at sandwiched ternary still fail at other procs ***")
else:
    print(f"*** {completable_count} cycles survive — (1,1) does NOT force failure ***")


# =====================================================================
# ANALYSIS 6: Check EC at OTHER procs for no-EC-at-sandwiched cycles
# =====================================================================

print("\n" + "=" * 70)
print("ANALYSIS 6: Where does EC appear in no-sandwiched-EC cycles?")
print("=" * 70)

ms = [2, 2, 2, 2, 3]
n = 5
sandwiched = [4]

words = enumerate_mover_words(ms, n, max_length=20)
ec_locations = Counter()
total_no_sand_ec = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    phases = get_phases(word, cycle, 4, n)
    has_11 = any(p['J'] == 1 and p['K'] == 1 for p in phases)
    if not has_11:
        continue

    # Check EC at sandwiched ternary first
    bL, bR = 3, 0
    mover, nonmover = set(), set()
    for s in range(len(word)):
        ctx = (cycle[s][bL], cycle[s][4], cycle[s][bR])
        if word[s] == 4:
            mover.add(ctx)
        else:
            nonmover.add(ctx)
    if mover & nonmover:
        continue  # Has EC at sandwiched ternary, skip

    total_no_sand_ec += 1

    # Where is EC?
    ec_result = check_ec_all_procs(word, cycle, ms, n)
    for p in range(n):
        if ec_result[p][0]:
            ec_locations[p] += 1

print(f"Cycles with (1,1) phase but NO EC at sandwiched ternary: {total_no_sand_ec}")
print(f"EC locations among these:")
for p in range(n):
    cnt = ec_locations.get(p, 0)
    print(f"  Proc {p} (m={ms[p]}): {cnt}/{total_no_sand_ec} "
          f"({'YES' if cnt == total_no_sand_ec else 'PARTIAL' if cnt > 0 else 'NEVER'})")

# Are there cycles with NO EC at ANY proc?
no_ec_anywhere_count = 0
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    phases = get_phases(word, cycle, 4, n)
    has_11 = any(p['J'] == 1 and p['K'] == 1 for p in phases)
    if not has_11:
        continue

    ec_result = check_ec_all_procs(word, cycle, ms, n)
    if not any(has_ec for has_ec, _, _, _ in ec_result.values()):
        no_ec_anywhere_count += 1

print(f"\nCycles with (1,1) phase and NO EC at ANY proc: {no_ec_anywhere_count}")
