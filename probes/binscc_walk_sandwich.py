#!/usr/bin/env python3
"""Walk Sandwich Analysis: Is the mover always in a length-1 (L,R) stay?

In alternating ring, P's neighbors are binary. Walk must arrive from binary,
fire P, depart to binary. So the step before and after P's mover both fire
binary neighbors → both toggle L or R → mover is in a length-1 stay.

KEY THEOREM TO VERIFY:
If J+K ≥ 4 in a sandwiched ternary phase, every stay has duration ≥ 1
(since consecutive neighbor firings require an intervening step),
so the trajectory has ≥ 5 positions with ≥ 1 repeated corner.
The mover's stay shares a corner with another stay → entry conflict.

But: the mover might be at a UNIQUE corner (repeat is elsewhere).
When does this happen?
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

print("=" * 70)
print("WALK SANDWICH: MOVER STAY LENGTH ANALYSIS")
print("=" * 70)

# ===== PART 1: Verify mover is always in length-1 stay =====
print("\nPART 1: Is mover always in length-1 (L,R) stay?")

for n, ms, max_len, label in [
    (5, [2,3,2,3,2], 20, "n=5 alt"),
    (6, [2,3,2,3,2,3], 24, "n=6 alt"),
    (7, [2,3,2,3,2,3,3], 21, "n=7 (3bin)"),
]:
    t0 = time.time()
    words = enumerate_mover_words(ms, n, max_len)

    ternary = [p for p in range(n) if ms[p] >= 3]
    sandwiched = [t for t in ternary if ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

    total = 0
    violations = 0  # mover NOT in length-1 stay

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        total += 1
        ell = len(word)

        for t in sandwiched:
            bL, bR = (t-1)%n, (t+1)%n
            for k in range(ms[t]):
                steps = [s for s in range(ell) if cycle[s][t] == k]
                # Find mover step in this phase
                mover_steps = [s for s in steps if word[s] == t]

                for ms_idx in mover_steps:
                    # Check: step before and after are neighbor firings
                    s_prev = (ms_idx - 1) % ell
                    s_next = (ms_idx + 1) % ell
                    prev_is_neighbor = word[s_prev] in (bL, bR)
                    next_is_neighbor = word[s_next] in (bL, bR)

                    if not (prev_is_neighbor and next_is_neighbor):
                        violations += 1

    print(f"  {label}: {total} cycles, violations={violations}")
    print(f"    Time: {time.time()-t0:.1f}s")

# ===== PART 2: Verify the Toggle-FR theorem =====
print(f"\n{'='*60}")
print("PART 2: Toggle-FR Theorem Verification")
print("If J ≥ 2 (even) and K = 0, or J=0 and K ≥ 2: forced entry conflict")
print("If J + K ≥ 4: forced repeat, but mover might be at unique corner")

# For each phase of each sandwiched ternary, check:
# 1. J, K values
# 2. Whether the (L,R) trajectory has a corner repeat at the mover
# 3. Whether entry conflict holds at this phase

n, ms = 6, [2, 3, 2, 3, 2, 3]
max_len = 24
t0 = time.time()
words = enumerate_mover_words(ms, n, max_len)
print(f"\nn=6 alternating: {len(words)} words ({time.time()-t0:.1f}s)")

ternary = [1, 3, 5]
total = 0
jk_fr = Counter()  # (J, K) → how many phases have FR
jk_nofr = Counter()  # (J, K) → how many phases lack FR
mover_unique_corner = Counter()  # (J, K) → mover at unique corner
mover_shared_corner = Counter()  # (J, K) → mover shares corner with nonmover stay

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    total += 1
    ell = len(word)

    for t in ternary:
        bL, bR = (t-1)%n, (t+1)%n

        for k in range(ms[t]):
            steps = [s for s in range(ell) if cycle[s][t] == k]
            mover_steps_in_phase = [s for s in steps if word[s] == t]

            # Compute J, K
            J = sum(1 for s in steps if word[s] == bL)
            K = sum(1 for s in steps if word[s] == bR)

            # Check entry conflict at this phase
            mover_lr = set()
            nonmover_lr = set()
            for s in steps:
                lr = (cycle[s][bL], cycle[s][bR])
                if word[s] == t:
                    mover_lr.add(lr)
                else:
                    nonmover_lr.add(lr)
            has_fr = bool(mover_lr & nonmover_lr)

            if has_fr:
                jk_fr[(J, K)] += 1
            else:
                jk_nofr[(J, K)] += 1

            # Check mover corner uniqueness
            # Build (L,R) stay sequence
            lr_sequence = []
            for s in steps:
                lr = (cycle[s][bL], cycle[s][bR])
                is_mover = (word[s] == t)
                lr_sequence.append((lr, is_mover))

            # Find the mover's (L,R)
            for lr, is_m in lr_sequence:
                if is_m:
                    mover_corner = lr
                    # Check if any nonmover has same (L,R)
                    nonmover_same = any(lr2 == mover_corner and not is_m2
                                       for lr2, is_m2 in lr_sequence)
                    if nonmover_same:
                        mover_shared_corner[(J, K)] += 1
                    else:
                        mover_unique_corner[(J, K)] += 1

print(f"Total: {total}")
print(f"\n  {'J':>3} {'K':>3} | {'FR':>7} {'NoFR':>7} | {'Shared':>7} {'Unique':>7} | Note")
print("  " + "-" * 65)

all_jks = sorted(set(list(jk_fr.keys()) + list(jk_nofr.keys())))
for J, K in all_jks:
    fr = jk_fr.get((J, K), 0)
    nofr = jk_nofr.get((J, K), 0)
    shared = mover_shared_corner.get((J, K), 0)
    unique = mover_unique_corner.get((J, K), 0)

    note = ""
    if J % 2 == 0 and K % 2 == 0:
        note = "BOTH-EVEN (return)"
    elif J + K <= 3:
        note = f"≤3 toggles"
    elif J + K >= 4:
        note = f"≥4 toggles"

    total_here = fr + nofr
    fr_pct = 100 * fr / total_here if total_here > 0 else 0
    print(f"  {J:>3} {K:>3} | {fr:>7} {nofr:>7} | {shared:>7} {unique:>7} | {note}")

# ===== PART 3: Toggle-FR for specific patterns =====
print(f"\n{'='*60}")
print("PART 3: Toggle-FR Theorem Cases")
print()
print("Anti-diagonal phases (no Both-Even return):")
print("  A=(odd,even): min (1,0) - 2 positions, unique mover ✓ → no FR")
print("  B=(even,odd): min (0,1) - 2 positions, unique mover ✓ → no FR")
print("  C=(odd,odd):  min (1,1) - 3 positions, all distinct ✓ → no FR")
print()
print("Higher J+K cases:")
print("  (3,0): 4 positions, corners (00)(10)(00)(10) → FORCED repeat → FR!")
print("  (0,3): same by symmetry → FR!")
print("  (2,1): 4 positions, depends on order:")
print("    LLR: (00)(10)(00)(01) → (00) repeats → mover at (00)? → FR")
print("    LRL: (00)(10)(11)(01) → all distinct! → no FR possible")
print("    RLL: (00)(01)(11)(01) → wait this is wrong. RLL means:")
print("      (L0,R0) -R→ (L0,R1) -L→ (L1,R1) -L→ (L0,R1)")
print("      Corners: (0,0)(0,1)(1,1)(0,1). (0,1) repeats at pos 1,3.")
print("      If mover at pos 0=(0,0) or pos 2=(1,1): unique → no FR")
print("      If mover at pos 1 or 3=(0,1): shared → FR")

# Verify (3,0) always has FR in data
print(f"\n  From data: (3,0) FR rate: {jk_fr.get((3,0),0)}/{jk_fr.get((3,0),0)+jk_nofr.get((3,0),0)}")
print(f"  (0,3) FR rate: {jk_fr.get((0,3),0)}/{jk_fr.get((0,3),0)+jk_nofr.get((0,3),0)}")
print(f"  (1,0) FR rate: {jk_fr.get((1,0),0)}/{jk_fr.get((1,0),0)+jk_nofr.get((1,0),0)}")
print(f"  (0,1) FR rate: {jk_fr.get((0,1),0)}/{jk_fr.get((0,1),0)+jk_nofr.get((0,1),0)}")
print(f"  (1,1) FR rate: {jk_fr.get((1,1),0)}/{jk_fr.get((1,1),0)+jk_nofr.get((1,1),0)}")

# ===== PART 4: The critical question =====
# For the ABC structure (all phases anti-diagonal), what are the ACTUAL
# (J,K) values? If ALL phases have J+K ≤ 3, no individual phase is forced.
# But can ALL 3 phases have J+K ≤ 3 when fc constraints apply?

print(f"\n{'='*60}")
print("PART 4: Can ALL 3 phases have J+K ≤ 3?")

ternary_all_low = 0
ternary_some_high = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)

    for t in ternary:
        bL, bR = (t-1)%n, (t+1)%n
        all_low = True
        for k in range(ms[t]):
            steps = [s for s in range(ell) if cycle[s][t] == k]
            J = sum(1 for s in steps if word[s] == bL)
            K = sum(1 for s in steps if word[s] == bR)
            if J + K > 3:
                all_low = False
                break

        if all_low:
            ternary_all_low += 1
        else:
            ternary_some_high += 1

print(f"  All phases J+K ≤ 3: {ternary_all_low}")
print(f"  Some phase J+K > 3: {ternary_some_high}")

# For the failing ternary specifically:
print(f"\n  Among FAILING ternary (no FR at any phase):")
failing_all_low = 0
failing_some_high = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)

    for t in ternary:
        bL, bR = (t-1)%n, (t+1)%n

        # Check if t has entry conflict
        mover_lsr = set()
        nonmover_lsr = set()
        for s in range(ell):
            lsr = (cycle[s][bL], cycle[s][t], cycle[s][bR])
            if word[s] == t:
                mover_lsr.add(lsr)
            else:
                nonmover_lsr.add(lsr)
        has_fr = bool(mover_lsr & nonmover_lsr)

        if has_fr:
            continue  # t has FR, skip

        # t fails FR. Check if all phases have J+K ≤ 3
        all_low = True
        jk_list = []
        for k in range(ms[t]):
            steps = [s for s in range(ell) if cycle[s][t] == k]
            J = sum(1 for s in steps if word[s] == bL)
            K = sum(1 for s in steps if word[s] == bR)
            jk_list.append((J, K))
            if J + K > 3:
                all_low = False

        if all_low:
            failing_all_low += 1
        else:
            failing_some_high += 1

print(f"    All phases J+K ≤ 3: {failing_all_low}")
print(f"    Some phase J+K > 3: {failing_some_high}")

print(f"\n  IMPLICATION: If failing ternary ALWAYS have all J+K ≤ 3,")
print(f"  then the toggle-FR theorem (J+K ≥ 4 → FR) is NOT the mechanism.")
print(f"  If some have J+K > 3 but still no FR, the ordering matters.")

# ===== PART 5: Check for n=5 =====
print(f"\n{'='*60}")
print("PART 5: Same analysis at n=5")

n5, ms5 = 5, [2,3,2,3,2]
t0 = time.time()
w5 = enumerate_mover_words(ms5, n5, 20)
print(f"n=5: {len(w5)} words ({time.time()-t0:.1f}s)")

fail5_jk = Counter()  # (J,K) at failing ternary phases
for word in w5:
    cycle = build_cycle(ms5, n5, word)
    if cycle is None or not is_wrap_adjacent(word, n5):
        continue
    ell = len(word)

    for t in [1, 3]:
        bL, bR = (t-1)%n5, (t+1)%n5
        mover_lsr = set()
        nonmover_lsr = set()
        for s in range(ell):
            lsr = (cycle[s][bL], cycle[s][t], cycle[s][bR])
            if word[s] == t: mover_lsr.add(lsr)
            else: nonmover_lsr.add(lsr)
        has_fr = bool(mover_lsr & nonmover_lsr)

        if has_fr:
            continue

        for k in range(ms5[t]):
            steps = [s for s in range(ell) if cycle[s][t] == k]
            J = sum(1 for s in steps if word[s] == bL)
            K = sum(1 for s in steps if word[s] == bR)
            fail5_jk[(J, K)] += 1

print(f"  Failing ternary phase (J,K):")
for (J, K), cnt in sorted(fail5_jk.items()):
    note = "≤3" if J+K <= 3 else "≥4"
    print(f"    ({J},{K}): {cnt}  [J+K={J+K}, {note}]")

print(f"\nTotal: {time.time()-t0:.1f}s")
