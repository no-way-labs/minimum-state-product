#!/usr/bin/env python3
"""Deep coupling analysis: WHY fc[P4]=4 when both sandwiched fail.

The parity pigeonhole only gives fc[P4] ≥ 2. But data shows fc[P4]=4 always.
This script investigates the additional constraint: phase DURATION budgets.

Key insight to test: the cycle length ℓ imposes a budget constraint.
Each phase of each ternary has duration ≥ 2 (must have ≥1 mover + ≥1 nonmover for the
adjacency walk to work). Total duration = ℓ.
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

def has_entry_conflict_at(ms, n, word, cycle, p):
    ell = len(word)
    bL, bR = (p-1)%n, (p+1)%n
    mover, nonmover = set(), set()
    for s in range(ell):
        lsr = (cycle[s][bL], cycle[s][p], cycle[s][bR])
        if word[s] == p: mover.add(lsr)
        else: nonmover.add(lsr)
    return bool(mover & nonmover)

def phase_detail(ms, n, word, cycle, p):
    """Per-phase analysis: J, K, duration, mover/nonmover counts."""
    ell = len(word)
    bL, bR = (p-1)%n, (p+1)%n
    result = []
    for k in range(ms[p]):
        steps = [s for s in range(ell) if cycle[s][p] == k]
        J = sum(1 for s in steps if word[s] == bL)
        K = sum(1 for s in steps if word[s] == bR)
        M = sum(1 for s in steps if word[s] == p)  # mover firings
        dur = len(steps)
        # Check FR
        mover_lr, nonmover_lr = set(), set()
        for s in steps:
            lr = (cycle[s][bL], cycle[s][bR])
            if word[s] == p:
                mover_lr.add(lr)
            else:
                nonmover_lr.add(lr)
        has_fr = bool(mover_lr & nonmover_lr)
        is_return = (J % ms[bL] == 0) and (K % ms[bR] == 0)
        result.append({
            'k': k, 'J': J, 'K': K, 'M': M, 'dur': dur,
            'has_fr': has_fr, 'ret': is_return,
            'J_par': J % 2, 'K_par': K % ms[bR]
        })
    return result

print("=" * 70)
print("DEEP COUPLING: WHY fc[P4]=4 WHEN BOTH SANDWICHED FAIL")
print("=" * 70)

n, ms = 7, [2, 3, 2, 3, 2, 3, 3]
max_len = 24

t0 = time.time()
words = enumerate_mover_words(ms, n, max_len)
print(f"Words: {len(words)} ({time.time()-t0:.1f}s)")

total = 0
both_sand_fail = []

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    total += 1
    p1_fr = has_entry_conflict_at(ms, n, word, cycle, 1)
    p3_fr = has_entry_conflict_at(ms, n, word, cycle, 3)
    if not p1_fr and not p3_fr:
        both_sand_fail.append((word, cycle))

print(f"Total: {total}, Both sand fail: {len(both_sand_fail)}")

# PART 1: Phase durations and (J,K,M) per phase when both sand fail
print(f"\n{'='*60}")
print("PHASE STRUCTURE WHEN BOTH P1,P3 FAIL")

for idx, (word, cycle) in enumerate(both_sand_fail[:5]):
    fc = Counter(word)
    ell = len(word)
    print(f"\n--- Cycle {idx}: len={ell}, fc={[fc.get(p,0) for p in range(n)]} ---")
    for p_check in [1, 3, 5, 6]:
        phases = phase_detail(ms, n, word, cycle, p_check)
        print(f"  P{p_check} (m={ms[p_check]}, bL=P{(p_check-1)%n}(m={ms[(p_check-1)%n]}), bR=P{(p_check+1)%n}(m={ms[(p_check+1)%n]})):")
        for ph in phases:
            ret = "RET" if ph['ret'] else ""
            fr = "FR" if ph['has_fr'] else ""
            print(f"    phase {ph['k']}: dur={ph['dur']}, J={ph['J']}({ph['J_par']}), "
                  f"K={ph['K']}(≡{ph['K_par']}mod{ms[(p_check+1)%n]}), M={ph['M']}  {ret} {fr}")

# PART 2: Why is fc[P4] exactly 4, not 2?
print(f"\n{'='*60}")
print("MINIMUM CYCLE LENGTH ANALYSIS")

# Each ternary p has ms[p] phases, each phase needs ≥1 step to advance through
# Actually minimum: each ternary needs fc[p] ≥ ms[p] (at least one fire per phase)
# AND fc[p] ≡ 0 mod ms[p]
# Each binary needs fc[b] ≥ ms[b] = 2 and fc[b] ≡ 0 mod 2

# Minimum ℓ = Σ fc_min[p]
# Binary: fc_min = 2
# Ternary: fc_min = 3
# ℓ_min = 3(2) + 4(3) = 18

# Now: the cycle must be a connected walk on the ring graph.
# Each step fires one processor. Two consecutive steps must fire adjacent procs.
# So the mover word is a walk on a path graph (ring restricted).

print("Minimum cycle length constraints:")
print(f"  Binary (×3): fc ≥ 2, total ≥ 6")
print(f"  Ternary (×4): fc ≥ 3, total ≥ 12")
print(f"  ℓ_min = 18")

# PART 3: Duration constraint
# In a ring walk, to reach a proc p, you must walk through all intermediate procs.
# P4 is between P3 and P5. To fire P0, you must walk through P1,P2,P3 or P5,P6.
# This walk constraint means you can't independently minimize each fc.

print(f"\n{'='*60}")
print("WALK CONSTRAINT ANALYSIS")

# Count: in the 88 both-sand-fail cycles, what are the phase durations?
dur_dist = {p: Counter() for p in [1,3,5,6]}
jk_per_phase = {p: [Counter() for _ in range(ms[p])] for p in [1,3,5,6]}

for word, cycle in both_sand_fail:
    for p_check in [1, 3, 5, 6]:
        phases = phase_detail(ms, n, word, cycle, p_check)
        for ph in phases:
            dur_dist[p_check][ph['dur']] += 1
            jk_per_phase[p_check][ph['k']][(ph['J'], ph['K'])] += 1

for p_check in [1, 3, 5, 6]:
    print(f"\n  P{p_check} duration distribution: {dict(sorted(dur_dist[p_check].items()))}")
    for k in range(ms[p_check]):
        print(f"    Phase {k} (J,K): {dict(sorted(jk_per_phase[p_check][k].items()))}")

# PART 4: KEY TEST — is the fire count budget the mechanism?
# If fc[P2]=2 (minimum), then P2 fires exactly twice.
# P1 and P3 each need fc[P2] contributions through their phases.
# P1's K values: {even, odd, odd} (from ABC). K_A+K_B+K_C = fc[P2] = 2.
# K_A even ≥ 0, K_B odd ≥ 1, K_C odd ≥ 1 → K_A=0, K_B=1, K_C=1.
# P3's J values: {odd, even, odd} (from ABC). J_A'+J_B'+J_C' = fc[P2] = 2.
# J_A' odd ≥ 1, J_B' even ≥ 0, J_C' odd ≥ 1 → J_A'=1, J_B'=0, J_C'=1.
# So P2 fires EXACTLY in phases (of P1) A and C, and phases (of P3) A and C.

print(f"\n{'='*60}")
print("FIRE COUNT BUDGET AT P2 WHEN BOTH SAND FAIL")
print("If fc[P2]=2, P1's K=(0,1,1), P3's J=(1,0,1). Minimal allocation.")

# Now: P2's 2 firings must land in specific phases of P1 AND P3.
# A firing of P2 at step s has cycle[s][1] = k1 (P1 phase) and cycle[s][3] = k3 (P3 phase).
# This firing contributes to K_{k1} of P1 AND J_{k3} of P3.

# The 2 P2 firings contribute to P1's phases B and C (one each)
# and to P3's phases A' and C' (one each).
# But which P3 phase is A' depends on the cycle structure.

# Let's trace exactly which (P1-phase, P3-phase) each P2 firing lands in.
p2_phase_pairs = Counter()
for word, cycle in both_sand_fail:
    ell = len(word)
    for s in range(ell):
        if word[s] == 2:  # P2 fires
            p1_phase = cycle[s][1]
            p3_phase = cycle[s][3]
            p2_phase_pairs[(p1_phase, p3_phase)] += 1

print(f"\n  P2 firing lands in (P1-phase, P3-phase): {dict(sorted(p2_phase_pairs.items()))}")

# Similarly for P0 and P4
p0_phase_pairs = Counter()
p4_phase_pairs = Counter()
for word, cycle in both_sand_fail:
    ell = len(word)
    for s in range(ell):
        if word[s] == 0:
            p1_phase = cycle[s][1]
            p6_phase = cycle[s][6]
            p0_phase_pairs[(p1_phase, p6_phase)] += 1
        elif word[s] == 4:
            p3_phase = cycle[s][3]
            p5_phase = cycle[s][5]
            p4_phase_pairs[(p3_phase, p5_phase)] += 1

print(f"  P0 firing lands in (P1-phase, P6-phase): {dict(sorted(p0_phase_pairs.items()))}")
print(f"  P4 firing lands in (P3-phase, P5-phase): {dict(sorted(p4_phase_pairs.items()))}")

# PART 5: The KEY question — does fc[P4]=4 force return at P5?
print(f"\n{'='*60}")
print("DOES fc[P4]=4 FORCE RETURN AT P5?")
print()
print("P5 has 3 phases. Return at phase k: J_k≡0 mod 2 AND K_k≡0 mod 3.")
print("fc[P4]=4: J_0+J_1+J_2=4. Parities: must have 0 or 2 odd values.")
print()
print("Case A (0 odd): All J_k even. For no return, need ALL K_k ∉ {0,3}.")
print("  K_0+K_1+K_2=3 with each ∈ {1,2}. Only option: (1,1,1).")
print("  So anti-return requires K=(1,1,1) — VERY constrained.")
print()
print("Case B (2 odd): 2 phases with J_k odd, 1 with J_k even.")
print("  Only the even-J phase needs K_k ∈ {1,2}. Possible.")

# Actually verify: in the 88 cycles, what are P5's (J,K) per phase?
p5_phases_detail = []
for word, cycle in both_sand_fail:
    phases5 = phase_detail(ms, n, word, cycle, 5)
    jk_tuple = tuple((ph['J'], ph['K']) for ph in phases5)
    p5_phases_detail.append(jk_tuple)

p5_detail_counter = Counter(p5_phases_detail)
print(f"\nP5 phase (J,K) tuples when both sand fail:")
for jk_tuple, cnt in sorted(p5_detail_counter.items(), key=lambda x: -x[1]):
    has_ret = any(j % 2 == 0 and k % 3 == 0 for j, k in jk_tuple)
    print(f"  {jk_tuple}: {cnt}  {'RET' if has_ret else 'NO-RET'}")

# PART 6: What about fc[P6] distribution?
p6_phases_detail = []
for word, cycle in both_sand_fail:
    phases6 = phase_detail(ms, n, word, cycle, 6)
    jk_tuple = tuple((ph['J'], ph['K']) for ph in phases6)
    p6_phases_detail.append(jk_tuple)

p6_detail_counter = Counter(p6_phases_detail)
print(f"\nP6 phase (J,K) tuples when both sand fail:")
for jk_tuple, cnt in sorted(p6_detail_counter.items(), key=lambda x: -x[1]):
    has_ret = any(j % ms[5] == 0 and k % ms[0] == 0 for j, k in jk_tuple)
    print(f"  {jk_tuple}: {cnt}  {'RET' if has_ret else 'NO-RET'}")

# PART 7: General n test — verify both-sand-fail → fixed fc pattern
print(f"\n{'='*60}")
print("GENERALITY: TEST AT n=5,6 (alternating and non-alternating)")

for test_n, test_ms, test_max in [
    (5, [2,3,2,3,2], 20),
    (6, [2,3,2,3,2,3], 24),
]:
    t1 = time.time()
    w = enumerate_mover_words(test_ms, test_n, test_max)
    print(f"\n  n={test_n}, ms={test_ms}, max_len={test_max}: {len(w)} words ({time.time()-t1:.1f}s)")

    sandwiched = [p for p in range(test_n) if test_ms[p] >= 3
                  and test_ms[(p-1)%test_n] == 2 and test_ms[(p+1)%test_n] == 2]

    total_here = 0
    all_sand_fail = 0
    all_sand_fail_fc = Counter()

    for word in w:
        cycle = build_cycle(test_ms, test_n, word)
        if cycle is None or not is_wrap_adjacent(word, test_n):
            continue
        total_here += 1

        if all(not has_entry_conflict_at(test_ms, test_n, word, cycle, s) for s in sandwiched):
            all_sand_fail += 1
            fc = Counter(word)
            fc_key = tuple(fc.get(p, 0) for p in range(test_n))
            all_sand_fail_fc[fc_key] += 1

    print(f"  Total: {total_here}, Sandwiched={sandwiched}")
    print(f"  ALL sand fail: {all_sand_fail}")
    for fc_key, cnt in sorted(all_sand_fail_fc.items(), key=lambda x: -x[1]):
        print(f"    fc={list(fc_key)}: {cnt}")

print(f"\nTotal: {time.time()-t0:.1f}s")
