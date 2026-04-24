#!/usr/bin/env python3
"""Parity pigeonhole proof for entry conflict complementarity.

KEY INSIGHT: If sandwiched ternary P1 (between P0,P2) has ALL phases anti-diagonal:
- Phase parities of (P0_fires, P2_fires) must be {A=(odd,even), B=(even,odd), C=(odd,odd)}
  (exactly one of each type, forced by parity constraints)
- This forces fc[0] = odd+even+odd = even ✓, fc[2] = even+odd+odd = even ✓

COUPLING: If P3 also fails, same analysis → P4 fire count constraints.
The fire counts at P4 then force non-sandwiched P5 to have FR.

This script verifies the parity structure and tests whether
the analytical parity pigeonhole correctly predicts complementarity.
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

def phase_parities(ms, n, word, cycle, p):
    """Get parity of (bL_fires, bR_fires) per phase of p."""
    ell = len(word)
    bL, bR = (p-1) % n, (p+1) % n
    parities = []
    for k in range(ms[p]):
        steps = [s for s in range(ell) if cycle[s][p] == k]
        J = sum(1 for s in steps if word[s] == bL)
        K = sum(1 for s in steps if word[s] == bR)
        parities.append((J % 2, K % ms[bR]))  # parity for bL, residue for bR
    return parities

def has_return_phase(ms, n, word, cycle, p):
    """Return = bL ≡ 0 mod m_bL AND bR ≡ 0 mod m_bR."""
    ell = len(word)
    bL, bR = (p-1) % n, (p+1) % n
    for k in range(ms[p]):
        steps = [s for s in range(ell) if cycle[s][p] == k]
        J = sum(1 for s in steps if word[s] == bL)
        K = sum(1 for s in steps if word[s] == bR)
        if J % ms[bL] == 0 and K % ms[bR] == 0:
            return True
    return False

def has_fr_at(ms, n, word, cycle, p):
    """Entry conflict = same (L,S,R) at mover and nonmover."""
    ell = len(word)
    bL, bR = (p-1) % n, (p+1) % n
    mover, nonmover = set(), set()
    for s in range(ell):
        lsr = (cycle[s][bL], cycle[s][p], cycle[s][bR])
        if word[s] == p:
            mover.add(lsr)
        else:
            nonmover.add(lsr)
    return bool(mover & nonmover)

print("=" * 70)
print("PARITY PIGEONHOLE ANALYSIS")
print("=" * 70)

n, ms = 7, [2, 3, 2, 3, 2, 3, 3]
max_len = 24

t0 = time.time()
words = enumerate_mover_words(ms, n, max_len)
print(f"Words: {len(words)} ({time.time()-t0:.1f}s)")

total = 0
# Analytical prediction: phase parity types
# For sandwiched P1 (bL=P0 mod 2, bR=P2 mod 2):
# Type A: bLf odd, bRf even → parity (1,0)
# Type B: bLf even, bRf odd → parity (0,1)
# Type C: bLf odd, bRf odd → parity (1,1)
# Both-Even (return): parity (0,0)

parity_type_counts = Counter()  # for P1 when it all-fails
p1_all_fail_parity_tuples = Counter()
p3_all_fail_parity_tuples = Counter()

# When both sand fail: what's fc[4]?
both_sand_fail_fc4 = Counter()
both_sand_fail_fc0 = Counter()

# Verify: does parity pigeonhole predict correctly?
parity_correct = 0
parity_wrong = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    total += 1

    # P1 phase parities (mod 2 for both neighbors since both binary)
    ell = len(word)
    p1_par = []
    for k in range(ms[1]):
        steps = [s for s in range(ell) if cycle[s][1] == k]
        J = sum(1 for s in steps if word[s] == 0)  # P0 fires
        K = sum(1 for s in steps if word[s] == 2)  # P2 fires
        p1_par.append((J % 2, K % 2))

    p1_has_return = any(j == 0 and k == 0 for j, k in p1_par)
    p1_fr = has_fr_at(ms, n, word, cycle, 1)

    if not p1_fr:  # P1 all-fails
        sorted_par = tuple(sorted(p1_par))
        p1_all_fail_parity_tuples[sorted_par] += 1

    # P3 phase parities
    p3_par = []
    for k in range(ms[3]):
        steps = [s for s in range(ell) if cycle[s][3] == k]
        J = sum(1 for s in steps if word[s] == 2)  # P2 fires
        K = sum(1 for s in steps if word[s] == 4)  # P4 fires
        p3_par.append((J % 2, K % 2))

    p3_has_return = any(j == 0 and k == 0 for j, k in p3_par)
    p3_fr = has_fr_at(ms, n, word, cycle, 3)

    if not p3_fr:
        sorted_par = tuple(sorted(p3_par))
        p3_all_fail_parity_tuples[sorted_par] += 1

    # When both sand fail
    if not p1_fr and not p3_fr:
        fc = Counter(word)
        both_sand_fail_fc4[fc[4]] += 1
        both_sand_fail_fc0[fc[0]] += 1

    # Verify parity prediction:
    # "Return phase exists ↔ some phase has (0,0) parity"
    if p1_has_return == p1_fr:
        parity_correct += 1
    else:
        parity_wrong += 1

    # Verify the ABC classification for P1 all-fail
    if not p1_fr and not p1_has_return:
        for j, k in p1_par:
            parity_type_counts[(j, k)] += 1

print(f"Total: {total}")

# PART 1: Parity type analysis when P1 all-fails
print(f"\n{'='*60}")
print("P1 ALL-FAIL PARITY ANALYSIS")
print(f"P1 phase parity tuples (sorted) when P1 has no FR:")
for par_tuple, cnt in sorted(p1_all_fail_parity_tuples.items(), key=lambda x: -x[1]):
    print(f"  {par_tuple}: {cnt}")

print(f"\nParity type distribution at P1 when all-fail (no return):")
for (j, k), cnt in sorted(parity_type_counts.items()):
    label = {(0,0): 'RETURN', (0,1): 'B', (1,0): 'A', (1,1): 'C'}[(j,k)]
    print(f"  ({j},{k}) = {label}: {cnt}")

print(f"\nPrediction: return ↔ FR correctness: {parity_correct}/{total} "
      f"({100*parity_correct/total:.1f}%)")
print(f"  Return but no FR (non-return FR needed): {parity_wrong}")

# PART 2: When both sand fail, fc analysis
print(f"\n{'='*60}")
print("WHEN BOTH P1 AND P3 FAIL:")
print(f"  fc[4] distribution: {dict(sorted(both_sand_fail_fc4.items()))}")
print(f"  fc[0] distribution: {dict(sorted(both_sand_fail_fc0.items()))}")

# PART 3: Analytical parity pigeonhole proof verification
print(f"\n{'='*60}")
print("PARITY PIGEONHOLE VERIFICATION")
print()
print("THEOREM: If sandwiched ternary P (between binary bL, bR) has")
print("ALL 3 phases failing Both-Even, then the parity tuple is")
print("{(1,0), (0,1), (1,1)} (exactly one A, one B, one C).")
print()
print("PROOF: P has 3 phases with parities (j_k, k_k) in {0,1}^2 \\ {(0,0)}.")
print("  fc[bL] = Σ J_k ≡ 0 mod 2 → # odd J_k is even (0 or 2).")
print("  fc[bR] = Σ K_k ≡ 0 mod 2 → # odd K_k is even (0 or 2).")
print("  Each phase excludes (0,0), so each is A=(1,0), B=(0,1), or C=(1,1).")
print()
print("  If #A + #C = # odd J values: must be 0 or 2.")
print("  If #B + #C = # odd K values: must be 0 or 2.")
print("  #A + #B + #C = 3.")
print()
print("  Case #A+#C = 0: #A=#C=0, #B=3. Then #B+#C=3 (odd). CONTRADICTION.")
print("  Case #A+#C = 2: #B = 1. Then #B+#C = 1+#C. Must be even → #C odd.")
print("    #A + #C = 2 and #C odd → #C = 1, #A = 1. #B = 1. ✓")
print()
print("  So exactly #A=1, #B=1, #C=1. QED.")

# Verify against data
all_abc = all(par == ((0,1), (1,0), (1,1)) for par in p1_all_fail_parity_tuples.keys())
print(f"\n  Data confirms: all P1-fail cycles have ABC parity? {all_abc}")
total_abc = sum(p1_all_fail_parity_tuples.values())
print(f"  Total P1-fail cycles: {total_abc}")

# PART 4: Consequence for P4 fire count
print(f"\n{'='*60}")
print("CONSEQUENCE: FC[4] WHEN BOTH SANDWICHED FAIL")
print()
print("If P3 also has ABC parity: K₃ parities = {even, odd, odd}.")
print("  fc[4] = K₃_A + K₃_B + K₃_C = even + odd + odd.")
print("  Minimum: 0 + 1 + 1 = 2.")
print()
print("Similarly fc[0] ≥ 2 from P1's J₁ parities = {odd, even, odd}.")
print("  fc[0] = J₁_A + J₁_B + J₁_C = odd + even + odd ≥ 1+0+1 = 2.")

# PART 5: Test the MINIMUM case
# Can fc[4]=2 coexist with both sand failing?
print(f"\n{'='*60}")
print("CRITICAL: CAN fc[4]=2 COEXIST WITH BOTH SAND FAILING?")

if both_sand_fail_fc4:
    min_fc4 = min(both_sand_fail_fc4.keys())
    print(f"  Minimum fc[4] observed: {min_fc4}")
    print(f"  fc[4]=2 count: {both_sand_fail_fc4.get(2, 0)}")
    print(f"  fc[4]=4 count: {both_sand_fail_fc4.get(4, 0)}")
else:
    print(f"  No cycles where both sand fail (max_len too small?)")

# PART 6: What about the non-sandwiched ternary?
# P5 (between P4(2) and P6(3)):
# Return needs J%2=0 AND K%3=0
# Toggle-path FR: J≥3 gives (3,0) which always has FR
# (proven: path through (1,0) G-point)
print(f"\n{'='*60}")
print("P5 RETURN/FR MECHANISM WHEN BOTH SAND FAIL")

both_fail_p5_has_return = 0
both_fail_p5_has_fr = 0
both_fail_p5_mechanism = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    p1_fr = has_fr_at(ms, n, word, cycle, 1)
    p3_fr = has_fr_at(ms, n, word, cycle, 3)
    if p1_fr or p3_fr:
        continue

    # Both sand fail. Check P5.
    p5_ret = has_return_phase(ms, n, word, cycle, 5)
    p5_fr = has_fr_at(ms, n, word, cycle, 5)

    if p5_ret:
        both_fail_p5_has_return += 1
    if p5_fr:
        both_fail_p5_has_fr += 1

    # Classify P5's mechanism
    ell = len(word)
    for k in range(ms[5]):
        steps = [s for s in range(ell) if cycle[s][5] == k]
        J = sum(1 for s in steps if word[s] == 4)
        K = sum(1 for s in steps if word[s] == 6)

        # Check FR at this phase
        mover_lr = set()
        nonmover_lr = set()
        for s in steps:
            lr = (cycle[s][4], cycle[s][6])
            if word[s] == 5:
                mover_lr.add(lr)
            else:
                nonmover_lr.add(lr)
        has_phase_fr = bool(mover_lr & nonmover_lr)

        if has_phase_fr:
            if J % 2 == 0 and K % 3 == 0:
                both_fail_p5_mechanism['return'] += 1
            elif J >= 3 and K == 0:
                both_fail_p5_mechanism['toggle_path_J3'] += 1
            elif J >= 2 and J % 2 == 0:
                both_fail_p5_mechanism['J_even_nonreturn'] += 1
            else:
                both_fail_p5_mechanism['other'] += 1

total_both_fail = sum(1 for _ in range(1) if both_sand_fail_fc4)  # hack
total_both_fail = sum(both_sand_fail_fc4.values())
print(f"Both sand fail: {total_both_fail} cycles")
print(f"  P5 has return phase: {both_fail_p5_has_return}/{total_both_fail}")
print(f"  P5 has FR: {both_fail_p5_has_fr}/{total_both_fail}")
print(f"  P5 FR mechanism: {dict(both_fail_p5_mechanism)}")

print(f"\nTotal: {time.time()-t0:.1f}s")
