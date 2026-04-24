"""
Deeper analysis: what property do the n=3 counterexamples lack?

The H-1 Uniqueness Lemma works for SWEEP cycles in the LB proof.
Maybe the lemma requires sweep structure (displacement >= 2n).

Also: the LB proof uses this lemma in a specific way — to show that
a shifted config stays non-good. Maybe that's what really needs proof,
not the H-1 Uniqueness per se.

Let me analyze the counterexample cycle in detail.
"""

# The example
ms = [2, 3, 3]
n = 3
CL = 8
word = (1, 1, 2, 0, 2, 2, 1, 0)
configs = [(0,0,0), (0,2,0), (0,1,0), (0,1,2), (1,1,2), (1,1,1), (1,1,0), (1,0,0)]

print("Cycle structure:")
for s in range(CL):
    c = configs[s]
    m = word[s]
    print(f"  step {s}: config={c}, mover=proc {m}")

# Displacement analysis
# CW step: mover position increases
# CCW step: mover position decreases
displacements = []
for s in range(CL):
    m = word[s]
    m_prev = word[(s-1) % CL]
    displacements.append(m - m_prev)

print(f"\nMover sequence: {list(word)}")
print(f"Displacements: {displacements}")

# Net displacement
# Actually, displacement is defined by the walk direction
# CW mover: mover(s) = (mover(s-1) + 1) mod n
# CCW mover: mover(s) = (mover(s-1) - 1) mod n
# Stay: mover(s) = mover(s-1)

cw = sum(1 for s in range(CL) if word[s] == (word[(s-1)%CL] + 1) % n)
ccw = sum(1 for s in range(CL) if word[s] == (word[(s-1)%CL] - 1) % n)
stay = sum(1 for s in range(CL) if word[s] == word[(s-1)%CL])
other = CL - cw - ccw - stay
print(f"CW={cw}, CCW={ccw}, Stay={stay}, Other={other}")
print(f"Net displacement (CW - CCW) = {cw - ccw}")

# Check if this is a sweep
# A sweep has |net displacement| >= 2n (the mover goes around the ring at least twice)
# With n=3 and CL=8: max possible displacement = 8 (all CW).
# Sweep threshold: 2*3 = 6.
is_sweep = abs(cw - ccw) >= 2 * n
print(f"Sweep? {is_sweep} (|{cw}-{ccw}| = {abs(cw-ccw)} vs threshold {2*n})")

# Fire count pattern
fc = [sum(1 for m in word if m == i) for i in range(n)]
print(f"Fire counts: {fc} (ms={ms})")

# The key: what kind of cycle IS this?
# It's NOT a sweep (displacement = 0 or small).
# It has back-and-forth (1,1,2,0,2,2,1,0).
# This is a "wiggle" or "balanced" cycle.

# The H-1 Uniqueness Lemma in the LB proof is used for:
# 1. Sweep non-consecutive (Case D2): need H-1 to show shadow trap
# 2. Implicitly in other cases

# For SWEEP cycles: the mover word has a specific structure
# (goes around the ring in one direction). Let me check if sweep
# cycles at n=3 have non-adjacent H-1 pairs.

print("\n" + "=" * 70)
print("Checking: do SWEEP cycles have non-adjacent H-1 pairs?")
print("=" * 70)

import itertools

def hamming_distance(c1, c2):
    return sum(1 for a, b in zip(c1, c2) if a != b)

def enumerate_mover_words(ms):
    base = []
    for i in range(len(ms)):
        base.extend([i]*ms[i])
    return set(itertools.permutations(base))

ms_test = [2, 3, 3]
n = 3
CL = sum(ms_test)
mover_words = list(enumerate_mover_words(ms_test))
all_cfgs = list(itertools.product(range(2), range(3), range(3)))

# Classify mover words by displacement
sweep_nonadj = 0
nonsweep_nonadj = 0
sweep_total = 0
nonsweep_total = 0

for word in mover_words:
    # Compute displacement
    cw = sum(1 for s in range(CL) if word[s] == (word[(s-1)%CL] + 1) % n)
    ccw = sum(1 for s in range(CL) if word[s] == (word[(s-1)%CL] - 1) % n)
    disp = cw - ccw
    is_sweep = abs(disp) >= 2 * n

    for start in all_cfgs:
        stack = [(0, start, [start])]
        while stack:
            step, current, path = stack.pop()
            if step == CL:
                if current == start and len(set(path[:CL])) == CL:
                    configs = path[:CL]
                    has_nonadj = False
                    for j in range(CL):
                        for k in range(j+1, CL):
                            if hamming_distance(configs[j], configs[k]) == 1:
                                d = k - j
                                if 1 < d < CL - 1:
                                    has_nonadj = True
                                    break
                        if has_nonadj:
                            break

                    if is_sweep:
                        sweep_total += 1
                        if has_nonadj:
                            sweep_nonadj += 1
                    else:
                        nonsweep_total += 1
                        if has_nonadj:
                            nonsweep_nonadj += 1
                continue
            mover = word[step]
            for new_val in range(ms_test[mover]):
                if new_val != current[mover]:
                    new_cfg = list(current)
                    new_cfg[mover] = new_val
                    stack.append((step+1, tuple(new_cfg), path + [tuple(new_cfg)]))

print(f"Sweep cycles: total={sweep_total}, with non-adj H-1={sweep_nonadj}")
print(f"Non-sweep cycles: total={nonsweep_total}, with non-adj H-1={nonsweep_nonadj}")

if sweep_nonadj == 0:
    print("\n*** SWEEP cycles NEVER have non-adjacent H-1 pairs! ***")
    print("The H-1 Uniqueness Lemma IS true for sweeps.")
    print("The document's claim is correct — it's applied only in the sweep case.")

# Also check: for all-ternary (3,3,3) — where gcd = 3
print("\n" + "=" * 70)
print("Check: ms=(3,3,3) — gcd=3")
print("=" * 70)

ms_333 = [3, 3, 3]
CL_333 = 9
words_333 = list(enumerate_mover_words(ms_333))

sweep_333 = 0
nonadj_333 = 0

for word in words_333:
    cw = sum(1 for s in range(CL_333) if word[s] == (word[(s-1)%CL_333] + 1) % 3)
    ccw = sum(1 for s in range(CL_333) if word[s] == (word[(s-1)%CL_333] - 1) % 3)
    is_sweep = abs(cw - ccw) >= 6

    for start in list(itertools.product(range(3), range(3), range(3)))[:5]:  # Sample
        stack = [(0, start, [start])]
        while stack:
            step, current, path = stack.pop()
            if step == CL_333:
                if current == start and len(set(path[:CL_333])) == CL_333:
                    configs = path[:CL_333]
                    if is_sweep:
                        sweep_333 += 1
                        for j in range(CL_333):
                            for k in range(j+1, CL_333):
                                if hamming_distance(configs[j], configs[k]) == 1:
                                    d = k - j
                                    if 1 < d < CL_333 - 1:
                                        nonadj_333 += 1
                                        break
                            else:
                                continue
                            break
                continue
            mover = word[step]
            for new_val in range(3):
                if new_val != current[mover]:
                    new_cfg = list(current)
                    new_cfg[mover] = new_val
                    stack.append((step+1, tuple(new_cfg), path + [tuple(new_cfg)]))

print(f"Sweep cycles (ms=(3,3,3)): {sweep_333}, with non-adj H-1: {nonadj_333}")
