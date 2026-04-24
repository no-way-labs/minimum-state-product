#!/usr/bin/env python3
"""Check: does BothEven/ToggleFR always fire for EVERY phase of
EVERY processor with both binary neighbors, under sub-threshold?

Key insight: if it does, palindromic_phase_ec is vacuously true
(the _hnormal hypothesis is False).

Focus on proving: for any sandwiched phase with n>=9,
(Even J ∧ Even K) ∨ (J >= 2 ∧ K = 0) ∨ (J = 0 ∧ K >= 2).

Counter-examples are (J,K) pairs NOT in these sets:
- (1,0), (0,1): one fire, other zero
- (1,1): one each
- (J,K) with J odd, K odd, both >= 1
- (J,K) with J even >=2, K odd >= 1
- (J,K) with J odd >= 1, K even >= 2

Let me check: for phase_len = 1 (s = a+1), what are J and K?
Phase has 1 step: step a. So J = (1 if moverAt(a) = left(t) else 0),
K = (1 if moverAt(a) = right(t) else 0).
J + K <= 1.
Possible: (0,0) — but ¬BothEven excludes this.
So (1,0) or (0,1) if phase_len=1.

For phase_len >= 2: more room for mechanisms.

Key question: can the phase have length 1 when n >= 9?
Phase length = s - a. From exists_ternaryPhase:
- a is the step after the previous fire of t
- s is the next fire of t
If t fires at consecutive steps, phase_len = 1.
Can t fire at consecutive steps?

moverAt(a) != t (from TernaryPhase). moverAt(a+1) = t (if s = a+1).
So at config a: someone else fires. At config a+1: t fires.
This means t fires, then at config a (after some other procs fire),
someone else fires, then t fires again.

Actually, the phase comes from consecutive fires of t.
t fires at step s (the current fire) and at step prev (the previous fire).
a = prev + 1. s could be prev + 1 if t fires at consecutive steps? No:
t fires at prev, then at a = prev+1, moverAt != t (since we need ht_nofire).
Actually moverAt(a) != t is required. If a = prev+1 and moverAt(prev) = t:
after t fires, the next step's mover is determined by unique_privileged.
If t is still privileged after firing, moverAt(prev+1) = t again. But then
a would not be a valid start (moverAt(a) = t violates ha_nonmover).

So the phase construction finds a valid starting point where t is NOT the mover.
If t fires at consecutive steps prev, prev+1: a = prev+1 but moverAt(prev+1) = t.
This violates ha_nonmover, so the phase construction would skip this and find a
different phase.

Actually, can t fire at consecutive steps? If moverAt(prev) = t and moverAt(prev+1) = t:
at config prev: t privileged. After fire: config prev+1. At config prev+1: t still
privileged? Only if f(L', S', R') != S' where S' is the NEW value of t.
For a ternary t (m=3): S' != S (t just fired to a different value).
Whether t is still privileged depends on f. It's possible.

For binary t (m=2): S' = 1-S. Whether t is still privileged at (L', 1-S, R')
depends on f.

So t CAN fire at consecutive steps. In this case, every phase would have length >= 2
(the construction skips phases where a is also a fire step of t).

Hmm, actually the exists_ternaryPhase proof handles this. It finds a phase where
a is a NON-fire step for t. If t fires at every step (all movers = t), then no
such a exists. But fireCount(t) < configs.length means t doesn't fire at every step.

So phase_len >= 1 is guaranteed. Can phase_len = 1?
a is a non-fire step for t. s = a+1 is a fire step for t. Phase [a, a+1) has
length 1. In this phase, exactly 1 step (step a) where moverAt(a) != t.
J + K <= 1. Normal form can occur.

Can this happen at n >= 9? If t fires many times and other procs fire between
some fires but not others, there could be a gap of just 1 step.

For convergence: the system must terminate from any non-good config. This
heavily constrains the transition functions but doesn't directly prevent
phase_len = 1.

Let me check: does phase_len = 1 occur in actual sub-threshold systems?
"""

# Let me check with the CLB witness at n=9
# ms = (2,3,3,3,3,3,3,3,2), product = 8748

import sys, random
sys.path.insert(0, './claude')

def check_normal_form(J, K):
    if J % 2 == 0 and K % 2 == 0:
        return False
    if J >= 2 and K == 0:
        return False
    if J == 0 and K >= 2:
        return False
    return True

def privileged(config, sys_f, ms, n, i):
    L = config[(i - 1) % n]
    S = config[i]
    R = config[(i + 1) % n]
    return sys_f[i][(L, S, R)] != S

def find_unique_privileged(config, sys_f, ms, n):
    privs = [i for i in range(n) if privileged(config, sys_f, ms, n, i)]
    return privs[0] if len(privs) == 1 else None

def apply_move(config, sys_f, ms, n, i):
    new_config = list(config)
    L = config[(i - 1) % n]
    S = config[i]
    R = config[(i + 1) % n]
    new_config[i] = sys_f[i][(L, S, R)]
    return tuple(new_config)

# Try to import the verifier
try:
    from probes.clb_witness_8748 import build_witness
    print("Using CLB witness")
except:
    print("CLB witness not available, using manual construction")

# Let's just test with manually constructed sub-threshold systems
# For ms = (2,3,3,3,3,3,3,3,2) at n=9, product = 2*3^7*2 = 8748 = 4*3^7
# This is at the THRESHOLD, not sub-threshold.

# For sub-threshold: product < 4*3^7 = 8748
# E.g., ms = (2,2,2,3,3,3,3,3,3), product = 8*3^6 = 5832 < 8748 ✓

# The key insight: in actual systems being analyzed (sub-threshold with n>=9),
# can phase_len = 1 ever occur?

# Instead of generating random systems, let me PROVE that phase_len >= 2
# under the given constraints.

# Hypothesis: In a good cycle where t has both binary neighbors, n >= 9,
# and hno_safe, every phase of t has length >= 2.

# Phase length = gap between consecutive fires of t.
# If phase_len = 1: t fires at step s, previous fire at step s-2 (with s-1 being non-t).
# At step s-1: some other proc fires. At step s: t fires again.

# The question: does hno_safe prevent short phases?

# hno_safe: for every q, ∃ k: moverAt(k) ∈ {q, left(q), right(q)}.
# This means the mover visits every processor's neighborhood.
# With n >= 9: at least 9 processors. Each needs their neighborhood visited.
# If t fires at most L/2 times (L = cycle length), there are >= L/2 non-t steps.
# These steps must cover all neighborhoods.

# For short phases: if ALL phases of t have length 1, then t fires at every other step.
# L = 2F where F is fire count of t. L/2 non-t steps must visit all n neighborhoods.
# With n >= 9: possible but constrained.

# Let me check: what fraction of phases have length 1 vs >= 2?
# I'll generate systems exhaustively for small n.

print("\n=== Checking phase lengths ===\n")

def exhaustive_check(n, ms, max_tables=100000):
    """Exhaustively check all transition tables for short phases."""
    from itertools import product as iprod

    short_phase_count = 0
    total_phase_count = 0
    total_cycles = 0

    # For each processor t with both binary neighbors
    sandwiched = [t for t in range(n) if ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

    # Random sample of transition tables
    for trial in range(max_tables):
        # Random transition
        sys_f = {}
        for i in range(n):
            m_l = ms[(i-1)%n]
            m_s = ms[i]
            m_r = ms[(i+1)%n]
            sys_f[i] = {}
            for L in range(m_l):
                for S in range(m_s):
                    for R in range(m_r):
                        sys_f[i][(L,S,R)] = random.randint(0, m_s-1)

        # Find good cycle
        config = tuple(random.randint(0, ms[i]-1) for i in range(n))
        visited = {}
        for step in range(3000):
            if config in visited:
                start = visited[config]
                cycle = []
                c = config
                valid = True
                for _ in range(step - start):
                    p = find_unique_privileged(c, sys_f, ms, n)
                    if p is None:
                        valid = False
                        break
                    cycle.append((c, p))
                    c = apply_move(c, sys_f, ms, n, p)
                if not valid or len(cycle) == 0:
                    break

                total_cycles += 1
                L = len(cycle)
                movers = [cycle[k][1] for k in range(L)]

                for t in sandwiched:
                    fire_steps = [k for k in range(L) if movers[k] == t]
                    if len(fire_steps) < 2:
                        continue

                    for idx in range(len(fire_steps)):
                        s_step = fire_steps[idx]
                        prev = fire_steps[(idx-1) % len(fire_steps)]
                        if prev < s_step:
                            phase_len = s_step - prev - 1
                            if phase_len >= 1:  # Valid phase
                                total_phase_count += 1
                                a = prev + 1
                                # Check normal form
                                lt = (t-1) % n
                                rt = (t+1) % n
                                J = sum(1 for k in range(a, s_step) if movers[k] == lt)
                                K = sum(1 for k in range(a, s_step) if movers[k] == rt)
                                if check_normal_form(J, K):
                                    short_phase_count += 1
                                    if short_phase_count <= 5:
                                        print(f"  NF phase: n={n} t={t}(m={ms[t]}) "
                                              f"J={J} K={K} plen={s_step-a}")
                break
            visited[config] = step
            p = find_unique_privileged(config, sys_f, ms, n)
            if p is None:
                break
            config = apply_move(config, sys_f, ms, n, p)

    return total_cycles, total_phase_count, short_phase_count

import random
random.seed(456)

for n, ms in [(5, [2,2,2,3,3]), (5, [2,3,2,3,3]), (7, [2,2,2,3,3,3,3]),
              (9, [2,2,2,3,3,3,3,3,3]), (9, [2,3,2,3,3,3,3,3,3])]:
    nc, np, ns = exhaustive_check(n, ms, max_tables=50000)
    print(f"n={n} ms={ms}: {nc} cycles, {np} phases, {ns} normal-form")
    print()

# The key question: are ALL normal-form phases at phase_len=1?
# If so, and we can prove phase_len >= 2 under n>=9 + hno_safe + converges,
# then palindromic_phase_ec is vacuously true.
