#!/usr/bin/env python3
"""
RA Part 2: Investigate same-mover bad cycles for stuttered sweeps.

Key finding from Part 1: constant offset doesn't work, BFS bad cycle has
DIFFERENT movers from good cycle.

New approach: For a sweep, every proc is a mover at some step. At step s with
mover p, the context (L,S,R) at the good config determines the forced entry.
If we want a bad cycle with the SAME movers, we need the SAME contexts at
the bad config so that the mover is privileged and fires to the correct next.

But if contexts must be identical, and the mover visits every position, then
the bad config must equal the good config at every position — contradiction
with disjointness!

UNLESS: contexts don't need to be identical, just need to produce the same
privilege and same transition result through a DIFFERENT entry.

Wait — actually for the step property, we need:
  move(bad[s], mover_s) = bad[s+1]
This means: at bad[s], mover p is privileged, and firing p gives bad[s+1].
The transition f_p(L,S,R) at bad[s] might use a DIFFERENT (L,S,R) than the
good cycle, but must still produce a valid transition.

So the bad cycle can have different contexts than the good cycle, as long as
the mover is privileged and the transition is consistent.

This is the forced-entry approach: any config where some mover context matches
a forced entry, the transition is determined. The forced entries create a
"shadow graph" of transitions among non-good configs.

Let me investigate systematically:
1. What bad cycles exist with same movers as good cycle?
2. What bad cycles exist with ANY movers (forced entries only)?
"""

import itertools
from collections import defaultdict

def enumerate_exact_fc_words(ms, n, target_fc):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    total_len = sum(target_fc[p] for p in range(n))
    results = []
    def dfs(word, fc):
        if len(word) == total_len:
            if abs(word[-1] - word[0]) % n in (1, n-1):
                config = [0]*n
                for p in word:
                    config[p] = (config[p]+1) % ms[p]
                if all(c == 0 for c in config):
                    results.append(tuple(word))
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            if fc[nxt] < target_fc[nxt]:
                fc[nxt] += 1
                word.append(nxt)
                remaining = total_len - len(word)
                needed = sum(target_fc[p] - fc[p] for p in range(n))
                if needed <= remaining:
                    dfs(word, fc)
                word.pop()
                fc[nxt] -= 1
    for p in range(n):
        if target_fc[p] > 0:
            fc = {q: 0 for q in range(n)}
            fc[p] = 1
            dfs([p], fc)
    return results

def build_cycle(ms, n, word):
    ell = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p]+1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]: return None
    if len(set(configs[:ell])) != ell: return None
    return configs[:ell]

def canonicalize_word(word):
    best = word
    for i in range(len(word)):
        rot = word[i:] + word[:i]
        if rot < best: best = rot
    return best

def compute_displacement(word, n):
    total = 0
    ell = len(word)
    for i in range(ell):
        diff = (word[(i+1)%ell] - word[i]) % n
        if diff == 1: total += 1
        elif diff == n-1: total -= 1
    return total

def enumerate_state_sequences(m, k):
    seqs = []
    def dfs(seq, remaining):
        if remaining == 0:
            if seq[-1] == 0: seqs.append(tuple(seq))
            return
        for nv in range(m):
            if nv != seq[-1]:
                if remaining == 1 and nv != 0: continue
                seq.append(nv)
                dfs(seq, remaining-1)
                seq.pop()
    dfs([0], k)
    return seqs

def get_good_cycle_with_combo(ms, n, word, combo):
    ell = len(word)
    fc_num = [0]*ell
    pc = [0]*n
    for s in range(ell):
        fc_num[s] = pc[word[s]]
        pc[word[s]] += 1
    configs = []
    state = [0]*n
    for s in range(ell):
        configs.append(tuple(state))
        p = word[s]
        state[p] = combo[p][fc_num[s]+1]
    return configs, fc_num

# ============================================================
# Setup
# ============================================================
n = 9
ms = [2,3,3,2,3,3,2,3,3]
target_fc = {p: ms[p] for p in range(n)}

words = enumerate_exact_fc_words(ms, n, target_fc)
seen = set()
unique = []
for w in words:
    canon = canonicalize_word(w)
    if canon not in seen:
        seen.add(canon)
        unique.append(w)
valid = []
for w in unique:
    cycle = build_cycle(ms, n, w)
    if cycle is not None:
        valid.append((w, cycle))
sweeps = [(w, c, compute_displacement(w, n)) for w, c in valid if abs(compute_displacement(w, n)) == 2*n]

w0, _, d0 = sweeps[0]
ell = len(w0)
combo0 = tuple(enumerate_state_sequences(ms[p], ms[p])[0] for p in range(n))
gc_configs, fc_num = get_good_cycle_with_combo(ms, n, w0, combo0)
good_set = set(gc_configs)

# Build forced mover entries
mcx = defaultdict(dict)
for s in range(ell):
    p = w0[s]
    L = gc_configs[s][(p-1)%n]; S = gc_configs[s][p]; R = gc_configs[s][(p+1)%n]
    mcx[p][(L, S, R)] = gc_configs[(s+1)%ell][p]

print("="*72)
print("APPROACH: Same-mover forced-entry cycle search")
print("="*72)

# For each step s, the mover is w0[s]. At a bad config b[s], mover w0[s]
# must be privileged (some (L,S,R) at w0[s] that maps to S' != S).
# The transition at w0[s] must produce b[s+1].
#
# Key constraint: only the 3 context positions matter for the mover.
# The other n-3 positions are "free" — they can be anything, as long as
# they're consistent with the NEXT step's context.
#
# This means: at step s, positions {w0[s]-1, w0[s], w0[s]+1} are constrained
# by the mover. At step s+1, positions {w0[s+1]-1, w0[s+1], w0[s+1]+1} are
# constrained. The transition changes only w0[s].
#
# So: b[s+1] differs from b[s] only at position w0[s].
# And the context at w0[s+1] in b[s+1] involves positions
# {w0[s+1]-1, w0[s+1], w0[s+1]+1}.

# Let me just try a direct search for same-mover bad cycles.
# At each step, we know the mover. We need to find configs b[0..23] such that:
# 1. For each s: firing w0[s] at b[s] gives b[s+1] (using some forced entry)
# 2. b[s] not in good_set for all s
# 3. All b[s] distinct
# 4. The cycle is closed: firing w0[23] at b[23] gives b[0]

# The search space is huge (5832^24). Let me instead use the forced-entry graph.
# For each non-good config c and each mover p = w0[s]:
#   If there exists a forced entry (L,S,R) -> S' with S' != S at position p:
#     Then c transitions to c' = c with c'[p] = S'

# Build the forced-entry transition graph with SAME movers
print(f"\nMover word: {list(w0)}")
print(f"Building same-mover transition graph...")

all_cfgs = list(itertools.product(*(range(m) for m in ms)))
non_good = [c for c in all_cfgs if c not in good_set]
print(f"Non-good configs: {len(non_good)}")

# For each step s, build the forced transition: c -> c' via mover w0[s]
# We want cycles of length 24 using the SPECIFIC mover sequence.
# This is like a composition of 24 functions.

# Build step-specific transitions
step_trans = {}  # step -> {config -> (next_config, mover)}
for s in range(ell):
    p = w0[s]
    trans = {}
    for c in non_good:
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        if (L, S, R) in mcx[p]:
            Sp = mcx[p][(L, S, R)]
            if Sp != S:
                nc = list(c); nc[p] = Sp; nc = tuple(nc)
                if nc not in good_set:
                    trans[c] = nc
    step_trans[s] = trans

# How many configs have a valid transition at each step?
for s in range(ell):
    print(f"  Step {s:2d} (P{w0[s]}): {len(step_trans[s])} configs with forced trans")

# Now compose: start from step 0, apply trans[0], trans[1], ..., trans[23]
# and check if we return to start.
# This is a permutation composition on the set of configs that survive all 24 steps.

# Find configs that can survive all 24 steps
print(f"\nFinding configs surviving full orbit...")
survivors = set(non_good)
for s in range(ell):
    new_survivors = set()
    for c in survivors:
        if c in step_trans[s]:
            new_survivors.add(c)
    survivors = new_survivors
    if not survivors:
        print(f"  No survivors after step {s}")
        break

print(f"Survivors after forward pass: {len(survivors)}")

# Also need backward compatibility: the predecessor at each step must be a survivor
# Iterate until fixed point
for iteration in range(50):
    old_size = len(survivors)

    # Forward: can step s transition to a survivor at step s+1
    for s in range(ell):
        new_survivors = set()
        for c in survivors:
            if c in step_trans[s]:
                nc = step_trans[s][c]
                if nc in survivors:
                    new_survivors.add(c)
        survivors = new_survivors

    # Backward: config at step s+1 must have a predecessor at step s
    # Build inverse
    for s in range(ell):
        inv = defaultdict(set)
        for c in survivors:
            if c in step_trans[s]:
                nc = step_trans[s][c]
                if nc in survivors:
                    inv[nc].add(c)
        new_survivors = set()
        for c in survivors:
            # c must be reachable as output of step (s-1)
            # AND must have a valid transition at step s
            prev_s = (s - 1) % ell
            if c in inv.get(c, set()) or True:  # This logic is wrong, let me redo
                pass
        # Actually this is getting complicated. Let me do it differently.
        break

    if len(survivors) == old_size:
        break

print(f"Survivors after refinement: {len(survivors)}")

# Let me try a cleaner approach: compose the 24 step functions and find fixed points.
print(f"\nComposing 24 step functions...")
# Start with all non-good configs. Apply trans[0], trans[1], ..., trans[23].
# A config c is in a valid bad cycle iff applying all 24 transitions returns to c.

# Compose: f = trans[23] o trans[22] o ... o trans[0]
# f(c) = result of applying all 24 transitions starting from c
current = {}
for c in non_good:
    current[c] = c

for s in range(ell):
    new_current = {}
    for start_c, cur_c in current.items():
        if cur_c in step_trans[s]:
            new_current[start_c] = step_trans[s][cur_c]
    current = new_current

print(f"Configs surviving all 24 steps: {len(current)}")

# Find fixed points: c such that f(c) = c
fixed_points = [c for c, result in current.items() if result == c]
print(f"Fixed points (bad cycle starts): {len(fixed_points)}")

if fixed_points:
    # Extract a bad cycle from the first fixed point
    c0 = fixed_points[0]
    bad_cycle = [c0]
    bad_movers = []
    cur = c0
    for s in range(ell):
        p = w0[s]
        bad_movers.append(p)
        cur = step_trans[s][cur]
        if s < ell - 1:
            bad_cycle.append(cur)

    print(f"\nBad cycle (same movers):")
    print(f"Length: {len(bad_cycle)}")
    print(f"Distinct: {len(set(bad_cycle)) == len(bad_cycle)}")
    print(f"Disjoint from good: {all(c not in good_set for c in bad_cycle)}")

    # Verify step
    step_ok = True
    for s in range(ell):
        p = w0[s]
        c = bad_cycle[s]
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        if (L, S, R) not in mcx[p]:
            step_ok = False
            print(f"  Step {s}: context {(L,S,R)} not in forced entries for P{p}")
            break
        Sp = mcx[p][(L, S, R)]
        nc = list(c); nc[p] = Sp; nc = tuple(nc)
        expected = bad_cycle[(s+1)%ell]
        if tuple(nc) != expected:
            step_ok = False
            print(f"  Step {s}: got {tuple(nc)}, expected {expected}")
            break
    print(f"Step closure: {step_ok}")

    # Offset analysis
    print(f"\nOffset analysis (bad - good):")
    offsets = []
    for s in range(ell):
        d = tuple((bad_cycle[s][p] - gc_configs[s][p]) % ms[p] for p in range(n))
        offsets.append(d)
        print(f"  Step {s:2d}: d={d}  mover=P{w0[s]}")

    unique_offsets = set(offsets)
    print(f"\nUnique offsets: {len(unique_offsets)}")
    is_constant = len(unique_offsets) == 1
    print(f"Constant offset: {is_constant}")
    if is_constant:
        print(f"The offset: {offsets[0]}")

    # Check ALL fixed points
    print(f"\n--- All {len(fixed_points)} fixed points ---")
    # Group by their offset patterns
    offset_patterns = defaultdict(list)
    for c0 in fixed_points:
        bad = [c0]
        cur = c0
        for s in range(ell):
            cur = step_trans[s][cur]
            if s < ell - 1:
                bad.append(cur)
        ds = [tuple((bad[s][p] - gc_configs[s][p]) % ms[p] for p in range(n)) for s in range(ell)]
        if len(set(ds)) == 1:
            offset_patterns[ds[0]].append(c0)
        else:
            offset_patterns['non-constant'].append(c0)

    for key, starts in sorted(offset_patterns.items(), key=lambda x: str(x[0])):
        if key == 'non-constant':
            print(f"  Non-constant offset: {len(starts)} cycles")
        else:
            print(f"  Constant offset d={key}: {len(starts)} cycles")
else:
    print("No same-mover bad cycles exist with forced entries!")
    print("This means the Lean approach must use DIFFERENT movers.")

# ============================================================
# PART 2: What about privilege-preserving but non-forced entries?
# ============================================================
print(f"\n{'='*72}")
print("PART 2: Check what transitions are available (not just forced)")
print("="*72)

# At each step, the mover is w0[s]. For ANY transition function consistent
# with the good cycle, the mover must be privileged. The question is:
# what contexts (L,S,R) at position w0[s] can make w0[s] privileged?
#
# Privilege means: f_{w0[s]}(L, S, R) != S
# The forced entries are the ones where (L,S,R) appears in the good cycle.
# But OTHER entries in the table can also create privilege.
#
# For the Lean proof, we need to work with ANY system that has the good cycle.
# So we can only use the forced entries.

# Actually wait — the Lean theorem takes `hconv : converges sys gc` as hypothesis.
# If the system converges and has this good cycle, then the forced entries must
# be as determined by the good cycle. But free entries (contexts not seen in
# the good cycle) can be anything.
#
# For the bad cycle, we need: at each step s, mover w0[s] is privileged at
# bad[s]. This means the context (L,S,R) at w0[s] in bad[s] must have
# f_{w0[s]}(L,S,R) != S. This could use a forced entry OR a free entry.
#
# But free entries are chosen by the adversary (the system). We're trying to
# show that NO system with this good cycle can converge. So we need a bad
# cycle that works for ALL possible free entries.
#
# The forced-entry approach only uses entries that are FORCED by the good cycle.
# If a bad config has context (L,S,R) at the mover that matches a forced entry,
# then the transition is determined regardless of free entries.

# So let me check: for the same-mover bad cycle found above (if any),
# does every step use a forced entry?
if fixed_points:
    c0 = fixed_points[0]
    print(f"\nChecking forced entries for bad cycle starting at {c0}:")
    cur = c0
    all_forced = True
    for s in range(ell):
        p = w0[s]
        L = cur[(p-1)%n]; S = cur[p]; R = cur[(p+1)%n]
        is_forced = (L, S, R) in mcx[p]
        if not is_forced:
            all_forced = False
            print(f"  Step {s}: P{p} ctx=({L},{S},{R}) NOT FORCED")
        cur = step_trans[s][cur]
    print(f"All forced: {all_forced}")

# ============================================================
# PART 3: Try smaller n first (n=7) for insight
# ============================================================
print(f"\n{'='*72}")
print("PART 3: Analysis at n=7")
print("="*72)

n7 = 7
ms7 = [2,3,3,2,3,3,2]
target_fc7 = {p: ms7[p] for p in range(n7)}
words7 = enumerate_exact_fc_words(ms7, n7, target_fc7)
seen7 = set()
unique7 = []
for w in words7:
    canon = canonicalize_word(w)
    if canon not in seen7:
        seen7.add(canon)
        unique7.append(w)
valid7 = []
for w in unique7:
    cycle = build_cycle(ms7, n7, w)
    if cycle is not None:
        valid7.append((w, cycle))
sweeps7 = [(w, c, compute_displacement(w, n7)) for w, c in valid7 if abs(compute_displacement(w, n7)) == 2*n7]
print(f"Sweeps at n=7: {len(sweeps7)}")

if sweeps7:
    w7, _, d7 = sweeps7[0]
    ell7 = len(w7)
    combo7 = tuple(enumerate_state_sequences(ms7[p], ms7[p])[0] for p in range(n7))
    gc7, fc7 = get_good_cycle_with_combo(ms7, n7, w7, combo7)
    good_set7 = set(gc7)

    mcx7 = defaultdict(dict)
    for s in range(ell7):
        p = w7[s]
        L = gc7[s][(p-1)%n7]; S = gc7[s][p]; R = gc7[s][(p+1)%n7]
        mcx7[p][(L, S, R)] = gc7[(s+1)%ell7][p]

    print(f"Mover word: {list(w7)}")
    print(f"Cycle length: {ell7}")
    print(f"Forced entries:")
    for p in sorted(mcx7.keys()):
        print(f"  P{p} (m={ms7[p]}): {dict(mcx7[p])}")

    # Compose 18 step functions
    all_cfgs7 = list(itertools.product(*(range(m) for m in ms7)))
    non_good7 = [c for c in all_cfgs7 if c not in good_set7]
    print(f"Non-good configs: {len(non_good7)} / {len(all_cfgs7)}")

    step_trans7 = {}
    for s in range(ell7):
        p = w7[s]
        trans = {}
        for c in non_good7:
            L = c[(p-1)%n7]; S = c[p]; R = c[(p+1)%n7]
            if (L, S, R) in mcx7[p]:
                Sp = mcx7[p][(L, S, R)]
                if Sp != S:
                    nc = list(c); nc[p] = Sp; nc = tuple(nc)
                    if nc not in good_set7:
                        trans[c] = nc
        step_trans7[s] = trans

    # Compose
    current7 = {}
    for c in non_good7:
        current7[c] = c
    for s in range(ell7):
        new_current = {}
        for start_c, cur_c in current7.items():
            if cur_c in step_trans7[s]:
                new_current[start_c] = step_trans7[s][cur_c]
        current7 = new_current

    print(f"Configs surviving all {ell7} steps: {len(current7)}")
    fixed7 = [c for c, result in current7.items() if result == c]
    print(f"Fixed points: {len(fixed7)}")

    if fixed7:
        # Analyze offset patterns
        const_count = 0
        nonconst_count = 0
        const_offsets = set()
        for c0 in fixed7:
            bad = [c0]
            cur = c0
            for s in range(ell7):
                cur = step_trans7[s][cur]
                if s < ell7 - 1:
                    bad.append(cur)
            ds = [tuple((bad[s][p] - gc7[s][p]) % ms7[p] for p in range(n7)) for s in range(ell7)]
            if len(set(ds)) == 1:
                const_count += 1
                const_offsets.add(ds[0])
            else:
                nonconst_count += 1

        print(f"Constant-offset cycles: {const_count}")
        print(f"Non-constant cycles: {nonconst_count}")
        if const_offsets:
            print(f"Constant offsets found:")
            for d in sorted(const_offsets):
                print(f"  d = {d}")
