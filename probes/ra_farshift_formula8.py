#!/usr/bin/env python3
"""
RA Part 8: Understand combo-dependent shift amount.

At n=9 CCW sweeps: P8 shift=1 works for 50% of combos, shift=2 for other 50%.
Question: what determines which shift works?

Also: the REAL proof approach might not be single-proc shift.
The Lean needs: existence of a bad cycle for ANY system with this good cycle.
The forced-entry graph ALWAYS has a cycle (512/512).
So the proof should show the forced-entry graph always has a cycle.

But for Lean, we need an EXPLICIT formula. Can we characterize which shift
works based on the combo?

ALTERNATIVE: Instead of requiring ONE shift that works universally,
show that for EACH system, SOME shift works. The Lean can use a
case split: if shift=1 works, use it; otherwise shift=2 works.
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

def test_shift(ms, n, gc_configs, good_set, mcx, q, shift_amount=1):
    ell = len(gc_configs)
    c0 = list(gc_configs[0])
    c0[q] = (c0[q] + shift_amount) % ms[q]
    c0 = tuple(c0)
    if c0 in good_set:
        return None
    path = [c0]
    movers = []
    cur = c0
    for step in range(ell + 5):
        available = []
        for p in range(n):
            L = cur[(p-1)%n]; S = cur[p]; R = cur[(p+1)%n]
            if (L, S, R) in mcx[p]:
                Sp = mcx[p][(L, S, R)]
                if Sp != S:
                    nc = list(cur); nc[p] = Sp; nc = tuple(nc)
                    if nc not in good_set:
                        available.append((nc, p))
        if not available:
            return None
        nxt, p = available[0]
        movers.append(p)
        if nxt == c0:
            if len(path) == ell:
                return (path, movers)
            return None
        if nxt in set(path):
            return None
        path.append(nxt)
        cur = nxt
    return None

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

all_combos = list(itertools.product(*[enumerate_state_sequences(ms[p], ms[p]) for p in range(n)]))

# ============================================================
# For CCW sweeps: understand shift=1 vs shift=2 at P8
# ============================================================
print("="*72)
print("CCW sweep 0: P8 shift=1 vs shift=2 by combo")
print("="*72)

word = sweeps[0][0]
print(f"Word: {list(word)}")

# The state sequences for ternary procs
ternary_seqs = enumerate_state_sequences(3, 3)
print(f"Ternary state sequences: {ternary_seqs}")
# For m=3, k=3: sequences starting and ending at 0, length 4, no consecutive repeats
# Should be: (0,1,2,0) and (0,2,1,0)

binary_seqs = enumerate_state_sequences(2, 2)
print(f"Binary state sequences: {binary_seqs}")
# For m=2, k=2: (0,1,0)

for ci, combo in enumerate(all_combos):
    gc, _ = get_good_cycle_with_combo(ms, n, word, combo)
    gs = set(gc)
    mx = defaultdict(dict)
    for s in range(len(word)):
        p = word[s]
        L = gc[s][(p-1)%n]; S = gc[s][p]; R = gc[s][(p+1)%n]
        mx[p][(L, S, R)] = gc[(s+1)%len(word)][p]

    r1 = test_shift(ms, n, gc, gs, mx, 8, 1)
    r2 = test_shift(ms, n, gc, gs, mx, 8, 2)
    works1 = "Y" if r1 else "N"
    works2 = "Y" if r2 else "N"

    # What's the state sequence at P8?
    seq8 = combo[8]
    seq7 = combo[7]

    if ci < 20 or (works1 == "N" and works2 == "N"):
        print(f"  Combo {ci:2d}: seq8={seq8} seq7={seq7} shift1={works1} shift2={works2}")

# Check: does it depend ONLY on seq8?
print(f"\nGrouped by seq8:")
for seq8 in ternary_seqs:
    s1_count = 0
    s2_count = 0
    total = 0
    for ci, combo in enumerate(all_combos):
        if combo[8] != seq8:
            continue
        total += 1
        gc, _ = get_good_cycle_with_combo(ms, n, word, combo)
        gs = set(gc)
        mx = defaultdict(dict)
        for s in range(len(word)):
            p = word[s]
            L = gc[s][(p-1)%n]; S = gc[s][p]; R = gc[s][(p+1)%n]
            mx[p][(L, S, R)] = gc[(s+1)%len(word)][p]
        if test_shift(ms, n, gc, gs, mx, 8, 1): s1_count += 1
        if test_shift(ms, n, gc, gs, mx, 8, 2): s2_count += 1
    print(f"  seq8={seq8}: shift1={s1_count}/{total} shift2={s2_count}/{total}")

# ============================================================
# KEY INSIGHT: At LEAST ONE of shift=1, shift=2 always works
# ============================================================
print(f"\n{'='*72}")
print("CRITICAL: Does shift1 OR shift2 always work at P8?")
print("="*72)

both_fail = 0
for wi, (word, _, disp) in enumerate(sweeps):
    for ci, combo in enumerate(all_combos):
        gc, _ = get_good_cycle_with_combo(ms, n, word, combo)
        gs = set(gc)
        mx = defaultdict(dict)
        for s in range(len(word)):
            p = word[s]
            L = gc[s][(p-1)%n]; S = gc[s][p]; R = gc[s][(p+1)%n]
            mx[p][(L, S, R)] = gc[(s+1)%len(word)][p]

        # For CCW sweeps, try P8; for CW sweeps, try P6
        if disp < 0:
            # CCW: try P8
            r1 = test_shift(ms, n, gc, gs, mx, 8, 1)
            r2 = test_shift(ms, n, gc, gs, mx, 8, 2)
            if not r1 and not r2:
                both_fail += 1
                print(f"  BOTH FAIL: sweep {wi}, combo {ci}")
        else:
            # CW: P6 shift=1 is universal (from previous part)
            r = test_shift(ms, n, gc, gs, mx, 6, 1)
            if not r:
                both_fail += 1
                print(f"  P6 FAIL: sweep {wi}, combo {ci}")

print(f"\nBoth-fail count: {both_fail}")

# ============================================================
# For the Lean formalization, we need:
# 1. A rule for which proc q to shift (depends on sweep direction)
# 2. A rule for which shift amount (1 or 2 for ternary)
# 3. Proof that the shift produces a valid bad cycle
#
# The shift=1 vs shift=2 depends on the combo (state sequence).
# Specifically: the initial config gc[0] is (0,0,...,0).
# Shifting P8 by 1 gives c0[8]=1, shifting by 2 gives c0[8]=2.
# Which works depends on whether c0 is in the good cycle or not,
# and whether the orbit closes.
#
# Actually: gc[0] = (0,...,0), so shifting P8 by 1 gives (0,...,0,1)
# and shifting by 2 gives (0,...,0,2). These are always non-good
# (since good starts at all-zeros and first change is at P0, not P8).
# So the overlap check passes. The question is orbit closure.
#
# For Lean: we can define shift_amount = if some_condition then 1 else 2.
# Or: we can take a different approach entirely.
# ============================================================

# ============================================================
# ALTERNATIVE APPROACH: Use ShadowTrap instead of BadCycleData
# ============================================================
print(f"\n{'='*72}")
print("ALTERNATIVE: ShadowTrap (set-based, no ordering needed)")
print("="*72)

# A ShadowTrap is a nonempty set S of non-good configs such that
# for every c in S, there exists a forced privileged proc p and
# the transition leads to some c' in S.
#
# This is MUCH easier to prove than BadCycleData because we don't
# need an explicit ordering, movers, distinctness, or cycle structure.
#
# The forced-entry graph always has a cycle (512/512 verified).
# The trap is the set of configs reachable from any cycle in the graph.

# Check: does the Lean file actually use BadCycleData or ShadowTrap?
# From reading: it uses BadCycleData with cfg, mover, disjoint, priv, step, distinct.
# But ShadowTrap would be easier...

# Let me verify: shifting P8 by 1 OR 2 produces a cycle that is ALWAYS
# a subset of the forced-entry graph's trap.

# Actually, the simplest approach for Lean might be:
# 1. Pick q = ternary proc adjacent to start and away from sweep direction
# 2. shift_amount = 1 (try first)
# 3. If the initial config (0,...,0) + e_q is in good set, use shift=2
#    (But it never is, since good starts at all-zeros)
# 4. The orbit ALWAYS closes in CL steps
# 5. Proof: the forced entries create a permutation on the shifted configs

# Wait, let me check: is the orbit closure PROVABLE analytically?
# The forced entries are incrementing: f_p(L,S,R) = (S+1) mod m_p.
# If we shift q by d, the orbit follows the same incrementing pattern.
# After CL = sum(ms) steps, each proc has been incremented m_p times,
# returning to its original value. So the orbit MUST close in CL steps!

# The question is: does the orbit stay within non-good configs and use
# only forced entry contexts?

print(f"\nOrbit closure analysis:")
print(f"CL = {sum(ms)} = sum(ms)")
print(f"After CL incrementing steps, each proc p is incremented m_p times")
print(f"So (S + m_p) mod m_p = S for all p -> orbit closes in CL steps")
print(f"This is INDEPENDENT of which contexts are forced!")

# But the issue is: at each step, the mover must be PRIVILEGED at the
# shifted config, AND the context must match a forced entry.
# The orbit follows WHATEVER forced transitions are available, not
# the good cycle's mover sequence.

# Actually, I realize the issue: the bad cycle doesn't follow the SAME
# mover word as the good cycle. It follows its OWN mover sequence,
# determined by which procs are privileged at each step.

# For the orbit to close: we need that after following forced transitions
# for CL steps, we return to the start. This is NOT guaranteed just because
# each proc is incremented m_p times — the mover SEQUENCE might differ.

# Let me check: in the verified bad cycles, does each proc fire exactly m_p times?
word = sweeps[0][0]
gc, _ = get_good_cycle_with_combo(ms, n, word, all_combos[0])
gs = set(gc)
mx = defaultdict(dict)
for s in range(len(word)):
    p = word[s]
    L = gc[s][(p-1)%n]; S = gc[s][p]; R = gc[s][(p+1)%n]
    mx[p][(L, S, R)] = gc[(s+1)%len(word)][p]

result = test_shift(ms, n, gc, gs, mx, 8, 1)
if result:
    bad_configs, bad_movers = result
    fc_bad = [0]*n
    for p in bad_movers:
        fc_bad[p] += 1
    print(f"\nBad cycle fire counts: {fc_bad}")
    print(f"ms:                    {ms}")
    print(f"Match: {all(fc_bad[p] == ms[p] for p in range(n))}")

    # Is the bad mover word a valid ring walk?
    ring_ok = True
    for s in range(len(bad_movers)):
        p = bad_movers[s]
        q = bad_movers[(s+1) % len(bad_movers)]
        if abs(p - q) % n not in (1, n-1):
            ring_ok = False
            break
    print(f"Bad mover word is ring walk: {ring_ok}")

    # Is the bad mover word a sweep?
    bad_disp = compute_displacement(bad_movers, n)
    print(f"Bad displacement: {bad_disp}")
    print(f"Good displacement: {compute_displacement(list(word), n)}")

# ============================================================
# THE SIMPLEST LEAN APPROACH
# ============================================================
print(f"\n{'='*72}")
print("SIMPLEST LEAN APPROACH")
print("="*72)

# Option A: BadCycleData with explicit bad cycle
#   - Need to specify cfg[k] for each k
#   - Need to specify mover[k] for each k
#   - The bad cycle's mover word is NOT the same as good cycle
#   - Would need to compute the bad mover word from the good cycle + shift
#   - Complex for Lean

# Option B: ShadowTrap (set-based)
#   - Just need a nonempty set S with forced out-edges staying in S
#   - S = trap from forced-entry graph
#   - Easier to state but hard to define constructively in Lean

# Option C: Show the forced-entry graph has a cycle of length CL
#   - The graph has in-degree 1 and out-degree >= 1 at every config
#     that has a forced entry. Wait, is this true?
#   - If each config has at least one forced out-edge within the trap,
#     and the trap is finite, then there's a cycle. But Lean needs a constructive proof.

# The REAL simplest approach: use decidability.
# For n=9 ms=[2,3,3,2,3,3,2,3,3], there are only 5832 configs.
# The forced-entry graph is finite and computable.
# Lean can just compute the trap and verify it's nonempty.

# But this is n-specific. The theorem should work for general n >= 9.

# For general n: the key insight is that the forced entries are INCREMENTING.
# Every proc's forced entry is f_p(L,S,R) = (S+1) mod m_p.
# The forced entry contexts are exactly those that appear in the good cycle.
# At a shifted config, the same contexts appear (for far procs, the shift
# doesn't affect the 3-neighborhood of the mover).

# WAIT. Let me reconsider the far-proc argument.
# For a sweep, the mover visits every proc. But at any given step,
# the mover is at ONE position, and the context involves only 3 positions.
# The shift at proc q affects the context ONLY at steps where q is
# in {mover-1, mover, mover+1}.
#
# For a proc q that is TERNARY and ADJACENT to the start position:
# q appears in the mover's context only when the mover is at {q-1, q, q+1}.
# At all other steps, q's value doesn't affect the context.
#
# At the steps where q IS in the context: the shifted value at q changes
# the context. The NEW context must ALSO be a forced entry. Is it?

print(f"\nContext analysis for shifted P8:")
print(f"P8 is ternary (m=3). Shifting P8 by 1.")
print(f"P8 appears in context of movers at P7, P8, P0.")
print()

# For the good cycle, extract ALL forced contexts
print("Forced entries (good cycle):")
for p in sorted(mx.keys()):
    print(f"  P{p}: {dict(mx[p])}")

# For the shifted bad cycle, which contexts are used?
print(f"\nBad cycle contexts:")
for s in range(len(bad_configs)):
    p = bad_movers[s]
    c = bad_configs[s]
    L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
    # Check which good-cycle step has this context
    match_steps = []
    for gs in range(len(word)):
        gp = word[gs]
        if gp == p:
            gL = gc[gs][(p-1)%n]; gS = gc[gs][p]; gR = gc[gs][(p+1)%n]
            if (gL, gS, gR) == (L, S, R):
                match_steps.append(gs)
    print(f"  [{s:2d}] P{p} ctx=({L},{S},{R}) matches good steps: {match_steps}")
