#!/usr/bin/env python3
"""
RA Part 10: Final formula — correct q selection.

Findings so far:
- CCW sweeps (0,8,7,...): q=P8 (the AHEAD proc), shift=combo[8][1] -> 64/64
- CW sweeps (0,1,2,...): q=P6 (binary), shift=1 -> universal

The pattern: q is the ternary proc AHEAD of the start in sweep direction.
For CCW: ahead = (start - 1) % n = P8 (ternary at n=9)
For CW: ahead = (start + 1) % n = P1 (ternary at n=9)
But P1 didn't work! P6 did. So that's wrong.

Wait: P6 is binary (m=2). combo[6][1] = 1 always. So shift=combo[6][1]=1.
And P6 is at distance 3 from start P0.

Let me look at this from a DIFFERENT angle. In Part 6:
- CW sweeps: P6 shift=1 universal (32 * 8 = 256 times)
- CCW sweeps: P8 shift=1 for 128, P8 shift=2 for 128

P8 and P6 are the "farthest" procs from the mover at certain key steps.
P6 is the MIDDLE binary proc (positions 0, 3, 6 — P6 is at index 6).
P8 is the last ternary proc.

Actually: the sweep at n=9 covers all 9 procs. The word is a stuttered
sweep where binary procs stutter. The last proc fired before returning to
start determines the "tail" of the sweep.

Let me just enumerate which q works for EACH sweep more carefully,
and look for the pattern.
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

def test_shift_full(ms, n, gc_configs, good_set, mcx, q, shift_amount):
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
                disjoint = all(c not in good_set for c in path)
                distinct = len(set(path)) == ell
                step_ok = True
                for s in range(ell):
                    pp = movers[s]
                    c = path[s]
                    L = c[(pp-1)%n]; S = c[pp]; R = c[(pp+1)%n]
                    if (L, S, R) not in mcx[pp]:
                        step_ok = False; break
                    Sp = mcx[pp][(L, S, R)]
                    nc = list(c); nc[pp] = Sp
                    expected = path[(s+1)%ell]
                    if tuple(nc) != expected:
                        step_ok = False; break
                if disjoint and distinct and step_ok:
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

print(f"n={n}, ms={ms}")
print(f"Sweeps: {len(sweeps)}, Combos: {len(all_combos)}")

# For each sweep, for each q, test combo[q][1] across all combos
print(f"\n{'='*72}")
print("For each sweep, which q with shift=combo[q][1] is universal?")
print("="*72)

for wi, (word, _, disp) in enumerate(sweeps):
    diff01 = (word[1] - word[0]) % n
    direction = "CCW" if diff01 == n-1 else "CW"
    print(f"\n  Sweep {wi}: start=P{word[0]}, dir={direction}, word[1]=P{word[1]}, disp={disp:+d}")

    for q in range(n):
        pass_q = 0
        for ci, combo in enumerate(all_combos):
            gc, _ = get_good_cycle_with_combo(ms, n, word, combo)
            gs = set(gc)
            mx = defaultdict(dict)
            for s in range(len(word)):
                p = word[s]
                L = gc[s][(p-1)%n]; S = gc[s][p]; R = gc[s][(p+1)%n]
                mx[p][(L, S, R)] = gc[(s+1)%len(word)][p]
            sh = combo[q][1]
            r = test_shift_full(ms, n, gc, gs, mx, q, sh)
            if r: pass_q += 1

        if pass_q > 0:
            print(f"    q=P{q} (m={ms[q]}): combo[q][1] works for {pass_q}/{len(all_combos)}")

# ============================================================
# Now I see that ONLY P8 works for CCW and ONLY P6 works for CW.
# P8 works with combo[8][1], P6 with combo[6][1]=1 (binary, always 1).
#
# Pattern: the shift proc is ALWAYS the proc that fires LAST in the
# first full sweep before the first stutter.
#
# Let me check: for CCW sweeps, the first leg goes:
# P0, P8, P7, P6, P5, P4, P3, P2, P1 (9 procs, one full sweep)
# The LAST proc before returning is P1.
# The FIRST proc after start is P8.
# P8 works.
#
# For CW sweeps: P0, P1, P2, P1, P2, P3, ...
# The first leg has a stutter at P1-P2. The last proc in the first
# full sweep leg is P8. But P6 works, not P8.
#
# Hmm. Let me look at the relationship differently.
# ============================================================

# The key: ms = [2,3,3,2,3,3,2,3,3]
# Binary: P0, P3, P6. Ternary: P1, P2, P4, P5, P7, P8.
# Non-consecutive binary (gap of 3 between each).
#
# The stuttered sweep visits all procs. The binary procs fire twice,
# ternary fire three times. The sweep has a main direction plus stutters
# at specific turnaround points.
#
# For the shift to work: q must be "far enough" from the initial mover's
# neighborhood that the shift doesn't affect the first transition.
#
# For CCW sweep starting at P0 going to P8: the initial context is
# P0's context at config (0,...,0), which involves (P8, P0, P1).
# Shifting P8 changes P8's value, which IS in P0's initial context!
# So the shift DOES affect the first transition. How does it still work?
#
# Because: the FORCED entry at P0 for context (0,0,0) is f_0(0,0,0)=1.
# After shifting P8 by d, the initial config is (0,...,0,d) and P0's
# context is (d,0,0). But wait: (d,0,0) might NOT be a forced entry!
# It's only forced if it appeared in the good cycle.
# The forced entry at P0 is {(0,0,0)->1, (1,1,1)->0}.
# So (d,0,0) is forced only if d=0 (which is the good cycle) or d=1 (no!).
# (1,0,0) is NOT a forced entry for P0!
#
# So when we shift P8 by 1, at step 0 P0 is NOT fired (its context
# (1,0,0) is not forced). Some OTHER proc fires instead.
# That's why the bad cycle has different movers!

# The bad cycle at step 0 fires P7 (ctx=(0,0,1)), which IS forced for P7.
# So shifting P8 makes P7 the first to fire, not P0.
# The wavefront starts from the SHIFT position and sweeps in the
# OPPOSITE direction!

print(f"\n{'='*72}")
print("INSIGHT: The bad cycle's wavefront starts at the shifted proc")
print("="*72)

word = sweeps[0][0]
combo = all_combos[0]
gc, _ = get_good_cycle_with_combo(ms, n, word, combo)
gs = set(gc)
mx = defaultdict(dict)
for s in range(len(word)):
    p = word[s]
    L = gc[s][(p-1)%n]; S = gc[s][p]; R = gc[s][(p+1)%n]
    mx[p][(L, S, R)] = gc[(s+1)%len(word)][p]

# Good cycle starts all-zeros, shifts P8 by 1
result = test_shift_full(ms, n, gc, gs, mx, 8, 1)
if result:
    bad_c, bad_m = result
    print(f"Good movers: {list(word)}")
    print(f"Bad movers:  {bad_m}")
    print()
    for s in range(len(bad_c)):
        c = bad_c[s]
        p = bad_m[s]
        print(f"  [{s:2d}] fire P{p}: {c}")

# ============================================================
# THE REAL FORMULA for Lean
# ============================================================
print(f"\n{'='*72}")
print("THE FORMULA")
print("="*72)

# For a stuttered sweep good cycle:
# 1. All procs start at state 0 (gc[0] = (0,...,0))
# 2. Each proc p fires m_p times with incrementing transitions: 0->1->...->0
# 3. The forced entries are: f_p(L,S,R) = (S+1) mod m_p for each (L,S,R)
#    that appears at mover steps in the good cycle
#
# Construction of bad cycle:
# a. Choose q = the ternary proc IN THE SWEEP DIRECTION from start
#    (for CCW: q = (start-1)%n = P8; for CW: q = (start+1)%n = P1)
#    Wait, P8 works for CCW, not P1. And earlier said for CW P6 works.
#    Let me re-examine...

# Actually, from Part 6 results at n=9:
# CCW sweeps (0-3): P8 shift=1 or 2 (128 each), P6 shift=1 (256 total for CW)
# CW sweeps (4-7): P6 shift=1 universal

# And Part 9 "Alternative q" for sweep 0 (CCW):
# Only P8 has any success (64/64 with combo[8][1])
# All other procs: 0/64

# For sweep 4 (CW), only P6 works.
# P6 is binary (m=2), combo[6][1] = 1.

# The pattern at n=9:
# CCW sweeps: q = P8 = (start - 1) % n, which is the proc in sweep direction
# CW sweeps: q = P6 = (start - 3) % n = last binary proc CCW of start

# Wait: for CW sweep starting at P0 going P0,P1,P2,...
# The "behind" direction is CCW. P8 is behind. But P6 works, not P8.
# P6 is at distance 3 CCW from P0 (0->8->7->6).
# P6 is the first binary proc encountered going CCW from P0.

# For CCW sweep starting at P0 going P0,P8,P7,...
# The "behind" direction is CW. P1 is behind. But P8 works, not P1.
# P8 = (P0-1)%9 is the first proc in sweep direction (CCW).

# Hmm, for CW: P6 = P0 - 3 mod 9. Why not P3 (the closer binary)?
# Binary positions: 0, 3, 6.
# P3 is at distance 3 CW from P0.
# P6 is at distance 3 CCW from P0.

# For CW sweep: sweep goes 0->1->2->3->...->8.
# P6 is the LAST binary proc before wrap-around.
# It's also the binary proc farthest from start in CCW direction.

# I think the pattern is:
# q = the proc such that shifting it by 1 produces the initial config
# that the bad wavefront starts from.
# For CCW sweep: the bad wavefront starts at q=P8 and sweeps CW from there.
# For CW sweep: the bad wavefront starts at some position near P6.

# But this is getting complicated. Let me just verify the SIMPLER claim:
# For CCW: q = word[1] (the second mover in good cycle = P8)
# For CW: need to identify

print(f"\nFor each sweep, the WORKING q:")
for wi, (word, _, disp) in enumerate(sweeps):
    diff01 = (word[1] - word[0]) % n
    direction = "CCW" if diff01 == n-1 else "CW"
    # word[1] is the second mover
    second_mover = word[1]
    # The last binary proc in opposite direction
    binary_pos = [p for p in range(n) if ms[p] == 2]

    # Test all procs
    best_q = None
    best_score = 0
    for q in range(n):
        score = 0
        for ci, combo in enumerate(all_combos):
            gc, _ = get_good_cycle_with_combo(ms, n, word, combo)
            gs = set(gc)
            mx = defaultdict(dict)
            for s in range(len(word)):
                p = word[s]
                L = gc[s][(p-1)%n]; S = gc[s][p]; R = gc[s][(p+1)%n]
                mx[p][(L, S, R)] = gc[(s+1)%len(word)][p]
            sh = combo[q][1]
            r = test_shift_full(ms, n, gc, gs, mx, q, sh)
            if r: score += 1
        if score > best_score:
            best_score = score
            best_q = q

    print(f"  Sweep {wi} ({direction}): best q=P{best_q} ({best_score}/{len(all_combos)})")
    print(f"    word[1]=P{word[1]}, last_word=P{word[-1]}")
    # What's the ternary proc immediately CCW from the last binary?
    # Binary: 0, 3, 6.
    # For CCW sweep ending at P1: last binary in CW direction from P1 is P3.
    # The ternary proc before P0 (in CCW direction) is P8.
    # word[-1] = P1 for CCW sweep 0.
    # The best q = P8 = the proc immediately before start in CCW direction.
