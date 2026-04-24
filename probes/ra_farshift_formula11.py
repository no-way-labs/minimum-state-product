#!/usr/bin/env python3
"""
RA Part 11: Verify at n=11 to find general formula.

At n=9, ms=[2,3,3,2,3,3,2,3,3]:
  CCW: q=P8 (ternary, adjacent to start in sweep dir), shift=combo[8][1]
  CW: q=P6 (binary, at distance 3 from start in opposite dir), shift=1

The question: what is q for general n with ms = [2,3,3]*(n/3)?
Binary positions: 0, 3, 6, 9, ...
Ternary positions: 1, 2, 4, 5, 7, 8, ...

At n=11: ms=[2,3,3,2,3,3,2,3,3,2,3] or [2,3,3,2,3,3,2,3,3,3,3]?
Wait, ms pattern is [2,3,3] repeating. For n=9: [2,3,3,2,3,3,2,3,3].
For n=11: we need 3 binary + 8 ternary, product < 4*3^9 = 78732.
ms could be [2,3,3,2,3,3,2,3,3,3,3] = 2^3 * 3^8 = 52488.

Actually the problem says "non-consecutive binary, ≥3 binary, sub-threshold".
The concrete ms pattern doesn't matter for the Lean — it works for any valid ms.
But for testing, let me use [2,3,3,2,3,3,2,3,3,3,3] at n=11.

Actually, n=11 with this ms would be very slow to enumerate. Let me instead
focus on understanding WHY the specific q values work at n=9.

The real question for Lean: what is the PROOF that the shift works?
We need to show that every context in the bad cycle matches a forced entry.

Let me analyze the SPECIFIC contexts at each step of the bad cycle
and understand WHY they all match forced entries.
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
combo0 = tuple(enumerate_state_sequences(ms[p], ms[p])[0] for p in range(n))

# ============================================================
# DETAILED CONTEXT ANALYSIS: Why does shifting P8 work for CCW?
# ============================================================
print("="*72)
print("WHY SHIFTING P8 WORKS (CCW sweep)")
print("="*72)

word = sweeps[0][0]
gc, _ = get_good_cycle_with_combo(ms, n, word, combo0)
gs = set(gc)
mx = defaultdict(dict)
for s in range(len(word)):
    p = word[s]
    L = gc[s][(p-1)%n]; S = gc[s][p]; R = gc[s][(p+1)%n]
    mx[p][(L, S, R)] = gc[(s+1)%len(word)][p]

print(f"\nGood cycle (combo0):")
for s in range(len(word)):
    p = word[s]
    c = gc[s]
    L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
    print(f"  [{s:2d}] fire P{p}: {c}  ctx=({L},{S},{R})")

result = test_shift_full(ms, n, gc, gs, mx, 8, 1)
bad_c, bad_m = result
print(f"\nBad cycle (P8 shifted by 1):")
for s in range(len(bad_c)):
    p = bad_m[s]
    c = bad_c[s]
    L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
    # Find which good step has this context at this proc
    match = None
    for gs_idx in range(len(word)):
        if word[gs_idx] == p:
            gL = gc[gs_idx][(p-1)%n]; gS = gc[gs_idx][p]; gR = gc[gs_idx][(p+1)%n]
            if (gL, gS, gR) == (L, S, R):
                match = gs_idx
                break
    print(f"  [{s:2d}] fire P{p}: {c}  ctx=({L},{S},{R})  matches good step {match}")

# ============================================================
# KEY OBSERVATION: At EVERY step of the bad cycle, the mover's
# 3-neighborhood is IDENTICAL to some step of the good cycle.
# This means the forced entry applies.
#
# WHY? Because shifting P8 only affects positions P7, P8, P0
# (the 3-neighborhood of P8). At all other positions, the shift
# is invisible. When the mover is far from P8 (dist >= 2),
# the context is unchanged.
#
# When the mover IS P7, P8, or P0 (or their neighbors):
# the context involves P8's shifted value. But these contexts
# STILL match a forced entry because... let me check.
# ============================================================

print(f"\n{'='*72}")
print("WHICH STEPS INVOLVE P8 IN CONTEXT?")
print("="*72)

# A context involves P8 when the mover is P7, P8, or P0
# (since context = (mover-1, mover, mover+1))
for s in range(len(bad_c)):
    p = bad_m[s]
    ctx_procs = [(p-1)%n, p, (p+1)%n]
    involves_8 = 8 in ctx_procs

    c = bad_c[s]
    gc_s = gc[s]
    diff = tuple((c[i] - gc_s[i]) % ms[i] for i in range(n))

    if involves_8:
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        gL = gc_s[(p-1)%n]; gS = gc_s[p]; gR = gc_s[(p+1)%n]
        print(f"  [{s:2d}] P{p} involves P8: bad_ctx=({L},{S},{R}) good_ctx=({gL},{gS},{gR}) diff_at_8={diff[8]}")

# ============================================================
# Now let me understand: the bad cycle has DIFFERENT movers.
# When it fires P7 at step 0, the context is (P6,P7,P8) = (0,0,1).
# The good cycle fires P7 at step 2 with context (P6,P7,P8) = (0,0,1).
# IDENTICAL! Because at step 0 of the bad cycle, P6 and P7 are still 0
# (same as good), and P8 = 1 (shifted). At good step 2, P8 = 1 too
# (it was incremented at good step 1).
#
# So the bad cycle "catches up" to the good cycle's contexts by starting
# with P8 already at 1, and firing in a different order that maintains
# the same local contexts.
# ============================================================

# ============================================================
# FOR LEAN: The simplest formalization
# ============================================================
print(f"\n{'='*72}")
print("LEAN FORMALIZATION APPROACH")
print("="*72)

print("""
APPROACH: ShadowTrap from forced entries.

1. DEFINITION: For a good cycle gc with mover word w and forced entries
   mcx[p][(L,S,R)] = S', define the forced-entry graph G on non-good configs:
   - Vertices: configs c not in gc.configs
   - Edges: c -> c' if exists p such that (c[p-1], c[p], c[p+1]) in mcx[p]
     and c' = c with c'[p] = mcx[p][(c[p-1], c[p], c[p+1])]
     and c' not in gc.configs

2. CLAIM: G contains a cycle (hence a ShadowTrap).

3. PROOF:
   a. Start from c0 = (0,...,0) with position q shifted by d, where:
      - For CCW sweep: q = (start-1)%n, d = combo[q][1]
      - For CW sweep: q = last binary proc in CCW direction, d = 1
   b. c0 is not in gc.configs (gc starts at all-zeros, c0 differs at q)
   c. Follow forced transitions: at each step, there exists at least one
      proc p whose context (L,S,R) matches a forced entry
   d. After CL steps, return to c0 (each proc was incremented m_p times)
   e. All intermediate configs are non-good

4. For Lean: define BadCycleData where
   - cfg[k] = the k-th config in the forced-entry orbit from c0
   - mover[k] = the proc fired at step k
   - All 4 properties follow from the forced-entry matching

The HARD part for Lean: showing that at each step, there exists a proc
with a forced-entry context. This requires showing that the shift at q
propagates correctly through the sweep.

SIMPLER ALTERNATIVE: Use the fact that the forced-entry graph on non-good
configs has in-degree >= 1 for every config in the trap. Since the trap
is finite and nonempty, it must contain a cycle. The trap is nonempty
because c0 is in it.

But even this requires proving c0 is in the trap, which requires the same
context-matching argument.

THE SIMPLEST LEAN PROOF: Use computability.
- For each n from 9 to some bound K, verify computationally
- For n > K, use the analytical argument (context matching for far procs)
- The context matching for n > K follows because for large n, there are
  many procs far from any 3-neighborhood, so shifting any of them works.
""")

# ============================================================
# VERIFY: forced-entry cycle exists for ALL sweeps x ALL combos
# (using the correct q and shift)
# ============================================================
print(f"\n{'='*72}")
print("FINAL VERIFICATION: Correct q formula")
print("="*72)

all_combos = list(itertools.product(*[enumerate_state_sequences(ms[p], ms[p]) for p in range(n)]))
total = 0
pass_count = 0

for wi, (word, _, disp) in enumerate(sweeps):
    diff01 = (word[1] - word[0]) % n
    if diff01 == n-1:  # CCW
        q = (word[0] - 1) % n  # = P8 for start=P0
    else:  # CW
        # Last binary proc in opposite direction
        start = word[0]
        binary_pos = [p for p in range(n) if ms[p] == 2]
        # Find the binary proc at distance 3 in CCW direction
        # For start=P0: go CCW: P8, P7, P6. P6 is binary.
        q = None
        for step in range(1, n):
            candidate = (start - step) % n
            if ms[candidate] == 2:
                q = candidate
                break

    for ci, combo in enumerate(all_combos):
        gc, _ = get_good_cycle_with_combo(ms, n, word, combo)
        gs = set(gc)
        mx_local = defaultdict(dict)
        for s in range(len(word)):
            p = word[s]
            L = gc[s][(p-1)%n]; S = gc[s][p]; R = gc[s][(p+1)%n]
            mx_local[p][(L, S, R)] = gc[(s+1)%len(word)][p]

        shift = combo[q][1]
        result = test_shift_full(ms, n, gc, gs, mx_local, q, shift)
        total += 1
        if result:
            pass_count += 1
        else:
            print(f"  FAIL: sweep {wi} combo {ci} q=P{q} shift={shift}")

print(f"\nResult: {pass_count}/{total}")

# ============================================================
# Summary
# ============================================================
print(f"\n{'='*72}")
print("SUMMARY")
print("="*72)
print(f"""
At n=9, ms=[2,3,3,2,3,3,2,3,3]:

THE FORMULA:
  For a stuttered sweep good cycle starting at proc p0:

  If sweep is CCW (word[1] = (p0-1)%n):
    q = (p0 - 1) % n  (ternary proc in sweep direction)
    shift = combo[q][1]  (the value q transitions to after first firing)

  If sweep is CW (word[1] = (p0+1)%n):
    q = first binary proc encountered going CCW from p0
    shift = combo[q][1] = 1  (binary procs always have seq (0,1,0))

  Bad cycle: start from gc[0] with position q shifted by `shift`.
  Follow forced transitions (always choosing first available).
  Returns to start after CL = sum(ms) steps.
  All 4 BadCycleData properties hold.

VERIFICATION: {pass_count}/{total} (all cases at n=9)

For Lean: the bad cycle is defined as:
  bad_cfg[0] = gc.configs[0] with position q shifted by shift
  bad_cfg[k+1] = move(bad_cfg[k], bad_mover[k])
  where bad_mover[k] = first proc p such that (L,S,R) at p in bad_cfg[k]
    matches a forced entry and S' ≠ S
""")
