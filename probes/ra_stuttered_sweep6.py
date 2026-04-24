#!/usr/bin/env python3
"""
RA Part 6: Final clarification and proof-of-concept.

Key questions:
1. The forced trap EXISTS for all combos. But can we PROVE it exists
   without enumerating? What's the structural reason?
2. The sorry needs hconv. Can we get it threaded through?
3. Is there a simpler mechanism that doesn't need the full ShadowTrap?

Let me check: does the EXISTING shadow machinery (for WaterfallCycles)
somehow apply here? The stuttered sweep is NOT a WaterfallCycle
(CL != 2n), but maybe we can reduce to it.

Alternative: the non-consecutive binary + isolated means we have
a binary proc with gap >= 2. This gives an entry conflict or shadow
through a DIFFERENT mechanism than the waterfall shadow.

Let me check: is there actually an entry conflict hidden here that
we missed? The EC check in script 1 said "all_ec=False, no_ec_count=64/64"
meaning NO COMBO has EC. But that was for the incrementing-only check.
Let me verify with the full transition-independent check.
"""

import sys
import itertools
from collections import Counter, defaultdict

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


# ============================================================
# Check: does the CONVERGENCE argument work?
# ============================================================
print("=" * 72)
print("CONVERGENCE-BASED PROOF CHECK")
print("=" * 72)

print("""
The sorry is inside sweep_false which has signature:
  (hconv : converges sys gc) in the CALLING chain
  but NOT passed to the sorry's function.

Looking at the code at line 580-626:
  theorem sweep_false
    {sys : System} (gc : GoodCycle sys)
    (hn : sys.rs.n >= 9) (hconv : converges sys gc)  <-- hconv IS here!
    ...
    (hsweep : gc.isSweep) : False

So hconv IS available at the sorry point! The sorry is just missing
the proof that uses it.

The existing Lean infrastructure has:
  - ShadowTrap: a cycle of non-good configs with privileged-proc transitions
  - shadowTrap_not_converges: ShadowTrap -> not(converges)
  - hconv: converges sys gc

So the proof is: construct ShadowTrap, apply shadowTrap_not_converges,
contradict hconv. QED.

But constructing ShadowTrap requires proving:
  1. configs != []
  2. All configs not in good cycle
  3. Closed: each config has a privileged proc whose firing gives the next
  4. All configs distinct

For a general-n analytical proof, we need to show these properties hold
for a structurally-defined cycle. The forced-entry trap gives us this.
""")

# ============================================================
# KEY INSIGHT: The forced trap IS the existing shadow, just applied
# to a non-waterfall cycle. Let me check if the waterfall shadow
# construction can be adapted.
# ============================================================
print("=" * 72)
print("RELATIONSHIP TO WATERFALL SHADOW")
print("=" * 72)

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

w0, cyc0, d0 = sweeps[0]
ell = len(w0)

# The stuttered sweep word: [0,8,7,6,5,4,3,2,1, 0,8,7,8,7,6,5,4,5,4,3,2,1,2,1]
# It consists of:
# - A pure CCW sweep: 0,8,7,6,5,4,3,2,1 (9 steps)
# - Then 3 "stutter pairs": (7,8), (4,5), (1,2) each adding 2 extra steps
# Total: 9 + 9 + 3*2 = 24

# The pure sweep part (steps 0-8, 9) visits 10 configs.
# The stutter pairs visit 14 more configs.

# ALTERNATIVE APPROACH: The stuttered sweep has the SAME displacement
# as a waterfall (|disp|=2n=18). So it IS topologically a sweep.
# It's just not a "uniform" sweep (alternating direction).

# What if we decompose the stuttered sweep into a waterfall + perturbation?
# The waterfall part would be the 18 "core" steps (all CCW).
# The stutter part adds 6 extra steps (3 pairs of CW+CCW).

print(f"Stuttered sweep word: {list(w0)}")
print(f"Length: {ell}, displacement: {d0}")

dirs = []
for i in range(ell):
    diff = (w0[(i+1)%ell] - w0[i]) % n
    dirs.append('+' if diff == 1 else '-')

core_steps = [i for i in range(ell) if dirs[i] == '-']
stut_steps = [i for i in range(ell) if dirs[i] == '+']

print(f"Core CCW steps: {core_steps} ({len(core_steps)})")
print(f"Stutter CW steps: {stut_steps} ({len(stut_steps)})")

# The core steps form a sequence that visits processors in CCW order
# Core mover word (just CCW steps):
core_movers = [w0[i] for i in core_steps]
print(f"Core movers: {core_movers}")

# This IS a permutation of [0..8, 0..8] minus some... no, it's 21 steps.
# The core visits each proc enough times. Let me check fire counts.
core_fc = Counter(core_movers)
print(f"Core fire counts: {dict(core_fc)}")

# Core fire counts: binary procs fire 2, ternary fire 2 (not 3).
# Wait, 21 core steps but sum of fire counts should be 21.
# Binary: 2 fires each, ternary: need to check.
print(f"Sum core: {sum(core_fc.values())}")

# A waterfall cycle of length 2n=18 visits each proc exactly 2 times.
# Our 21 core steps visit each binary proc 2 times and each ternary proc
# either 2 or 3 times (since 3*3 binary fires + remaining from ternary).
# Total: 3*2 + 6*? = 21, so 6*? = 15, ?=2.5... not integer.
# So the "core" can't be cleanly separated.

# Let me think differently. The stuttered sweep is already proved to
# have a forced trap computationally. The question is how to prove it
# in Lean.

# ============================================================
# SIMPLEST PROOF: The existing Lean proof handles:
# - Waterfall cycles -> shadow trap (proved)
# - Non-sweep (wiggle, odd winding) -> entry conflict or shadow
# - Sweep + consecutive binary + isolated -> proved (consecutive_binary_isolated_false')
# The ONLY gap is: sweep + non-consecutive binary + isolated

# For this case, the key observation is:
# hconv + forced entries -> ShadowTrap -> contradiction
# ============================================================

print(f"\n{'='*72}")
print("CHECKING: Does the existing shadow construction apply?")
print(f"{'='*72}")

# The existing shadow construction in Lean is for WaterfallCycles.
# A WaterfallCycle requires:
#   - cycle length = 2n
#   - uniform direction (all steps same direction)
#   - "waterfall" structure

# Our stuttered sweep has CL=24 != 18, non-uniform direction.
# So the existing construction does NOT directly apply.

# But: the forced-entry trap we found computationally IS a valid ShadowTrap.
# We just need to construct it in Lean.

# The simplest Lean proof would be:
# 1. Use `hconv` to get well-foundedness of badStep
# 2. From the forced mover entries, show that non-good configs form cycles
# 3. This contradicts well-foundedness

# Actually, even simpler: we don't need to construct the full ShadowTrap.
# We just need to show that hconv is contradicted.

# Wait - let me re-read the sorry context more carefully.
# The sorry says: "binary flip companion -> two disjoint cycles -> not converges"
# This is a DIFFERENT proof strategy. Let me check if binary flip actually works.

# Binary flip: for a binary proc p with isolated firings, flip p's state
# (0->1, 1->0) to get a companion cycle. If the companion is disjoint from
# the original and also a valid good cycle, then convergence fails
# (two disjoint good cycles = bad daemon can alternate between them forever).

# But the memory says "binary flip was disproved". Let me verify.

print("\n--- Binary Flip Check ---")
# Take sweep #0, combo #0
combo = tuple(enumerate_state_sequences(ms[p], ms[p])[0] for p in range(n))
fc_num = [0]*ell
pc = [0]*n
for s in range(ell):
    fc_num[s] = pc[w0[s]]
    pc[w0[s]] += 1

cs = []
state = [0]*n
for s in range(ell):
    cs.append(tuple(state))
    p = w0[s]
    state[p] = combo[p][fc_num[s]+1]
good_set = set(cs)

# Binary procs: 0, 3, 6
# Flip P0's state in all good configs
for bp in [0, 3, 6]:
    flipped = set()
    for c in good_set:
        fc = list(c)
        fc[bp] = 1 - fc[bp]
        flipped.add(tuple(fc))

    overlap = flipped & good_set
    print(f"  Flip P{bp}: overlap with good = {len(overlap)}, "
          f"disjoint = {len(overlap) == 0}")

    # Check if flipped configs form a valid cycle
    # (i.e., single-privilege and closed)

# ============================================================
# The real question: what's the SIMPLEST Lean proof?
# ============================================================
print(f"\n{'='*72}")
print("SIMPLEST LEAN PROOF ANALYSIS")
print(f"{'='*72}")

print("""
OPTION 1: Thread hconv and use ShadowTrap
  - hconv is already in sweep_false's signature
  - Need to construct ShadowTrap for non-waterfall sweeps
  - Hard: requires general-n construction or computational proof

OPTION 2: Show the non-consecutive case reduces to waterfall
  - A stuttered sweep has |disp|=2n, so it's "like" a waterfall
  - Can we show that if it's not a waterfall, there's an EC?
  - This would avoid needing a new ShadowTrap construction

OPTION 3: Entry conflict via a different mechanism
  - The non-consecutive binary + sweep + isolated case might have
    entry conflict via the Universal Entry Conflict theorem
  - Let me check if UEC applies here

OPTION 4: Convergence contradiction without ShadowTrap
  - hconv gives Acc (badStep) for all configs
  - The forced mover entries create badStep transitions
  - If these transitions form a cycle, they contradict Acc
  - This doesn't need the full ShadowTrap structure!
  - Just need: exists a non-good config c with a badStep path back to c
  - This is WEAKER than ShadowTrap (no need for distinct/disjoint)

Let me check Option 4 more carefully.
""")

# Option 4: Just need a cycle in badStep, not a full ShadowTrap
# badStep is: c' is a badStep predecessor of c if:
#   - c is non-good
#   - c' is non-good
#   - exists privileged proc i at c' such that firing i gives c
# So badStep sys gc c c' means: c' -> c (c' fires to c)
# A cycle in badStep means: c0 -> c1 -> ... -> ck -> c0
# This means Acc(badStep)(c0) is false (infinite descent)
# Contradiction with hconv.

# The forced trap IS such a cycle! Each step:
#   config[step] fires mover[step] to get config[step+1]
#   All configs are non-good (verified)
#   All transitions use forced entries (mover is privileged)

# So Option 4 works and is STRICTLY SIMPLER than ShadowTrap!

# In fact, the Lean proof just needs:
# 1. Exhibit one non-good config c
# 2. Show c has a privileged proc whose firing gives c' (also non-good)
# 3. Show c' has a privileged proc whose firing gives c'' (also non-good)
# 4. ... until you get back to c
# 5. This gives an infinite descent, contradicting hconv

# Wait, that IS exactly ShadowTrap! The existing infrastructure already
# handles this via shadowTrap_not_converges.

# The question is just: can we construct the ShadowTrap in Lean?
# The forced entries make each step's privilege FOLLOW FROM the good cycle.
# We don't need to know the transition tables; we just need to know that
# at certain contexts, the proc fires (because the good cycle forces it).

# ============================================================
# KEY INSIGHT: The proof MUST use hconv somehow
# ============================================================

# Without hconv, we can't prove False. The system COULD have
# other transition table entries that prevent the trap.
# Wait — we showed the trap uses ONLY forced entries (0 free entries).
# So the trap exists regardless of the free entries!
# Does this mean we DON'T need hconv?

# Let me re-check: the forced entries are:
# - Mover: f_p(L,S,R) = S' != S (good cycle forces this)
# - Nonmover: f_p(L,S,R) = S (good cycle forces this)
# The trap uses mover entries at non-good configs.
# The mover entry f_p(L,S,R) = S' != S is FORCED by the good cycle.
# So at a non-good config where proc p sees (L,S,R), p IS privileged
# (because the forced entry makes f_p(L,S,R) != S).
# And firing p at that config changes p's state to S'.
# This gives a transition among non-good configs.
# If these transitions form a cycle, it's a ShadowTrap.

# So: the ShadowTrap exists by construction, using ONLY forced entries.
# We don't need hconv to show it exists.
# We need hconv to derive the CONTRADICTION (ShadowTrap -> not converges).

# So the proof is:
# 1. Construct ShadowTrap from forced entries (structural, no hconv needed)
# 2. Apply shadowTrap_not_converges to get not(converges)
# 3. Contradiction with hconv

# This is exactly the existing pattern used for waterfall shadows!

print("CONCLUSION: The proof follows the SAME pattern as the waterfall shadow:")
print("1. Construct ShadowTrap from the good cycle's forced entries")
print("2. Apply shadowTrap_not_converges -> not(converges)")
print("3. Contradiction with hconv")
print()
print("The only new work is step 1: constructing the ShadowTrap for")
print("stuttered sweeps. This requires showing that the forced mover")
print("entries create a cycle among non-good configs.")
print()
print("The SIMPLEST approach for Lean: prove it for the specific")
print("pattern ms = [2,3,...,3,2,...,3,...,3,2,...] with non-consecutive")
print("binary, then show the forced entries create a bad cycle of")
print("length = CL (same as good cycle).")

# ============================================================
# Verify the bad cycle has same length as good cycle
# ============================================================
print(f"\n{'='*72}")
print("BAD CYCLE LENGTH CHECK")
print(f"{'='*72}")

for test_n, test_ms in [(7, [2,3,3,2,3,3,2]), (9, [2,3,3,2,3,3,2,3,3])]:
    target_fc = {p: test_ms[p] for p in range(test_n)}
    words = enumerate_exact_fc_words(test_ms, test_n, target_fc)
    seen = set()
    unique = []
    for w in words:
        canon = canonicalize_word(w)
        if canon not in seen:
            seen.add(canon)
            unique.append(w)
    valid = []
    for w in unique:
        cycle = build_cycle(test_ms, test_n, w)
        if cycle is not None:
            valid.append((w, cycle))
    sweeps = [(w, c, compute_displacement(w, test_n)) for w, c in valid if abs(compute_displacement(w, test_n)) == 2*test_n]

    all_combos = list(itertools.product(
        *[enumerate_state_sequences(test_ms[p], test_ms[p]) for p in range(test_n)]
    ))

    for si, (w, cyc, d) in enumerate(sweeps[:2]):
        for ci, combo in enumerate(all_combos[:4]):
            ell = len(w)
            fc_num = [0]*ell
            pc = [0]*test_n
            for s in range(ell):
                fc_num[s] = pc[w[s]]
                pc[w[s]] += 1

            cs = []
            state = [0]*test_n
            for s in range(ell):
                cs.append(tuple(state))
                p = w[s]
                state[p] = combo[p][fc_num[s]+1]
            good_set = set(cs)

            mcx = defaultdict(dict)
            for s in range(ell):
                p = w[s]
                L = cs[s][(p-1)%test_n]; S = cs[s][p]; R = cs[s][(p+1)%test_n]
                mcx[p][(L, S, R)] = combo[p][fc_num[s]+1]

            # Find forced trap
            all_cfgs = itertools.product(*(range(m) for m in test_ms))
            forced_adj = defaultdict(list)
            for c in all_cfgs:
                if c in good_set: continue
                for p in range(test_n):
                    L = c[(p-1)%test_n]; S = c[p]; R = c[(p+1)%test_n]
                    if (L, S, R) in mcx[p]:
                        Sp = mcx[p][(L, S, R)]
                        if Sp != S:
                            nc = list(c); nc[p] = Sp; nc = tuple(nc)
                            if nc not in good_set:
                                forced_adj[c].append((nc, p))

            trap = set(c for c in forced_adj if forced_adj[c])
            changed = True
            while changed:
                changed = False
                to_remove = set()
                for c in trap:
                    if not any(nc in trap for nc, p in forced_adj[c]): to_remove.add(c)
                if to_remove: trap -= to_remove; changed = True

            # Find cycle
            if trap:
                start = next(iter(trap))
                visited = {start: ([], [])}
                queue = [start]
                shortest = None
                while queue:
                    cur = queue.pop(0)
                    for nxt, p in forced_adj[cur]:
                        if nxt == start and visited[cur][0]:
                            path = visited[cur][0] + [cur]
                            if shortest is None or len(path) < len(shortest):
                                shortest = path
                            break
                        if nxt in trap and nxt not in visited:
                            visited[nxt] = (visited[cur][0] + [cur], visited[cur][1] + [p])
                            if len(visited[nxt][0]) < 40:
                                queue.append(nxt)

                print(f"n={test_n}, sweep {si}, combo {ci}: "
                      f"good CL={ell}, shortest bad cycle={len(shortest) if shortest else '?'}, "
                      f"trap size={len(trap)}")

print("\nDONE")
