#!/usr/bin/env python3
"""
RA14 Part 4: Definitive findings and mechanism analysis.

CRITICAL FINDING from Part 3: Zero entry conflicts at the context level!
The mover contexts DO NOT overlap with non-mover contexts.
Yet forced bad cycles exist. How?

The mechanism: mover contexts from the good cycle ALSO fire at non-good
configs. A mover context (L,S,R)→S' for proc p means f_p(L,S,R)=S'.
If a non-good config has p seeing (L,S,R) with S=current state, then
p is privileged there too (S'≠S). The key is that non-good configs
can have mover contexts that are "out of place" — the context appears
at a config not in the good cycle, but p fires anyway.

No entry conflict needed! The forced cycle uses mover contexts applied
to non-good configs where those contexts happen to appear.

This is SIMPLER than entry conflict. Let me verify and characterize.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict, deque
from verifier import privileged_set, apply_move


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

def build_cycle_configs(ms, n, word, combo):
    ell = len(word)
    fc_num = [0]*ell
    pc = [0]*n
    for s in range(ell):
        fc_num[s] = pc[word[s]]
        pc[word[s]] += 1
    cs = []
    state = [0]*n
    for s in range(ell):
        cs.append(tuple(state))
        p = word[s]
        state[p] = combo[p][fc_num[s]+1]
    return cs, fc_num

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
valid_words = []
for w in unique:
    cycle = build_cycle(ms, n, w)
    if cycle is not None:
        valid_words.append((w, cycle))
sweeps = [(w, c, compute_displacement(w, n)) for w, c in valid_words if abs(compute_displacement(w, n)) == 2*n]

combos_per_proc = [enumerate_state_sequences(ms[p], ms[p]) for p in range(n)]
all_cfgs = list(cartesian(*(range(m) for m in ms)))


# ══════════════════════════════════════════════════════════════════
# Part A: Understand WHY the forced cycle exists without entry conflicts
# ══════════════════════════════════════════════════════════════════
print("=" * 72)
print("PART A: Forced cycle mechanism (no entry conflict needed)")
print("=" * 72)

w0, cyc0, d0 = sweeps[0]
combo0 = tuple(c[0] for c in combos_per_proc)
cs0, fc_num0 = build_cycle_configs(ms, n, w0, combo0)
good_set = set(cs0)
ell = len(w0)

# Extract mover contexts
mcx = defaultdict(dict)
for s in range(ell):
    p = w0[s]
    L = cs0[s][(p-1)%n]; S = cs0[s][p]; R = cs0[s][(p+1)%n]
    mcx[p][(L, S, R)] = combo0[p][fc_num0[s]+1]

# The bad cycle from Part 3:
bad_cycle = [
    (0, 1, 1, 1, 0, 1, 0, 1, 2),
    (0, 1, 1, 0, 0, 1, 0, 1, 2),
    (0, 1, 2, 0, 0, 1, 0, 1, 2),
    (0, 2, 2, 0, 0, 1, 0, 1, 2),
    (0, 2, 0, 0, 0, 1, 0, 1, 2),
    (0, 0, 0, 0, 0, 1, 0, 1, 2),
    (0, 0, 0, 0, 1, 1, 0, 1, 2),
    (0, 0, 0, 1, 1, 1, 0, 1, 2),
    (0, 0, 1, 1, 1, 1, 0, 1, 2),
    (0, 0, 1, 1, 1, 2, 0, 1, 2),
    (0, 0, 1, 1, 2, 2, 0, 1, 2),
    (0, 0, 1, 1, 2, 0, 0, 1, 2),
    (0, 0, 1, 1, 0, 0, 0, 1, 2),
    (0, 0, 1, 1, 0, 0, 1, 1, 2),
    (0, 0, 1, 1, 0, 1, 1, 1, 2),
    (0, 0, 1, 1, 0, 1, 1, 2, 2),
    (0, 0, 1, 1, 0, 1, 1, 2, 0),
    (1, 0, 1, 1, 0, 1, 1, 2, 0),
    (1, 1, 1, 1, 0, 1, 1, 2, 0),
    (1, 1, 1, 1, 0, 1, 1, 0, 0),
    (1, 1, 1, 1, 0, 1, 0, 0, 0),
    (1, 1, 1, 1, 0, 1, 0, 0, 1),
    (0, 1, 1, 1, 0, 1, 0, 0, 1),
    (0, 1, 1, 1, 0, 1, 0, 1, 1),
]
bad_movers = [3, 2, 1, 2, 1, 4, 3, 2, 5, 4, 5, 4, 6, 5, 7, 8, 0, 1, 7, 6, 8, 0, 7, 8]

# For each step: show which mover context is being used
print("Bad cycle mechanism — each step uses a good-cycle mover context:")
print()
for i in range(len(bad_cycle)):
    c = bad_cycle[i]
    p = bad_movers[i]
    L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
    Sp = mcx[p][(L, S, R)]
    nxt = bad_cycle[(i+1) % len(bad_cycle)]

    # Which good-cycle step has this mover context?
    gc_step = None
    for s in range(ell):
        if w0[s] == p:
            gc_L = cs0[s][(p-1)%n]; gc_S = cs0[s][p]; gc_R = cs0[s][(p+1)%n]
            if (gc_L, gc_S, gc_R) == (L, S, R):
                gc_step = s
                break

    # How does the bad config differ from the good config at that step?
    if gc_step is not None:
        gc_c = cs0[gc_step]
        diff_positions = [j for j in range(n) if c[j] != gc_c[j]]
        print(f"  [{i:2d}] fire P{p} ctx=({L},{S},{R})→{Sp}  "
              f"matches GC step {gc_step}  diff from GC at procs {diff_positions}")
    else:
        print(f"  [{i:2d}] fire P{p} ctx=({L},{S},{R})→{Sp}  NO matching GC step!")


# ══════════════════════════════════════════════════════════════════
# Part B: Compare bad cycle to good cycle — structural relationship
# ══════════════════════════════════════════════════════════════════
print("\n" + "=" * 72)
print("PART B: Bad cycle vs good cycle — structural comparison")
print("=" * 72)

print(f"\nGood cycle word: {list(w0)}")
print(f"Bad cycle movers: {bad_movers}")
print(f"Lengths: good={ell}, bad={len(bad_cycle)}")

# Hamming distances between bad cycle configs and nearest good config
print("\nHamming distances from bad cycle to nearest good config:")
for i, bc in enumerate(bad_cycle):
    min_dist = n
    nearest_gc = None
    for gc in cs0:
        d = sum(1 for a, b in zip(bc, gc) if a != b)
        if d < min_dist:
            min_dist = d
            nearest_gc = gc
    print(f"  c[{i:2d}] = {bc}  nearest GC config: {nearest_gc}  dist={min_dist}")


# ══════════════════════════════════════════════════════════════════
# Part C: Does the bad cycle look like a "shadow" of the good cycle?
# ══════════════════════════════════════════════════════════════════
print("\n" + "=" * 72)
print("PART C: Is the bad cycle a shifted/shadow version of the good cycle?")
print("=" * 72)

# The bad cycle has the same length as the good cycle (24).
# Let's check if the mover sequence of the bad cycle is a rotation
# or permutation of the good cycle's mover word.

from collections import Counter
gc_mover_counts = Counter(w0)
bc_mover_counts = Counter(bad_movers)
print(f"Good cycle mover counts: {dict(gc_mover_counts)}")
print(f"Bad cycle mover counts:  {dict(bc_mover_counts)}")
print(f"Same multiset: {gc_mover_counts == bc_mover_counts}")

# Check if bad mover word is a rotation of good mover word
gc_doubled = list(w0) + list(w0)
bc_list = bad_movers
is_rotation = False
for offset in range(ell):
    if gc_doubled[offset:offset+ell] == bc_list:
        is_rotation = True
        print(f"Bad mover word IS a rotation of good mover word (offset {offset})")
        break
if not is_rotation:
    print("Bad mover word is NOT a rotation of good mover word")


# ══════════════════════════════════════════════════════════════════
# Part D: Check smaller n values — does forced cycle exist there?
# ══════════════════════════════════════════════════════════════════
print("\n" + "=" * 72)
print("PART D: Forced cycle check at smaller n")
print("=" * 72)

for test_n in [5, 7]:
    # Try ms with 3 binary + ternary
    if test_n == 5:
        test_ms = [2, 3, 3, 2, 3]
    else:  # n=7
        test_ms = [2, 3, 3, 2, 3, 3, 2]

    tfc = {p: test_ms[p] for p in range(test_n)}
    ws = enumerate_exact_fc_words(test_ms, test_n, tfc)
    seen_t = set()
    unique_t = []
    for w in ws:
        cn = canonicalize_word(w)
        if cn not in seen_t:
            seen_t.add(cn)
            unique_t.append(w)
    valid_t = []
    for w in unique_t:
        cyc = build_cycle(test_ms, test_n, w)
        if cyc is not None:
            valid_t.append((w, cyc))
    sweeps_t = [(w, c, compute_displacement(w, test_n)) for w, c in valid_t
                if abs(compute_displacement(w, test_n)) == 2*test_n]

    if not sweeps_t:
        # Try non-sweep words too
        print(f"n={test_n}, ms={test_ms}: {len(valid_t)} valid words, {len(sweeps_t)} sweeps")
        # Use first valid word
        if valid_t:
            w_t, cyc_t = valid_t[0]
            combos_t = [enumerate_state_sequences(test_ms[p], test_ms[p]) for p in range(test_n)]
            combo_t = tuple(c[0] for c in combos_t)
            cs_t, fc_t = build_cycle_configs(test_ms, test_n, w_t, combo_t)
            good_t = set(cs_t)
            ell_t = len(w_t)

            mcx_t = defaultdict(dict)
            for s in range(ell_t):
                p = w_t[s]
                L = cs_t[s][(p-1)%test_n]; S = cs_t[s][p]; R = cs_t[s][(p+1)%test_n]
                mcx_t[p][(L, S, R)] = combo_t[p][fc_t[s]+1]

            all_t = list(cartesian(*(range(m) for m in test_ms)))
            non_good_t = set(c for c in all_t if c not in good_t)

            fadj_t = defaultdict(list)
            for c in non_good_t:
                for p in range(test_n):
                    L = c[(p-1)%test_n]; S = c[p]; R = c[(p+1)%test_n]
                    if (L, S, R) in mcx_t[p]:
                        Sp = mcx_t[p][(L, S, R)]
                        if Sp != S:
                            nc = list(c); nc[p] = Sp; nc = tuple(nc)
                            if tuple(nc) not in good_t:
                                fadj_t[c].append((tuple(nc), p))

            # Floyd cycle check
            has = False
            for sc in non_good_t:
                if not fadj_t.get(sc): continue
                slow = sc; fast = sc
                for _ in range(len(non_good_t)):
                    if not fadj_t.get(slow): break
                    slow = fadj_t[slow][0][0]
                    if not fadj_t.get(fast): break
                    fast = fadj_t[fast][0][0]
                    if not fadj_t.get(fast): break
                    fast = fadj_t[fast][0][0]
                    if slow == fast:
                        has = True
                        break
                if has: break
            print(f"  First valid word: {list(w_t)}, disp={compute_displacement(w_t, test_n)}")
            print(f"  Forced bad cycle: {has}")
    else:
        print(f"n={test_n}, ms={test_ms}: {len(sweeps_t)} sweeps")
        for wi, (w_t, c_t, d_t) in enumerate(sweeps_t[:2]):
            combos_t = [enumerate_state_sequences(test_ms[p], test_ms[p]) for p in range(test_n)]
            combo_t = tuple(c[0] for c in combos_t)
            cs_t, fc_t = build_cycle_configs(test_ms, test_n, w_t, combo_t)
            good_t = set(cs_t)
            ell_t = len(w_t)

            mcx_t = defaultdict(dict)
            for s in range(ell_t):
                p = w_t[s]
                L = cs_t[s][(p-1)%test_n]; S = cs_t[s][p]; R = cs_t[s][(p+1)%test_n]
                mcx_t[p][(L, S, R)] = combo_t[p][fc_t[s]+1]

            all_t = list(cartesian(*(range(m) for m in test_ms)))
            non_good_t = set(c for c in all_t if c not in good_t)

            fadj_t = defaultdict(list)
            for c in non_good_t:
                for p in range(test_n):
                    L = c[(p-1)%test_n]; S = c[p]; R = c[(p+1)%test_n]
                    if (L, S, R) in mcx_t[p]:
                        Sp = mcx_t[p][(L, S, R)]
                        if Sp != S:
                            nc = list(c); nc[p] = Sp; nc = tuple(nc)
                            if tuple(nc) not in good_t:
                                fadj_t[c].append((tuple(nc), p))

            has = False
            for sc in non_good_t:
                if not fadj_t.get(sc): continue
                slow = sc; fast = sc
                for _ in range(len(non_good_t)):
                    if not fadj_t.get(slow): break
                    slow = fadj_t[slow][0][0]
                    if not fadj_t.get(fast): break
                    fast = fadj_t[fast][0][0]
                    if not fadj_t.get(fast): break
                    fast = fadj_t[fast][0][0]
                    if slow == fast:
                        has = True
                        break
                if has: break
            print(f"  Sweep {wi} (disp={d_t}): forced bad cycle = {has}")


# ══════════════════════════════════════════════════════════════════
# Part E: The "shadow cycle" connection
# ══════════════════════════════════════════════════════════════════
print("\n" + "=" * 72)
print("PART E: Shadow cycle connection")
print("=" * 72)

# The bad cycle has length 24 = same as good cycle.
# The bad cycle movers have the same multiset as good cycle movers.
# This strongly suggests it's the SHADOW CYCLE from the Shadow Cycle Mirror Theorem.

# Let's check: for each bad config, compute the "offset" from the good cycle
# The shadow cycle should have each config offset by exactly 1 position from
# the corresponding good config.

print("Config-by-config comparison:")
print(f"{'Step':>4} {'Good config':>30} {'Bad config':>30} {'Diff positions':>20}")
for i in range(min(ell, len(bad_cycle))):
    gc = cs0[i]
    bc = bad_cycle[i]
    diffs = [j for j in range(n) if gc[j] != bc[j]]
    print(f"{i:4d} {str(gc):>30} {str(bc):>30} {str(diffs):>20}")


# ══════════════════════════════════════════════════════════════════
# Part F: Formal proof requirements summary
# ══════════════════════════════════════════════════════════════════
print("\n" + "=" * 72)
print("PART F: FORMAL PROOF REQUIREMENTS")
print("=" * 72)

print("""
=== DEFINITIVE FINDINGS ===

1. EXISTENTIAL NON-GOOD SUCCESSOR IS FALSE (even in valid systems)
   - Sol3 n=5: 3 configs where ALL daemon choices → good
   - CUP-2 n=5: 8 such configs
   - This is EXPECTED: these configs are 1-step convergent

2. THE RIGHT APPROACH: Exhibit a bad cycle (ShadowTrap)
   - For sub-threshold systems, the FORCED GRAPH
     (using only good-cycle mover contexts) has bad cycles
   - 512/512 instances confirmed at n=9
   - The forced graph is TRANSITION-INDEPENDENT
     (depends only on the good cycle, not the completion)

3. FORCED CYCLE MECHANISM (no entry conflict needed):
   - Good cycle mover context: f_p(L,S,R) = S' ≠ S
   - This is FORCED by the good cycle (consistency)
   - Non-good configs can also have proc p seeing (L,S,R)
   - At those configs, p is forced-privileged: f_p(L,S,R) = S' ≠ S
   - The move produces a new config that may also be non-good
   - Chain these moves → forced cycle

4. BAD CYCLE STRUCTURE:
   - Length = same as good cycle (24 at n=9)
   - Mover multiset = same as good cycle
   - Configs differ from good cycle at 5-7 positions
   - Contains multi-priv configs (not single-priv-only)
   - Looks like a "shadow" of the good cycle

5. FOR LEAN FORMALIZATION:
   (a) Define: forcedMove(gc, c, p) — proc p fires at non-good c
       because its context matches a mover context from gc
   (b) Define: shadowTrap(gc) — a cycle of non-good configs
       connected by forcedMove edges
   (c) Theorem: For sub-threshold sweep cycles, shadowTrap exists
   (d) Corollary: badStep has a cycle → ¬WellFounded → ¬converges

   The key simplification: we don't need forcedSucc_nonGood at all.
   We just need to EXHIBIT the shadow trap, which is a finite
   combinatorial object verifiable by decide/native_decide.

6. PROOF STRUCTURE:
   Given: good cycle GC with mover contexts MCX
   Construct: shadow cycle SC (24 configs + 24 movers)
   Verify (mechanically, step by step):
     ∀i, SC[i] ∉ GC.configs                    -- non-good
     ∀i, (L,S,R) of SC[i] at mover[i] ∈ MCX    -- context matches
     ∀i, MCX[mover[i]](L,S,R) ≠ S              -- privileged
     ∀i, apply_move(SC[i], mover[i]) = SC[i+1]  -- transition correct
   Conclude: badStep cycle exists → ¬WellFounded(badStep)
""")
