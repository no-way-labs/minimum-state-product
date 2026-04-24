#!/usr/bin/env python3
"""
RA Part 2: Deep dive into the bad cycle structure.

Key findings from Part 1:
1. Movers are DIFFERENT (never same as good cycle)
2. NOT a constant shift (only first + last few steps match)
3. Privilege is NOT unique — most steps have 2 privileged procs

Questions:
A. What is the tie-breaking rule?
B. Is there a pattern to which proc is chosen?
C. Can we define the bad cycle WITHOUT depending on unique privilege?
D. What about using the FULL system's transition function (not just forced entries)?
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

def build_cycle_with_combo(ms, n, word, combo):
    ell = len(word)
    fc = [0]*n
    configs = []
    state = list(combo[p][0] for p in range(n))
    for s in range(ell):
        configs.append(tuple(state))
        p = word[s]
        fc[p] += 1
        state[p] = combo[p][fc[p]]
    if tuple(state) != configs[0]:
        return None
    if len(set(configs)) != ell:
        return None
    return configs

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
                dfs(seq, remaining - 1)
                seq.pop()
    dfs([0], k)
    return seqs

def compute_displacement(word, n):
    total = 0
    ell = len(word)
    for i in range(ell):
        diff = (word[(i+1)%ell] - word[i]) % n
        if diff == 1: total += 1
        elif diff == n-1: total -= 1
    return total

def extract_forced_entries(ms, n, word, configs):
    ell = len(word)
    entries = {}
    for s in range(ell):
        p = word[s]
        c = configs[s]
        L = c[(p-1) % n]; S = c[p]; R = c[(p+1) % n]
        c_next = configs[(s+1) % ell]
        Sp = c_next[p]
        if p not in entries: entries[p] = {}
        entries[p][(L, S, R)] = Sp
    return entries

# ============================================================
# Setup
# ============================================================
n = 9
ms = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = sum(ms)

target_fc = {p: ms[p] for p in range(n)}
words = enumerate_exact_fc_words(ms, n, target_fc)
seen = set()
unique = []
for w in words:
    canon = tuple(min(w[i:]+w[:i] for i in range(len(w))))
    if canon not in seen:
        seen.add(canon)
        unique.append(w)
valid_words = [w for w in unique if abs(compute_displacement(w, n)) == 2*n]

all_combos = {}
for p in range(n):
    all_combos[p] = enumerate_state_sequences(ms[p], ms[p])

word = valid_words[0]
combo = tuple(all_combos[p][0] for p in range(n))
configs = build_cycle_with_combo(ms, n, word, combo)
good_set = set(configs)
forced = extract_forced_entries(ms, n, word, configs)

# ============================================================
# Question A: What are ALL privileged procs at each step?
# When there's a tie, which one leads to a valid cycle?
# ============================================================
print("="*72)
print("QUESTION A: Privilege structure at each step")
print("="*72)

q, d = 8, 1
c0 = list(configs[0])
c0[q] = (c0[q] + d) % ms[q]
c0 = tuple(c0)

# Follow the orbit, recording ALL choices
path = [c0]
movers_chosen = []
all_priv_at_step = []
cur = c0

for step in range(CL):
    privileged = []
    for p in range(n):
        L = cur[(p-1)%n]; S = cur[p]; R = cur[(p+1)%n]
        if p in forced and (L,S,R) in forced[p]:
            Sp = forced[p][(L,S,R)]
            if Sp != S:
                privileged.append((p, Sp))
    all_priv_at_step.append(privileged)

    # The first script chose privileged[0] — what determines the ordering?
    # Let's check: is it always the SMALLEST proc index?
    p, Sp = privileged[0]  # This is ordered by proc index (smallest first)
    movers_chosen.append(p)
    nxt = list(cur)
    nxt[p] = Sp
    cur = tuple(nxt)
    if step < CL - 1:
        path.append(cur)

print("Step | Chosen | All privileged procs")
for s in range(CL):
    procs = [p for p, _ in all_priv_at_step[s]]
    print(f"  [{s:2d}] P{movers_chosen[s]}      priv={procs}")

# ============================================================
# Question B: Does choosing the OTHER privileged proc also work?
# ============================================================
print(f"\n{'='*72}")
print("QUESTION B: What if we choose the LAST privileged proc instead?")
print("="*72)

path2 = [c0]
movers2 = []
cur = c0
for step in range(CL + 5):
    privileged = []
    for p in range(n):
        L = cur[(p-1)%n]; S = cur[p]; R = cur[(p+1)%n]
        if p in forced and (L,S,R) in forced[p]:
            Sp = forced[p][(L,S,R)]
            if Sp != S:
                privileged.append((p, Sp))
    if not privileged:
        print(f"  STUCK at step {step}")
        break
    # Choose LAST instead of first
    p, Sp = privileged[-1]
    movers2.append(p)
    nxt = list(cur)
    nxt[p] = Sp
    cur = tuple(nxt)
    if cur == c0:
        print(f"  Cycle closes at step {step+1}, length = {len(path2)}")
        disjoint2 = all(c not in good_set for c in path2)
        print(f"  Disjoint from good: {disjoint2}")
        break
    if cur in set(path2):
        print(f"  Subcycle at step {step+1}")
        break
    path2.append(cur)

print(f"  Movers (last-pref): {movers2[:CL]}")
print(f"  Movers (first-pref): {movers_chosen}")

# ============================================================
# Question C: Key insight — at steps with 2 privileged procs,
# do BOTH choices lead to the same next-step?
# Or does the choice matter?
# ============================================================
print(f"\n{'='*72}")
print("QUESTION C: At ambiguous steps, try ALL branches")
print("="*72)

# At step 1, privileged = [6, 8]. What happens if we fire P8 instead of P6?
for s_test in [1, 2, 9, 10]:
    if len(all_priv_at_step[s_test]) < 2:
        continue
    for p_choice, Sp_choice in all_priv_at_step[s_test]:
        c_test = list(path[s_test])
        c_test[p_choice] = Sp_choice
        c_test = tuple(c_test)
        # Check if c_test equals the actual next config
        actual_next = path[s_test + 1] if s_test + 1 < CL else c0
        match = "SAME" if c_test == actual_next else "DIFF"
        # How many priv at this new config?
        nxt_priv = []
        for p2 in range(n):
            L = c_test[(p2-1)%n]; S2 = c_test[p2]; R = c_test[(p2+1)%n]
            if p2 in forced and (L,S2,R) in forced[p2]:
                Sp2 = forced[p2][(L,S2,R)]
                if Sp2 != S2:
                    nxt_priv.append(p2)
        print(f"  Step {s_test}: fire P{p_choice} -> {match} as chosen path, next_priv={nxt_priv}")

# ============================================================
# Question D: Does the bad cycle actually need the system's
# transition function, not just forced entries?
# For BadCycleData, we need: privileged sys (cfg k) (mover k)
# This means: sys.f (mover k) (L, S, R) ≠ S
# NOT just: forced[mover k][(L,S,R)] ≠ S
#
# The forced entries tell us what sys.f MUST be at certain contexts.
# At a bad config, the privileged proc has context (L,S,R) that
# appears in the forced entries. So sys.f(L,S,R) = forced(L,S,R) ≠ S.
#
# But wait: at a bad config, the mover might have a context that
# does NOT appear in the forced entries. Is that possible?
# ============================================================
print(f"\n{'='*72}")
print("QUESTION D: Are all bad-cycle contexts in forced entries?")
print("="*72)

all_in_forced = True
for s in range(CL):
    p = movers_chosen[s]
    c = path[s]
    L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
    ctx = (L, S, R)
    if p not in forced or ctx not in forced[p]:
        print(f"  [{s}] P{p}: ctx={ctx} NOT in forced entries!")
        all_in_forced = False
    else:
        Sp = forced[p][ctx]
        if Sp == S:
            print(f"  [{s}] P{p}: ctx={ctx} -> {Sp} = S (NOT privileged!)")
            all_in_forced = False
print(f"All contexts in forced entries and privileged: {all_in_forced}")

# ============================================================
# Question E: What is the MOVER WORD of the bad cycle?
# Is it a rotation/permutation of the good cycle's mover word?
# ============================================================
print(f"\n{'='*72}")
print("QUESTION E: Bad cycle mover word structure")
print("="*72)

good_word = list(word)
bad_word = movers_chosen

# Check if bad_word is a rotation of good_word
for rot in range(CL):
    rotated = good_word[rot:] + good_word[:rot]
    if rotated == bad_word:
        print(f"  Bad word = rotation of good word by {rot}")
        break
else:
    print(f"  Bad word is NOT a rotation of good word")

# Check fire counts
from collections import Counter
print(f"  Good word fire counts: {dict(Counter(good_word))}")
print(f"  Bad word fire counts: {dict(Counter(bad_word))}")

# ============================================================
# Question F: For Lean, can we define the bad cycle as a
# RECURSION: cfg[0] = c0, cfg[k+1] = move sys (cfg[k]) (mover[k])?
# The key issue is defining mover[k]. If privilege isn't unique,
# we need an explicit rule.
#
# But wait — we're constructing a BadCycleData, not proving one exists.
# We can CHOOSE the mover at each step. We just need:
# 1. The chosen mover IS privileged
# 2. Firing it gives the next config
# 3. All configs are non-good and distinct
#
# So the non-uniqueness of privilege is NOT a problem!
# We just need to specify WHICH privileged proc to fire.
# ============================================================
print(f"\n{'='*72}")
print("QUESTION F: Defining bad mover word")
print("="*72)

# The bad mover word depends on the good mover word.
# Let's see the relationship more carefully.
print("Good word:  ", good_word)
print("Bad word:   ", bad_word)
print("Diff:       ", ["." if g==b else f"{g}>{b}" for g, b in zip(good_word, bad_word)])

# Look at the structure: good = CW sweep, word starts at P0
# Good word moves CW: 0,8,7,6,5,4,3,2,1, then back...
# Bad word starts at P7 and also moves CW-ish

# ============================================================
# Question G: TRY A DIFFERENT APPROACH.
# Instead of "shift one proc" then follow forced dynamics,
# what if the bad cycle is defined by a FIXED mover permutation?
# ============================================================
print(f"\n{'='*72}")
print("QUESTION G: Universal test — does mover word depend on combo?")
print("="*72)

# For the same word, different combos: does the bad mover word change?
mover_words_seen = set()
for combo_idx in itertools.product(*[range(len(all_combos[p])) for p in range(n)]):
    combo_t = tuple(all_combos[p][combo_idx[p]] for p in range(n))
    cfgs = build_cycle_with_combo(ms, n, word, combo_t)
    if cfgs is None: continue
    gs = set(cfgs)
    fe = extract_forced_entries(ms, n, word, cfgs)

    c0t = list(cfgs[0])
    c0t[8] = (c0t[8] + 1) % ms[8]
    c0t = tuple(c0t)
    if c0t in gs: continue

    # Follow forced orbit
    cur = c0t
    bm = []
    for step in range(CL):
        priv = []
        for p in range(n):
            L = cur[(p-1)%n]; S = cur[p]; R = cur[(p+1)%n]
            if p in fe and (L,S,R) in fe[p]:
                Sp = fe[p][(L,S,R)]
                if Sp != S:
                    priv.append((p, Sp))
        if not priv: break
        p, Sp = priv[0]  # Smallest proc index
        bm.append(p)
        nxt = list(cur); nxt[p] = Sp; cur = tuple(nxt)

    mover_words_seen.add(tuple(bm))

print(f"Number of distinct bad mover words for this sweep word: {len(mover_words_seen)}")
for bw in sorted(mover_words_seen):
    print(f"  {list(bw)}")

# ============================================================
# Question H: At n=7, is the structure the same?
# ============================================================
print(f"\n{'='*72}")
print("QUESTION H: Test at n=7")
print("="*72)

n7 = 7
ms7 = [2, 3, 3, 2, 3, 3, 3]
CL7 = sum(ms7)  # = 19? No: 2+3+3+2+3+3+3 = 19
print(f"n={n7}, ms={ms7}, CL={CL7}")

target_fc7 = {p: ms7[p] for p in range(n7)}
words7 = enumerate_exact_fc_words(ms7, n7, target_fc7)
seen7 = set()
unique7 = []
for w in words7:
    canon = tuple(min(w[i:]+w[:i] for i in range(len(w))))
    if canon not in seen7:
        seen7.add(canon)
        unique7.append(w)
valid7 = [w for w in unique7 if abs(compute_displacement(w, n7)) == 2*n7]
print(f"Sweep words at n=7: {len(valid7)}")

all_combos7 = {}
for p in range(n7):
    all_combos7[p] = enumerate_state_sequences(ms7[p], ms7[p])

total7, pass7, mover_same7, mover_diff7, unique_priv_fail7 = 0, 0, 0, 0, 0

for wi, w in enumerate(valid7):
    combo_lists7 = [all_combos7[p] for p in range(n7)]
    for combo_idx in itertools.product(*[range(len(c)) for c in combo_lists7]):
        combo_t = tuple(combo_lists7[p][combo_idx[p]] for p in range(n7))
        cfgs = build_cycle_with_combo(ms7, n7, w, combo_t)
        if cfgs is None: continue
        gs = set(cfgs)
        fe = extract_forced_entries(ms7, n7, w, cfgs)
        total7 += 1

        # Try all q, d
        found = False
        for qq in range(n7):
            for dd in range(1, ms7[qq]):
                c0t = list(cfgs[0])
                c0t[qq] = (c0t[qq] + dd) % ms7[qq]
                c0t = tuple(c0t)
                if c0t in gs: continue

                cur = c0t
                bpath = [cur]
                bm = []
                priv_unique = True
                for step in range(CL7 + 5):
                    priv = []
                    for p in range(n7):
                        L = cur[(p-1)%n7]; S = cur[p]; R = cur[(p+1)%n7]
                        if p in fe and (L,S,R) in fe[p]:
                            Sp = fe[p][(L,S,R)]
                            if Sp != S:
                                priv.append((p, Sp))
                    if not priv: break
                    if len(priv) > 1: priv_unique = False
                    p, Sp = priv[0]
                    bm.append(p)
                    nxt = list(cur); nxt[p] = Sp; cur = tuple(nxt)
                    if cur == c0t:
                        if len(bpath) == CL7:
                            bs = set(bpath)
                            if bs.isdisjoint(gs):
                                ms_same = all(bm[s] == w[s] for s in range(CL7))
                                if ms_same: mover_same7 += 1
                                else: mover_diff7 += 1
                                if not priv_unique: unique_priv_fail7 += 1
                                pass7 += 1
                                found = True
                        break
                    if cur in set(bpath): break
                    bpath.append(cur)
                if found: break
            if found: break
        if not found:
            print(f"  FAIL at n=7: word={w}, combo_idx={combo_idx}")

print(f"n=7 results: {pass7}/{total7} pass, movers same={mover_same7}, diff={mover_diff7}, priv_not_unique={unique_priv_fail7}")
