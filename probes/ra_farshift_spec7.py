#!/usr/bin/env python3
"""
RA Part 7: Why forced-entry transitions never go from non-good to good.

KEY OBSERVATION from Part 6: In the full forced-entry graph, NO non-good config
transitions to a good config. edge_to_good = 0.

If this is UNIVERSAL, it means:
- The forced-entry graph decomposes into connected components
- The good cycle is one component
- All other cycles are in non-good components
- Any non-good config with an outgoing edge stays in non-good territory

This would be the CLEANEST proof: show that forced entries preserve "non-good",
then show the non-good subgraph has a cycle (by finiteness + existence of some
non-good config with an outgoing edge).

WHY would forced entries preserve non-good?

Claim: if c is non-good and p is forced-privileged at c (context (L,S,R) matches
forced entry, output S' ≠ S), then move(c, p) = c' is also non-good.

Proof attempt: Suppose c' IS good. Then c' = good_cfg[j] for some j.
At good step j, some mover p_j fires with context (L_j, S_j, R_j).
The previous good config is good_cfg[j-1].
We have: c' = good_cfg[j] = move(c, p).
So c and good_cfg[j] differ only at position p.
Now c[p] = S ≠ S' = c'[p] = good_cfg[j][p].

Also: good_cfg[j-1] and good_cfg[j] differ only at position p_{j-1}.
So good_cfg[j] differs from good_cfg[j-1] only at p_{j-1}.

For c to map to good_cfg[j] by firing p:
c must equal good_cfg[j] at all positions except p, where c[p] = S.

Now: is there a good config that differs from good_cfg[j] only at position p,
with value S at position p?

If p ≠ p_{j-1}: good_cfg[j-1] differs from good_cfg[j] at p_{j-1} ≠ p.
So good_cfg[j-1][p] = good_cfg[j][p] = S' ≠ S.
We need a good config that matches good_cfg[j] everywhere except at p.
But good configs are the orbit of the good cycle — they form a specific sequence.

Actually, this is getting complicated. Let me just verify computationally.
"""

import itertools
from collections import Counter

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
        p = word[s]; fc[p] += 1; state[p] = combo[p][fc[p]]
    if tuple(state) != configs[0]: return None
    if len(set(configs)) != ell: return None
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
                seq.append(nv); dfs(seq, remaining-1); seq.pop()
    dfs([0], k)
    return seqs

def compute_displacement(word, n):
    total = 0; ell = len(word)
    for i in range(ell):
        diff = (word[(i+1)%ell] - word[i]) % n
        if diff == 1: total += 1
        elif diff == n-1: total -= 1
    return total

def extract_forced_entries(ms, n, word, configs):
    ell = len(word); entries = {}
    for s in range(ell):
        p = word[s]; c = configs[s]
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        Sp = configs[(s+1)%ell][p]
        if p not in entries: entries[p] = {}
        entries[p][(L,S,R)] = Sp
    return entries

# ============================================================
# Test at n=9: verify edge_to_good = 0 for ALL words × combos
# ============================================================
n = 9
ms = [2,3,3,2,3,3,2,3,3]
CL = sum(ms)
target_fc = {p: ms[p] for p in range(n)}
words = enumerate_exact_fc_words(ms, n, target_fc)
seen = set()
unique = []
for w in words:
    canon = tuple(min(w[i:]+w[:i] for i in range(len(w))))
    if canon not in seen: seen.add(canon); unique.append(w)
valid_words = [w for w in unique if abs(compute_displacement(w, n)) == 2*n]
all_combos = {}
for p in range(n):
    all_combos[p] = enumerate_state_sequences(ms[p], ms[p])

print(f"n={n}, ms={ms}, sweeps={len(valid_words)}")

# Check edge_to_good for first 3 (word, combo) pairs in detail
# Then verify all 512
print(f"\n{'='*72}")
print("edge_to_good check for ALL words × combos")
print(f"{'='*72}")

total_tests = 0
total_edge_to_good = 0
total_non_good_with_edge = 0
total_non_good_cycles = 0

for wi, w in enumerate(valid_words):
    combo_lists = [all_combos[p] for p in range(n)]
    for combo_idx in itertools.product(*[range(len(c)) for c in combo_lists]):
        combo_t = tuple(combo_lists[p][combo_idx[p]] for p in range(n))
        cfgs = build_cycle_with_combo(ms, n, w, combo_t)
        if cfgs is None: continue
        gs = set(cfgs)
        fe = extract_forced_entries(ms, n, w, cfgs)
        total_tests += 1

        edge_to_good = 0
        non_good_with_edge = 0

        for vals in itertools.product(*[range(m) for m in ms]):
            c = tuple(vals)
            if c in gs: continue
            for p in range(n):
                L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
                if p in fe and (L,S,R) in fe[p]:
                    Sp = fe[p][(L,S,R)]
                    if Sp != S:
                        nxt = list(c); nxt[p] = Sp; nxt = tuple(nxt)
                        if nxt in gs:
                            edge_to_good += 1
                        else:
                            non_good_with_edge += 1
                        break

        total_edge_to_good += edge_to_good
        total_non_good_with_edge += non_good_with_edge

        if edge_to_good > 0:
            print(f"  EDGE_TO_GOOD! word {wi}, combo {combo_idx}: {edge_to_good} edges")

print(f"\nTotal tests: {total_tests}")
print(f"Total edge_to_good: {total_edge_to_good}")
print(f"Total non-good with edge: {total_non_good_with_edge}")
print(f"edge_to_good is ALWAYS 0: {total_edge_to_good == 0}")

# ============================================================
# WHY is edge_to_good always 0?
# ============================================================
print(f"\n{'='*72}")
print("PROOF: Why forced entries preserve non-good")
print(f"{'='*72}")

# Take first (word, combo), investigate structure
w = valid_words[0]
combo = tuple(all_combos[p][0] for p in range(n))
cfgs = build_cycle_with_combo(ms, n, w, combo)
gs = set(cfgs)
fe = extract_forced_entries(ms, n, w, cfgs)

# For each good config, what are its "pre-images" under forced entries?
# That is: which configs c have forced entry (p, L, S, R) -> S' such that
# move(c, p) = good_cfg[j]?
print("Pre-images of good configs under forced entries:")
for j in range(CL):
    gc_j = cfgs[j]
    pre_images = []
    # c differs from gc_j at exactly one position p, where c[p] = S ≠ gc_j[p] = S'
    # AND (c[p-1], c[p], c[p+1]) = (gc_j[p-1], S, gc_j[p+1]) is a forced entry for p
    # AND forced[p][(gc_j[p-1], S, gc_j[p+1])] = S' = gc_j[p]
    for p in range(n):
        if p not in fe: continue
        L = gc_j[(p-1)%n]; Sp = gc_j[p]; R = gc_j[(p+1)%n]
        # Need S ≠ Sp such that forced[p][(L, S, R)] = Sp
        for S in range(ms[p]):
            if S == Sp: continue
            if (L, S, R) in fe[p] and fe[p][(L, S, R)] == Sp:
                # Build pre-image
                c = list(gc_j)
                c[p] = S
                c = tuple(c)
                if c not in gs:
                    pre_images.append((c, p, S, Sp))
    if pre_images:
        print(f"  good[{j}]: {len(pre_images)} non-good pre-images")
        for c, p, S, Sp in pre_images[:3]:
            print(f"    P{p}: S={S}->S'={Sp}, pre={c}")
    else:
        print(f"  good[{j}]: 0 non-good pre-images")

# ============================================================
# AHA: Let's count carefully. A non-good config c maps to good config g
# if and only if:
# 1. c differs from g at exactly position p (the mover)
# 2. c[p] has forced entry leading to g[p]
# 3. c is not good
#
# For this to happen: there must be a forced entry at proc p with
# context (g[p-1], S, g[p+1]) -> g[p] where S ≠ g[p].
#
# Now: forced entries come from the good cycle. At good step k,
# mover p_k has context (L_k, S_k, R_k) -> S'_k.
# So forced[p_k][(L_k, S_k, R_k)] = S'_k.
#
# For a pre-image of g: we need forced[p][(g[p-1], S, g[p+1])] = g[p].
# This means (g[p-1], S, g[p+1]) = (L_k, S_k, R_k) for some good step k
# where p_k = p, and S'_k = g[p].
#
# Now: S_k is the value at p in good_cfg[k], and S'_k = g[p] is the value
# at p in good_cfg[k+1]. So g[p] = good_cfg[k+1][p].
#
# Also: L_k = good_cfg[k][p-1] = g[p-1] and R_k = good_cfg[k][p+1] = g[p+1].
# So good_cfg[k][p-1] = g[p-1] and good_cfg[k][p+1] = g[p+1].
#
# The pre-image c equals g at all positions except p, where c[p] = S = S_k = good_cfg[k][p].
# So c = g with c[p] = good_cfg[k][p].
#
# But wait: good_cfg[k] and c might differ at other positions!
# c[i] = g[i] for i ≠ p, and c[p] = good_cfg[k][p].
# good_cfg[k][i] might differ from g[i] at positions i ≠ p.
#
# For c to be GOOD, c must equal some good_cfg[m].
# c equals g everywhere except at p, where c[p] = good_cfg[k][p].
#
# If c IS good, say c = good_cfg[m], then good_cfg[m] and g differ only at p.
# Since g is also good, say g = good_cfg[j], this means good_cfg[m] and good_cfg[j]
# differ only at position p. And good_cfg[m][p] = good_cfg[k][p].
#
# So: c is good iff there exists good_cfg[m] that equals good_cfg[j] everywhere
# except at p, with good_cfg[m][p] = good_cfg[k][p].
#
# This CAN happen. For example, if good_cfg[k] = good_cfg[j] everywhere except
# at p (and p_k = p, the mover at step k), then c = good_cfg[k], which IS good.
# In fact, if k = j-1 (the step just before j), then good_cfg[k] and good_cfg[j]
# differ only at p_{k} = p_k. If p_k = p (the same proc), then c = good_cfg[k]
# which is good. But we already excluded c ∈ gs.
#
# The question is: are there OTHER good configs (not good_cfg[j-1]) that differ
# from good_cfg[j] only at p? This depends on the cycle structure.

# Let me check: for each good config, how many other good configs differ at exactly 1 position?
print(f"\n\nGood-config neighbor structure:")
for j in range(CL):
    gj = cfgs[j]
    neighbors = []
    for m in range(CL):
        if m == j: continue
        gm = cfgs[m]
        diffs = [i for i in range(n) if gj[i] != gm[i]]
        if len(diffs) == 1:
            neighbors.append((m, diffs[0]))
    print(f"  good[{j}]: {len(neighbors)} neighbors at dist 1: {neighbors}")

# ============================================================
# For the forced transition from c -> g:
# c = good_cfg[j] with c[p] = good_cfg[k][p].
# c is good iff c equals some good config.
# Since c = g except at p: c is good iff there's a good config
# that matches g everywhere except possibly at p.
# ============================================================
# The pre-image check: for each g=good[j], for each forced entry p with
# context (g[p-1], S, g[p+1]) -> g[p]:
# c = g with c[p] = S. Is c good?
print(f"\nPre-image goodness check:")
for j in range(CL):
    g = cfgs[j]
    for p in range(n):
        if p not in fe: continue
        L = g[(p-1)%n]; Sp = g[p]; R = g[(p+1)%n]
        for S in range(ms[p]):
            if S == Sp: continue
            if (L, S, R) in fe[p] and fe[p][(L, S, R)] == Sp:
                c = list(g); c[p] = S; c = tuple(c)
                is_good = c in gs
                if not is_good:
                    pass  # expected: non-good pre-image → edge to good exists? No!
                else:
                    # c IS good, so the pre-image is a good config → good-to-good edge
                    # This is just a good cycle transition
                    idx = cfgs.index(c)
                    # Is this the standard transition? c -> g via mover p
                    # Check: at good step idx, is mover p?
                    # If c = good[idx] and g = good[j], and they differ at p,
                    # then idx should be j-1 (mod CL) and w[idx] = p
                    prev_step = (j - 1) % CL
                    is_std = (idx == prev_step and w[prev_step] == p)
                    if not is_std:
                        print(f"  NON-STANDARD: good[{idx}] -> good[{j}] via P{p} (expected step {prev_step}, mover P{w[prev_step]})")

print(f"\nCONCLUSION:")
print(f"Every pre-image of a good config under forced entries is EITHER:")
print(f"  (a) The previous good config (standard transition), or")
print(f"  (b) A non-good config")
print(f"If (b), does the forced-entry graph send it to the good config?")
print(f"The Part 6 test showed edge_to_good = 0. But that used 'smallest-index'.")
print(f"Let me check: is the non-good pre-image's smallest-index privileged proc")
print(f"actually p (leading to the good config)?")

print(f"\n{'='*72}")
print("CRITICAL: Why smallest-index never sends non-good to good")
print(f"{'='*72}")

# For each non-good pre-image of a good config:
for j in range(CL):
    g = cfgs[j]
    for p in range(n):
        if p not in fe: continue
        L = g[(p-1)%n]; Sp = g[p]; R = g[(p+1)%n]
        for S in range(ms[p]):
            if S == Sp: continue
            if (L, S, R) in fe[p] and fe[p][(L, S, R)] == Sp:
                c = list(g); c[p] = S; c = tuple(c)
                if c in gs: continue
                # c is non-good, and firing p at c gives good[j].
                # What is the smallest-index privileged proc at c?
                for p2 in range(n):
                    L2 = c[(p2-1)%n]; S2 = c[p2]; R2 = c[(p2+1)%n]
                    if p2 in fe and (L2,S2,R2) in fe[p2]:
                        Sp2 = fe[p2][(L2,S2,R2)]
                        if Sp2 != S2:
                            if p2 < p:
                                print(f"  good[{j}] pre via P{p}: smallest priv is P{p2} < P{p} -> edge to NON-good")
                            elif p2 == p:
                                print(f"  good[{j}] pre via P{p}: smallest priv IS P{p} -> edge to GOOD!")
                            else:
                                print(f"  good[{j}] pre via P{p}: smallest priv is P{p2} > P{p} (unexpected)")
                            break
                else:
                    print(f"  good[{j}] pre via P{p}: NO forced priv at all")
