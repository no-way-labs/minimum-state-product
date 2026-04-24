#!/usr/bin/env python3
"""ra12_farshift_claim2_deep.py — Deep analysis of Claim 2 proof mechanism.

The question: WHY does no non-good config map to good via forced entries?

Two sub-questions:
(A) For each good g_k and position i: if move(c,i) = g_k where c non-good,
    then c = (g_k with c[i] set to some x != g_k[i]).
    The forced entry f_i(L, x, R) = g_k[i] must exist.
    For this entry to exist, (L, x, R) must appear at some step in the cycle
    where proc i is active (mover or non-mover).

(B) If (L, x, R) IS forced, does the forced value equal g_k[i]?
    If the forced value is something ELSE, then move(c,i) != g_k. No violation.
    If the forced value IS g_k[i], then c maps to g_k. But then c is good
    (by the cross-mapping analysis).

We need to verify that case (B) always resolves: either the entry maps elsewhere,
or the resulting c is good.
"""

import sys, os, itertools
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian

def compute_displacement(word, n):
    total = 0; ell = len(word)
    for i in range(ell):
        diff = (word[(i+1)%ell] - word[i]) % n
        if diff == 1: total += 1
        elif diff == n-1: total -= 1
    return total

def enumerate_sweep_words(ms, n):
    CL = sum(ms)
    target_fc = {p: ms[p] for p in range(n)}
    ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}
    results = []
    def dfs(word, fc):
        if len(word) == CL:
            if abs(word[-1] - word[0]) % n in (1, n-1):
                config = [0]*n
                for p in word: config[p] = (config[p]+1) % ms[p]
                if all(c == 0 for c in config):
                    if abs(compute_displacement(word, n)) == 2*n:
                        results.append(tuple(word))
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            if fc[nxt] < target_fc[nxt]:
                fc[nxt] += 1; word.append(nxt)
                if sum(target_fc[p] - fc[p] for p in range(n)) <= CL - len(word):
                    dfs(word, fc)
                word.pop(); fc[nxt] -= 1
    for p in range(n):
        if target_fc[p] > 0:
            fc = {q: 0 for q in range(n)}; fc[p] = 1
            dfs([p], fc)
    seen = set(); unique = []
    for w in results:
        canon = tuple(min(w[i:]+w[:i] for i in range(len(w))))
        if canon not in seen: seen.add(canon); unique.append(w)
    return unique

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

def build_cycle(ms, n, word, combo):
    ell = len(word); fc = [0]*n
    configs = []; state = [combo[p][0] for p in range(n)]
    for s in range(ell):
        configs.append(tuple(state))
        p = word[s]; fc[p] += 1; state[p] = combo[p][fc[p]]
    if tuple(state) != configs[0]: return None
    if len(set(configs)) != ell: return None
    return configs

n = 9
ms = [2,3,3,2,3,3,2,3,3]
CL = sum(ms)

words = enumerate_sweep_words(ms, n)
all_combos = {p: enumerate_state_sequences(ms[p], ms[p]) for p in range(n)}

# Analyze ALL instances
total = 0
case_a_count = 0  # (L,x,R) not in forced table → no forced privilege at i
case_b_maps_elsewhere = 0  # forced entry exists but maps to != g_k[i]
case_b_maps_to_gk_good = 0  # forced maps to g_k[i] but c is good
case_b_maps_to_gk_bad = 0  # VIOLATION: forced maps to g_k[i] and c is non-good

# Also check: for binary procs, is the argument simpler?
binary_cases = 0; ternary_cases = 0; binary_resolved = 0; ternary_resolved = 0

for wi, w in enumerate(words):
    combo_lists = [all_combos[p] for p in range(n)]
    for combo_idx in itertools.product(*[range(len(c)) for c in combo_lists]):
        combo_t = tuple(combo_lists[p][combo_idx[p]] for p in range(n))
        cfgs = build_cycle(ms, n, w, combo_t)
        if cfgs is None: continue
        total += 1

        gs = set(cfgs)
        ell = len(cfgs)

        # Build forced entries
        fe = {}
        for s in range(ell):
            p = w[s]; c = cfgs[s]
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]; Sp = cfgs[(s+1)%ell][p]
            if p not in fe: fe[p] = {}
            fe[p][(L,S,R)] = Sp
            for q in range(n):
                if q == p: continue
                Lq = c[(q-1)%n]; Sq = c[q]; Rq = c[(q+1)%n]
                if q not in fe: fe[q] = {}
                fe[q][(Lq,Sq,Rq)] = Sq

        # For each (g_k, position i, value x != g_k[i]):
        for ki in range(ell):
            gk = cfgs[ki]
            for i in range(n):
                L = gk[(i-1)%n]; R = gk[(i+1)%n]
                for x in range(ms[i]):
                    if x == gk[i]: continue

                    c = list(gk); c[i] = x; c = tuple(c)

                    # Is (L, x, R) in forced table for proc i?
                    if i not in fe or (L,x,R) not in fe[i]:
                        case_a_count += 1  # Not forced → can't use this entry
                        continue

                    target = fe[i][(L,x,R)]

                    if target == x:
                        # Non-privileged: f_i = S. No move happens.
                        case_a_count += 1
                        continue

                    if target != gk[i]:
                        # Privileged but maps to something else, not g_k[i]
                        case_b_maps_elsewhere += 1
                    else:
                        # target == gk[i]: move(c,i) = gk!
                        if c in gs:
                            case_b_maps_to_gk_good += 1
                        else:
                            case_b_maps_to_gk_bad += 1
                            print(f"VIOLATION: inst={total}, g[{ki}], i={i}, x={x}")

                    # Track binary vs ternary
                    if ms[i] == 2:
                        binary_cases += 1
                        if target != gk[i] or c in gs:
                            binary_resolved += 1
                    else:
                        ternary_cases += 1
                        if target != gk[i] or c in gs:
                            ternary_resolved += 1

print(f"Total instances: {total}")
print(f"\nCase analysis for all (g_k, i, x) triples:")
print(f"  Case A (not forced / non-privileged): {case_a_count}")
print(f"  Case B.1 (forced, maps elsewhere):    {case_b_maps_elsewhere}")
print(f"  Case B.2 (forced, maps to g_k[i], c good): {case_b_maps_to_gk_good}")
print(f"  Case B.3 (VIOLATION):                  {case_b_maps_to_gk_bad}")
print(f"\nBinary position cases: {binary_cases} ({binary_resolved} resolved)")
print(f"Ternary position cases: {ternary_cases} ({ternary_resolved} resolved)")
print(f"\n{'CLAIM 2 VERIFIED' if case_b_maps_to_gk_bad == 0 else 'CLAIM 2 FAILS'}")

# Detailed breakdown: which resolution mechanism?
print(f"\n--- Resolution mechanism breakdown ---")
print(f"Total dangerous triples (forced, privileged): {case_b_maps_elsewhere + case_b_maps_to_gk_good + case_b_maps_to_gk_bad}")
print(f"  Resolved by 'maps elsewhere': {case_b_maps_elsewhere} ({100*case_b_maps_elsewhere/max(1,case_b_maps_elsewhere+case_b_maps_to_gk_good+case_b_maps_to_gk_bad):.1f}%)")
print(f"  Resolved by 'c is good':      {case_b_maps_to_gk_good} ({100*case_b_maps_to_gk_good/max(1,case_b_maps_elsewhere+case_b_maps_to_gk_good+case_b_maps_to_gk_bad):.1f}%)")

# Check: in the "c is good" cases, is c always g_{k-1}?
print(f"\n--- 'c is good' identification ---")
c_is_prev = 0; c_is_next = 0; c_is_other = 0
for wi, w in enumerate(words[:1]):  # just first word
    combo_lists = [all_combos[p] for p in range(n)]
    for combo_idx in itertools.product(*[range(len(c)) for c in combo_lists]):
        combo_t = tuple(combo_lists[p][combo_idx[p]] for p in range(n))
        cfgs = build_cycle(ms, n, w, combo_t)
        if cfgs is None: continue

        gs = set(cfgs)
        ell = len(cfgs)
        cfg_to_idx = {cfgs[k]: k for k in range(ell)}

        fe2 = {}
        for s in range(ell):
            p2 = w[s]; c2 = cfgs[s]
            L2 = c2[(p2-1)%n]; S2 = c2[p2]; R2 = c2[(p2+1)%n]; Sp2 = cfgs[(s+1)%ell][p2]
            if p2 not in fe2: fe2[p2] = {}
            fe2[p2][(L2,S2,R2)] = Sp2
            for q2 in range(n):
                if q2 == p2: continue
                Lq2 = c2[(q2-1)%n]; Sq2 = c2[q2]; Rq2 = c2[(q2+1)%n]
                if q2 not in fe2: fe2[q2] = {}
                fe2[q2][(Lq2,Sq2,Rq2)] = Sq2

        for ki in range(ell):
            gk = cfgs[ki]
            for i in range(n):
                L = gk[(i-1)%n]; R = gk[(i+1)%n]
                for x in range(ms[i]):
                    if x == gk[i]: continue
                    if i not in fe2 or (L,x,R) not in fe2[i]: continue
                    tgt = fe2[i][(L,x,R)]
                    if tgt == x or tgt != gk[i]: continue
                    # tgt == gk[i] and tgt != x: potential violation
                    c = list(gk); c[i] = x; c = tuple(c)
                    if c in gs:
                        ci = cfg_to_idx[c]
                        if ci == (ki-1) % ell:
                            c_is_prev += 1
                        elif ci == (ki+1) % ell:
                            c_is_next += 1
                        else:
                            c_is_other += 1
                            print(f"  OTHER: g[{ki}] i={i} x={x} -> c=g[{ci}]")
        break
    break

print(f"  c = g_{{k-1}}: {c_is_prev}")
print(f"  c = g_{{k+1}}: {c_is_next}")
print(f"  c = g_other: {c_is_other}")

print("\nDONE")
