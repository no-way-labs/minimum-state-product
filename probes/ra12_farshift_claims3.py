#!/usr/bin/env python3
"""ra12_farshift_claims3.py — Proof mechanism analysis for Claim 2.

The key question: WHY does forced non-good closure hold?
Two candidate mechanisms:
(A) H-1 uniqueness: every good config has exactly 2 H-1 good neighbors (prev/next)
(B) Preimage uniqueness: for each forced mover entry f_p(L,S,R)=T at a good config,
    the only value x with f_p(L,x,R)=T is x=S (the good config's value).

If (B) holds, then move(c,p)=g_k implies c[p] has the same value as g_k[p] pre-move,
meaning c[p] = g_{k-1}[p] (if mover at step k-1 is p), which would make c = g_{k-1}.

Actually wait: let me re-examine. If move(c,i)=g_k where c is non-good:
- c agrees with g_k at all j != i
- c[i] != g_k[i] (since i is privileged at c: f_i(L,c[i],R) = g_k[i] != c[i])
- So c is Hamming-1 from g_k at position i

If the only good configs at Hamming-1 from g_k are g_{k-1} and g_{k+1},
and c is non-good, then c is NOT one of them. But we need more:
does the FORCED entry at position i map c[i] to g_k[i]?

For this to happen, the forced entry must have f_i(L, c[i], R) = g_k[i],
where L = g_k[i-1], R = g_k[i+1] (since c agrees with g_k at all j != i).

The question: is (L, c[i], R) even in the forced entry table?
If it IS forced, does it map to g_k[i]?

Let's check all this carefully.
"""

import sys, os, itertools
sys.path.insert(0, os.path.dirname(__file__))

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
                    disp = compute_displacement(word, n)
                    if abs(disp) == 2*n:
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

def extract_forced_entries(ms, n, word, configs):
    ell = len(word); entries = {}
    for s in range(ell):
        p = word[s]; c = configs[s]
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]; Sp = configs[(s+1)%ell][p]
        if p not in entries: entries[p] = {}
        entries[p][(L,S,R)] = Sp
        for q in range(n):
            if q == p: continue
            Lq = c[(q-1)%n]; Sq = c[q]; Rq = c[(q+1)%n]
            if q not in entries: entries[q] = {}
            entries[q][(Lq,Sq,Rq)] = Sq
    return entries

# ================================================================
# Analysis
# ================================================================

n = 9
ms = [2,3,3,2,3,3,2,3,3]
CL = sum(ms)

words = enumerate_sweep_words(ms, n)
all_combos = {p: enumerate_state_sequences(ms[p], ms[p]) for p in range(n)}

# Analyze first instance in detail
for wi, w in enumerate(words):
    combo_lists = [all_combos[p] for p in range(n)]
    for combo_idx in itertools.product(*[range(len(c)) for c in combo_lists]):
        combo_t = tuple(combo_lists[p][combo_idx[p]] for p in range(n))
        cfgs = build_cycle(ms, n, w, combo_t)
        if cfgs is None: continue

        gs = set(cfgs)
        fe = extract_forced_entries(ms, n, w, cfgs)
        ell = len(cfgs)

        print(f"Instance: word {wi}, combo {combo_idx}")
        print(f"Cycle length: {ell}")
        print(f"Word: {w}")
        print()

        # ========================================
        # Analysis A: For each good g_k and each position i:
        # What configs c differ from g_k only at position i,
        # and have a forced mover entry at i that maps to g_k[i]?
        # ========================================
        print("=== Analysis A: non-good H-1 preimages via forced entries ===")

        preimage_cases = 0
        for ki in range(ell):
            gk = cfgs[ki]
            for i in range(n):
                L = gk[(i-1)%n]; R = gk[(i+1)%n]
                for x in range(ms[i]):
                    if x == gk[i]: continue
                    # Config c = gk except c[i] = x
                    c = list(gk); c[i] = x; c = tuple(c)

                    # Is (L, x, R) a forced mover entry for proc i?
                    if i in fe and (L,x,R) in fe[i]:
                        target = fe[i][(L,x,R)]
                        if target != x:  # i is forced-privileged at c
                            if target == gk[i]:  # maps to good!
                                # This would be a claim 2 violation
                                preimage_cases += 1
                                if preimage_cases <= 5:
                                    is_good = c in gs
                                    print(f"  g[{ki}], i={i}, x={x}: fe[{i}]({L},{x},{R})={target}=gk[{i}]")
                                    print(f"    c={c}, c in good: {is_good}")
                            # else: forced entry maps to something != gk[i], so move(c,i) != gk

        print(f"Total preimage-to-good cases: {preimage_cases}")

        # ========================================
        # Analysis B: Why does the H-1 uniqueness hold?
        # For each good g_k: what makes it have exactly 2 H-1 good neighbors?
        # ========================================
        print("\n=== Analysis B: H-1 neighbor structure ===")

        # For each step k, mover is w[k]. g_k -> g_{k+1} changes position w[k].
        # So g_k and g_{k+1} differ at position w[k] (H-1 neighbors).
        # Also g_{k-1} and g_k differ at position w[k-1].
        # So g_k's H-1 good neighbors include g_{k-1} (diff at w[k-1]) and g_{k+1} (diff at w[k]).
        # Question: can g_j (j != k-1, k+1) also be H-1 from g_k?

        for ki in range(min(5, ell)):
            gk = cfgs[ki]
            prev_pos = w[(ki-1)%ell]
            next_pos = w[ki]
            h1 = []
            for kj in range(ell):
                if kj == ki: continue
                diffs = [p for p in range(n) if gk[p] != cfgs[kj][p]]
                if len(diffs) == 1:
                    h1.append((kj, diffs[0]))
            print(f"  g[{ki}]: mover_prev=w[{(ki-1)%ell}]={prev_pos}, mover_next=w[{ki}]={next_pos}")
            print(f"    H-1 neighbors: {h1}")
            # Each should be (ki-1, prev_pos) and (ki+1, next_pos)

        # ========================================
        # Analysis C: The actual Claim 2 proof mechanism
        # ========================================
        print("\n=== Analysis C: Claim 2 proof mechanism ===")
        print("For move(c,i) = g_k where c non-good:")
        print("  - c agrees with g_k at all j != i")
        print("  - c[i] != g_k[i]")
        print("  - So c is H-1 from g_k at position i")
        print()

        # For each good config g_k, for each mover position i:
        # Is there any value x != g_k[i] such that:
        #   1. The config c = (g_k with c[i]=x) is non-good
        #   2. i is privileged at c (in the forced entries)
        #   3. The forced entry maps c[i] -> g_k[i]
        # If no such x exists for ANY (g_k, i), then Claim 2 holds.

        # Check WHY no such x exists:
        print("Checking for each (g_k, i, x):")
        for ki in range(ell):
            gk = cfgs[ki]
            for i in range(n):
                L = gk[(i-1)%n]; R = gk[(i+1)%n]
                for x in range(ms[i]):
                    if x == gk[i]: continue
                    c = list(gk); c[i] = x; c = tuple(c)
                    if c in gs:
                        continue  # c is good, not relevant

                    # Is (L, x, R) forced?
                    forced = i in fe and (L,x,R) in fe[i]
                    if forced:
                        target = fe[i][(L,x,R)]
                        if target == gk[i]:
                            print(f"  VIOLATION: g[{ki}] i={i} x={x}: forced({L},{x},{R})={target}=gk[i]!")
                        elif target != x:
                            pass  # privileged but maps elsewhere (not to g_k)
                        # else: target == x, not privileged
                    else:
                        pass  # (L,x,R) is a free entry — not determined by the cycle

        # ========================================
        # Analysis D: Why forced entries don't map to good
        # ========================================
        print("\n=== Analysis D: Why no violation exists ===")
        # For position i at good config g_k:
        # The forced entry at (L, g_k[i], R) maps to g_k[i] (non-mover) or to
        # g_{k+1}[i] (mover). Let's categorize:
        #
        # Mover case: w[k] = i (proc i fires at step k)
        #   Forced: f_i(L, g_k[i], R) = g_{k+1}[i] != g_k[i]
        #   Context: (L, S, R) = (g_k[i-1], g_k[i], g_k[i+1])
        #
        # Non-mover case: w[k] != i
        #   Forced: f_i(L, g_k[i], R) = g_k[i] (identity)
        #   This creates an "identity" forced entry.
        #
        # For violation: we need (L, x, R) forced to g_k[i] where x != g_k[i].
        # The mover entry forces (L, g_k[i], R) -> g_{k+1}[i] (not to g_k[i]).
        # The non-mover entries force (L, g_k[i], R) -> g_k[i] (maps S to S).
        # So forced entries at context (L, *, R) where L=g_k[i-1], R=g_k[i+1]:
        # Only (L, g_k[i], R) is forced. (L, x, R) for x != g_k[i] might NOT be forced.
        #
        # But wait: (L, x, R) could be forced from a DIFFERENT good config!
        # If some other good config g_j has g_j[i-1]=L, g_j[i]=x, g_j[i+1]=R,
        # then it creates a forced entry at (L, x, R) for proc i.

        print("Context analysis for position i at each good config:")
        context_map = {}  # (i, L, R) -> list of (ki, S, target)
        for ki in range(ell):
            gk = cfgs[ki]
            for i in range(n):
                L = gk[(i-1)%n]; S = gk[i]; R = gk[(i+1)%n]
                key = (i, L, R)
                if key not in context_map:
                    context_map[key] = []
                if w[ki] == i:
                    target = cfgs[(ki+1)%ell][i]
                else:
                    target = S
                context_map[key].append((ki, S, target))

        # Check: for each (i,L,R), are there multiple S values?
        multi_S = 0
        for key, entries in context_map.items():
            S_vals = set(e[1] for e in entries)
            if len(S_vals) > 1:
                multi_S += 1
                if multi_S <= 5:
                    i, L, R = key
                    print(f"  (i={i}, L={L}, R={R}): multiple S values in good cycle")
                    for ki, S, tgt in entries:
                        print(f"    g[{ki}]: S={S}, target={tgt}, mover={w[ki]==i}")

        print(f"\nContexts with multiple S values: {multi_S}")
        if multi_S > 0:
            print("Multiple S at same (i,L,R) means forced entries for different S values at proc i.")
            print("For violation: need forced (L,x,R)->gk[i] where x != gk[i] and (L,x,R) comes from another good config.")
            # Check: does any such cross-reference map to gk[i]?
            cross_violations = 0
            for key, entries in context_map.items():
                i, L, R = key
                for ki1, S1, tgt1 in entries:
                    for ki2, S2, tgt2 in entries:
                        if S1 == S2: continue
                        # Entry from g[ki2]: f_i(L, S2, R) = tgt2
                        # If tgt2 == S1 and S2 != S1: this means non-good config
                        # (gk1 with i set to S2) would map to S1 = gk1[i] when i fires.
                        # But we also need S2 != tgt2 (i must be privileged).
                        if tgt2 != S2 and tgt2 == S1:
                            cross_violations += 1
                            print(f"  CROSS-VIOLATION: g[{ki1}] i={i}: context ({L},{S2},{R}) forced to {tgt2}={S1}")
                            # But is (gk1 with i=S2) non-good?
                            gk1 = cfgs[ki1]
                            c = list(gk1); c[i] = S2; c = tuple(c)
                            print(f"    c={c}, c in good: {c in gs}")

            print(f"Cross-violations: {cross_violations}")
        break
    break

print("\nDONE")
