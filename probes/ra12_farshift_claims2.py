#!/usr/bin/env python3
"""ra12_farshift_claims2.py — Extended verification with orbit failure diagnosis."""

import sys, os, time, itertools
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
        # Mover entry
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]; Sp = configs[(s+1)%ell][p]
        if p not in entries: entries[p] = {}
        entries[p][(L,S,R)] = Sp
        # Non-mover entries
        for q in range(n):
            if q == p: continue
            Lq = c[(q-1)%n]; Sq = c[q]; Rq = c[(q+1)%n]
            if q not in entries: entries[q] = {}
            entries[q][(Lq,Sq,Rq)] = Sq
    return entries

def forced_step(n, c, fe):
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        if p in fe and (L,S,R) in fe[p] and fe[p][(L,S,R)] != S:
            nxt = list(c); nxt[p] = fe[p][(L,S,R)]
            return tuple(nxt), p
    return None, None

def has_any_forced(n, c, fe):
    """Check if c has ANY forced entry (privileged or not)."""
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        if p in fe and (L,S,R) in fe[p]:
            return True
    return False

def count_forced_coverage(n, c, fe, ms):
    """Count how many procs have forced entries vs free entries."""
    forced = 0; free = 0
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        if p in fe and (L,S,R) in fe[p]:
            forced += 1
        else:
            free += 1
    return forced, free

# ================================================================
# Main
# ================================================================

n = 9
ms = [2,3,3,2,3,3,2,3,3]
CL = sum(ms)

print(f"n={n}, ms={ms}, CL={CL}, product={eval('*'.join(str(m) for m in ms))}")

words = enumerate_sweep_words(ms, n)
all_combos = {p: enumerate_state_sequences(ms[p], ms[p]) for p in range(n)}
print(f"{len(words)} sweep words")

total = 0; orbit_ok = 0; orbit_stuck = 0; orbit_short = 0
stuck_reasons = []

for wi, w in enumerate(words):
    combo_lists = [all_combos[p] for p in range(n)]
    for combo_idx in itertools.product(*[range(len(c)) for c in combo_lists]):
        combo_t = tuple(combo_lists[p][combo_idx[p]] for p in range(n))
        cfgs = build_cycle(ms, n, w, combo_t)
        if cfgs is None: continue
        total += 1

        gs = set(cfgs)
        fe = extract_forced_entries(ms, n, w, cfgs)

        # Try ALL possible starting configs (shifted good configs)
        best_cycle_len = 0
        best_shadow = None
        found_any = False

        for q in range(n):
            for d in range(1, ms[q]):
                c0 = list(cfgs[0]); c0[q] = (c0[q]+d)%ms[q]; c0 = tuple(c0)
                if c0 in gs: continue

                nxt, p = forced_step(n, c0, fe)
                if nxt is None: continue
                found_any = True

                # Follow orbit
                orbit = [c0]; oset = {c0}; cur = c0
                ok = True
                for step in range(CL * 3):
                    nxt, p = forced_step(n, cur, fe)
                    if nxt is None:
                        ok = False
                        if total <= 5 and len(stuck_reasons) < 3:
                            f, fr = count_forced_coverage(n, cur, fe, ms)
                            stuck_reasons.append((total, len(orbit), f, fr, cur))
                        break
                    if nxt in gs:
                        ok = False; break
                    if nxt in oset:
                        ci = orbit.index(nxt)
                        shadow = orbit[ci:]
                        if len(shadow) > best_cycle_len:
                            best_cycle_len = len(shadow)
                            best_shadow = shadow
                        ok = True; break
                    orbit.append(nxt); oset.add(nxt); cur = nxt

        if best_shadow and best_cycle_len == CL:
            orbit_ok += 1
        elif best_shadow:
            orbit_short += 1
        elif found_any:
            orbit_stuck += 1
        else:
            orbit_stuck += 1

print(f"\nTotal: {total}")
print(f"  Full CL-cycle found: {orbit_ok}")
print(f"  Shorter cycle found: {orbit_short}")
print(f"  No cycle (stuck/no start): {orbit_stuck}")

if stuck_reasons:
    print(f"\nStuck orbit details:")
    for inst, olen, f, fr, c in stuck_reasons[:5]:
        print(f"  Instance {inst}: orbit len={olen}, forced={f}, free={fr}")
        print(f"    Stuck at: {c}")

# ================================================================
# COMPREHENSIVE CLAIM 2 CHECK: enumerate ALL non-good configs
# ================================================================
print(f"\n{'='*70}")
print("Comprehensive Claim 2: enumerate ALL configs for first instance")
print(f"{'='*70}")

for wi, w in enumerate(words):
    combo_lists = [all_combos[p] for p in range(n)]
    for combo_idx in itertools.product(*[range(len(c)) for c in combo_lists]):
        combo_t = tuple(combo_lists[p][combo_idx[p]] for p in range(n))
        cfgs = build_cycle(ms, n, w, combo_t)
        if cfgs is None: continue

        gs = set(cfgs)
        fe = extract_forced_entries(ms, n, w, cfgs)

        # Enumerate ALL configs
        from itertools import product as cartesian
        all_cfgs = list(cartesian(*(range(m) for m in ms)))
        non_good = [c for c in all_cfgs if c not in gs]
        print(f"Total configs: {len(all_cfgs)}, non-good: {len(non_good)}")

        c2_viol = 0
        forced_priv_count = 0
        no_forced_count = 0
        forced_nonpriv_count = 0

        for c in non_good:
            nxt, p = forced_step(n, c, fe)
            if nxt is not None:
                forced_priv_count += 1
                if nxt in gs:
                    c2_viol += 1
                    if c2_viol <= 3:
                        print(f"  VIOL: c={c}, fire p={p} -> {nxt}")
            else:
                # Check if c has any forced entries at all
                if has_any_forced(n, c, fe):
                    forced_nonpriv_count += 1
                else:
                    no_forced_count += 1

        print(f"Non-good with forced privilege: {forced_priv_count}")
        print(f"Non-good with forced non-priv only: {forced_nonpriv_count}")
        print(f"Non-good with NO forced entries: {no_forced_count}")
        print(f"Claim 2 violations: {c2_viol}")

        # Check: among forced-priv configs, do they form cycles?
        # Build forced-priv graph
        graph = {}
        for c in non_good:
            nxt, p = forced_step(n, c, fe)
            if nxt is not None and nxt not in gs:
                graph[c] = nxt

        # Find cycles in this graph
        visited = set(); cycles_found = []
        for c in graph:
            if c in visited: continue
            path = []; pset = set(); cur = c
            while cur not in visited and cur not in pset and cur in graph:
                path.append(cur); pset.add(cur); cur = graph[cur]
            if cur in pset:
                ci = path.index(cur)
                cyc = path[ci:]
                cycles_found.append(len(cyc))
            visited.update(path)

        print(f"Non-good forced cycles found: {len(cycles_found)}, lengths: {sorted(set(cycles_found))}")
        break
    break

print("\nDONE")
