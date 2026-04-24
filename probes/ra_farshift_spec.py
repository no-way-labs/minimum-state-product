#!/usr/bin/env python3
"""
RA: Complete specification of the FarShift BadCycleData construction.

Systematically investigate the bad cycle construction for stuttered sweeps
at n=9, ms=[2,3,3,2,3,3,2,3,3], answering all 6 parts.

Key question: The current Lean code uses mover := gc.moverAt k (same movers).
Previous RA says movers are DIFFERENT. Who is right?
"""

import itertools
from collections import defaultdict

# ============================================================
# Core utilities
# ============================================================

def enumerate_exact_fc_words(ms, n, target_fc):
    """Enumerate mover words with exact fire counts."""
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
    """Build good cycle from mover word and state sequences (combo)."""
    ell = len(word)
    # combo[p] = sequence of values proc p takes: combo[p][0]=0, ..., combo[p][ms[p]]=0
    # fire_count tracks how many times each proc has fired
    fc = [0]*n
    configs = []
    state = list(combo[p][0] for p in range(n))  # all start at combo[p][0] = 0
    for s in range(ell):
        configs.append(tuple(state))
        p = word[s]
        fc[p] += 1
        state[p] = combo[p][fc[p]]
    # Check cycle closes
    if tuple(state) != configs[0]:
        return None
    if len(set(configs)) != ell:
        return None
    return configs

def enumerate_state_sequences(m, k):
    """All length-(k+1) sequences starting and ending at 0, all transitions change value."""
    seqs = []
    def dfs(seq, remaining):
        if remaining == 0:
            if seq[-1] == 0:
                seqs.append(tuple(seq))
            return
        for nv in range(m):
            if nv != seq[-1]:
                if remaining == 1 and nv != 0:
                    continue
                seq.append(nv)
                dfs(seq, remaining - 1)
                seq.pop()
    dfs([0], k)
    return seqs

def compute_displacement(word, n):
    total = 0
    ell = len(word)
    for i in range(ell):
        diff = (word[(i+1) % ell] - word[i]) % n
        if diff == 1: total += 1
        elif diff == n-1: total -= 1
    return total

def extract_forced_entries(ms, n, word, configs):
    """Extract the forced transition entries from a good cycle."""
    ell = len(word)
    entries = {}  # entries[p][(L,S,R)] = S'
    for s in range(ell):
        p = word[s]
        c = configs[s]
        L = c[(p-1) % n]
        S = c[p]
        R = c[(p+1) % n]
        c_next = configs[(s+1) % ell]
        Sp = c_next[p]
        if p not in entries:
            entries[p] = {}
        key = (L, S, R)
        if key in entries[p]:
            assert entries[p][key] == Sp, f"Conflict at P{p}, ctx={key}"
        entries[p][key] = Sp
    return entries

def follow_forced_orbit(ms, n, c0, forced, good_set, max_steps=200):
    """
    Starting from c0, follow forced transitions.
    At each step: find ALL procs whose context matches a forced entry AND
    the forced output differs from current value (i.e., proc is privileged).
    If exactly 1 such proc, fire it. Otherwise report ambiguity.
    Returns: (path, movers, status)
    """
    path = [c0]
    movers = []
    cur = c0
    for step in range(max_steps):
        privileged = []
        for p in range(n):
            L = cur[(p-1) % n]
            S = cur[p]
            R = cur[(p+1) % n]
            if p in forced and (L, S, R) in forced[p]:
                Sp = forced[p][(L, S, R)]
                if Sp != S:
                    privileged.append((p, Sp))
        if len(privileged) == 0:
            return path, movers, "STUCK"
        if len(privileged) > 1:
            # Multiple privileged procs — try each to see which leads to cycle
            # For now, just pick the first (we'll verify uniqueness separately)
            pass
        p, Sp = privileged[0]
        movers.append(p)
        nxt = list(cur)
        nxt[p] = Sp
        nxt = tuple(nxt)
        if nxt == c0:
            return path, movers, "CYCLE"
        if nxt in set(path):
            return path, movers, "SUBCYCLE"
        path.append(nxt)
        cur = nxt
    return path, movers, "TIMEOUT"

# ============================================================
# Setup: n=9, ms=[2,3,3,2,3,3,2,3,3]
# ============================================================

n = 9
ms = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = sum(ms)  # cycle length = 24

print(f"n={n}, ms={ms}, CL={CL}")
print(f"Binary procs: {[p for p in range(n) if ms[p]==2]}")
print(f"Ternary procs: {[p for p in range(n) if ms[p]==3]}")

# Enumerate mover words (sweep = displacement ±2n)
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
print(f"Sweep words: {len(valid_words)}")

# Enumerate state sequences (combos)
all_combos_by_proc = {}
for p in range(n):
    all_combos_by_proc[p] = enumerate_state_sequences(ms[p], ms[p])
print(f"Combos per proc: {[len(all_combos_by_proc[p]) for p in range(n)]}")
# Binary: 1 combo each (0,1,0). Ternary: 2 combos each (0,1,2,0) and (0,2,1,0).

# Take first word and first combo for detailed analysis
word = valid_words[0]
disp = compute_displacement(word, n)
direction = "CCW" if disp > 0 else "CW"
print(f"\nWord: {word}")
print(f"Displacement: {disp} ({direction})")

combo = tuple(all_combos_by_proc[p][0] for p in range(n))
configs = build_cycle_with_combo(ms, n, word, combo)
assert configs is not None
good_set = set(configs)
forced = extract_forced_entries(ms, n, word, configs)

print(f"\n{'='*72}")
print("PART 1: Good cycle detail")
print(f"{'='*72}")
for s in range(CL):
    p = word[s]
    c = configs[s]
    L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
    c_next = configs[(s+1)%CL]
    Sp = c_next[p]
    print(f"  [{s:2d}] mover=P{p}  cfg={c}  ctx=({L},{S},{R})->{Sp}")

# ============================================================
# PART 1: Which proc q to shift?
# ============================================================
print(f"\n{'='*72}")
print("PART 1: Finding q (proc to shift)")
print(f"{'='*72}")

# Test: for each proc q, for each shift amount d, try to follow forced orbit
for q in range(n):
    for d in range(1, ms[q]):
        c0 = list(configs[0])
        c0[q] = (c0[q] + d) % ms[q]
        c0 = tuple(c0)
        if c0 in good_set:
            continue
        path, movers, status = follow_forced_orbit(ms, n, c0, forced, good_set)
        if status == "CYCLE" and len(path) == CL:
            # Check disjoint from good
            bad_set = set(path)
            disjoint = bad_set.isdisjoint(good_set)
            print(f"  q=P{q}, d={d}: CYCLE of length {len(path)}, disjoint={disjoint}")

# ============================================================
# PART 2: Detailed bad cycle for the first working (q, d)
# ============================================================
print(f"\n{'='*72}")
print("PART 2: Detailed bad cycle construction")
print(f"{'='*72}")

# Find first working q,d
best_q, best_d = None, None
for q in range(n):
    for d in range(1, ms[q]):
        c0 = list(configs[0])
        c0[q] = (c0[q] + d) % ms[q]
        c0 = tuple(c0)
        if c0 in good_set:
            continue
        path, movers, status = follow_forced_orbit(ms, n, c0, forced, good_set)
        if status == "CYCLE" and len(path) == CL:
            bad_set = set(path)
            if bad_set.isdisjoint(good_set):
                best_q, best_d = q, d
                break
    if best_q is not None:
        break

print(f"Using q=P{best_q}, d={best_d}")

c0 = list(configs[0])
c0[best_q] = (c0[best_q] + best_d) % ms[best_q]
c0 = tuple(c0)

# Now follow with FULL detail, checking uniqueness of privilege
path = [c0]
movers_list = []
privilege_counts = []
cur = c0
for step in range(CL):
    privileged = []
    for p in range(n):
        L = cur[(p-1) % n]; S = cur[p]; R = cur[(p+1) % n]
        if p in forced and (L, S, R) in forced[p]:
            Sp = forced[p][(L, S, R)]
            if Sp != S:
                privileged.append((p, Sp))
    privilege_counts.append(len(privileged))
    if len(privileged) == 0:
        print(f"  [{step}] STUCK!")
        break
    p, Sp = privileged[0]
    movers_list.append(p)
    nxt = list(cur)
    nxt[p] = Sp
    cur = tuple(nxt)
    if step < CL - 1:
        path.append(cur)

bad_configs = path
bad_movers = movers_list

print(f"\nBad cycle (len={len(bad_configs)}):")
for s in range(len(bad_configs)):
    p = bad_movers[s]
    c = bad_configs[s]
    L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
    Sp = forced[p][(L, S, R)]
    gc_mover = word[s]
    same_mover = "SAME" if p == gc_mover else "DIFF"
    print(f"  [{s:2d}] mover=P{p} ({same_mover}, gc=P{gc_mover})  cfg={c}  ctx=({L},{S},{R})->{Sp}  #priv={privilege_counts[s]}")

# ============================================================
# PART 2b: Are movers same or different?
# ============================================================
print(f"\n{'='*72}")
print("PART 2b: Mover comparison (good vs bad)")
print(f"{'='*72}")
same_count = sum(1 for s in range(CL) if bad_movers[s] == word[s])
print(f"Same mover at {same_count}/{CL} steps")
print(f"Good movers: {list(word)}")
print(f"Bad movers:  {bad_movers}")

# ============================================================
# PART 3: Closed-form check — is bad_cfg[k] = shift(good_cfg[σ(k)], q, d)?
# ============================================================
print(f"\n{'='*72}")
print("PART 3: Permutation structure")
print(f"{'='*72}")

# For each bad config, find which good config it's closest to
for s in range(CL):
    bc = bad_configs[s]
    for g in range(CL):
        gc_c = configs[g]
        diff = tuple((bc[i] - gc_c[i]) % ms[i] for i in range(n))
        n_diff = sum(1 for i in range(n) if diff[i] != 0)
        if n_diff <= 2:
            print(f"  bad[{s:2d}] ~ good[{g:2d}]: diff at {[i for i in range(n) if diff[i]!=0]} vals={[diff[i] for i in range(n) if diff[i]!=0]}")
            break

# Check: is it a CONSTANT shift at q?
print(f"\n  Constant shift check (q=P{best_q}, d={best_d}):")
sigma = []
for s in range(CL):
    bc = bad_configs[s]
    found = None
    for g in range(CL):
        gc_c = configs[g]
        # Check: bc = gc_c with position best_q shifted by best_d
        match = True
        for i in range(n):
            if i == best_q:
                if (gc_c[i] + best_d) % ms[i] != bc[i]:
                    match = False
                    break
            else:
                if gc_c[i] != bc[i]:
                    match = False
                    break
        if match:
            found = g
            break
    sigma.append(found)
    if found is not None:
        print(f"  bad[{s:2d}] = shift(good[{found:2d}], P{best_q}, +{best_d})")
    else:
        print(f"  bad[{s:2d}] = NO MATCH (not a constant shift of any good config)")

# ============================================================
# PART 4: Unique privilege check
# ============================================================
print(f"\n{'='*72}")
print("PART 4: Unique privilege at each bad config")
print(f"{'='*72}")

all_unique = True
for s in range(CL):
    c = bad_configs[s]
    privileged = []
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        if p in forced and (L,S,R) in forced[p]:
            Sp = forced[p][(L,S,R)]
            if Sp != S:
                privileged.append(p)
    if len(privileged) != 1:
        all_unique = False
        print(f"  [{s:2d}] privilege count = {len(privileged)}: {privileged}")
print(f"All unique: {all_unique}")

# ============================================================
# PART 5: Disjointness check
# ============================================================
print(f"\n{'='*72}")
print("PART 5: Disjointness (every bad config not in good set)")
print(f"{'='*72}")

all_disjoint = all(bc not in good_set for bc in bad_configs)
print(f"All disjoint: {all_disjoint}")
for s in range(CL):
    bc = bad_configs[s]
    if bc in good_set:
        idx = configs.index(bc)
        print(f"  BAD! bad[{s}] = good[{idx}]")

# ============================================================
# PART 5b: WHY disjoint? At each step, which procs differ from all good configs?
# ============================================================
print(f"\nDiagnostic: at which positions does bad differ from good?")
for s in range(CL):
    bc = bad_configs[s]
    # For the matched good config sigma[s]:
    if sigma[s] is not None:
        g = sigma[s]
        print(f"  bad[{s:2d}]: differs from good[{g:2d}] only at P{best_q} (shift +{best_d})")
    else:
        # Find closest good config
        best_dist = n+1
        best_g = -1
        for g in range(CL):
            gc_c = configs[g]
            dist = sum(1 for i in range(n) if gc_c[i] != bc[i])
            if dist < best_dist:
                best_dist = dist
                best_g = g
        diffs = [i for i in range(n) if configs[best_g][i] != bc[i]]
        print(f"  bad[{s:2d}]: closest good[{best_g}], differs at {diffs}")

# ============================================================
# UNIVERSAL TEST: All sweeps × all combos
# ============================================================
print(f"\n{'='*72}")
print("UNIVERSAL TEST: All sweeps × all combos")
print(f"{'='*72}")

total_tests = 0
total_pass = 0
mover_same_count = 0
mover_diff_count = 0
unique_q_d_pairs = set()

for wi, w in enumerate(valid_words):
    disp = compute_displacement(w, n)
    # Generate all combos
    combo_lists = [all_combos_by_proc[p] for p in range(n)]
    for combo_idx in itertools.product(*[range(len(c)) for c in combo_lists]):
        combo = tuple(combo_lists[p][combo_idx[p]] for p in range(n))
        cfgs = build_cycle_with_combo(ms, n, w, combo)
        if cfgs is None:
            continue
        gs = set(cfgs)
        fe = extract_forced_entries(ms, n, w, cfgs)

        total_tests += 1

        # Try all q, d
        found = False
        for q in range(n):
            for d in range(1, ms[q]):
                c0 = list(cfgs[0])
                c0[q] = (c0[q] + d) % ms[q]
                c0 = tuple(c0)
                if c0 in gs:
                    continue
                path, movers, status = follow_forced_orbit(ms, n, c0, fe, gs)
                if status == "CYCLE" and len(path) == CL:
                    bad_set = set(path)
                    if bad_set.isdisjoint(gs):
                        # Check if movers match good cycle
                        movers_same = all(movers[s] == w[s] for s in range(CL))
                        if movers_same:
                            mover_same_count += 1
                        else:
                            mover_diff_count += 1
                        unique_q_d_pairs.add((q, d, "CCW" if disp > 0 else "CW"))
                        total_pass += 1
                        found = True
                        break
            if found:
                break
        if not found:
            print(f"  FAIL: word={w}, combo_idx={combo_idx}")

print(f"\nTotal tests: {total_tests}")
print(f"Total pass: {total_pass}")
print(f"Movers SAME as good cycle: {mover_same_count}")
print(f"Movers DIFFERENT from good cycle: {mover_diff_count}")
print(f"Unique (q, d, dir) pairs: {unique_q_d_pairs}")
