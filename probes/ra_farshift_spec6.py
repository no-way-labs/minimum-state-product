#!/usr/bin/env python3
"""
RA Part 6: The forced-entry graph approach.

Key finding from Part 5: "shift one proc, follow forced entries" fails for
some binary placements (192/512 for shifted layout). But the forced-entry
graph ALWAYS has cycles of length CL among non-good configs.

NEW APPROACH: Don't start from a specific c0. Instead, show that the forced-
entry graph restricted to non-good configs has a cycle. This is equivalent
to showing there's a ShadowTrap.

For Lean: the simplest proof is:
1. The forced-entry graph on all configs has CL = sum(ms) outgoing edges.
2. The good cycle uses CL of these edges.
3. Every forced entry that fires at config c produces config c'.
4. If c is not good, c' might or might not be good.
5. But the set of configs reachable from any non-good config with forced privilege
   must contain a cycle (pigeon hole: finite set, deterministic transitions).

Actually, the key insight is MUCH simpler. Let me check it.

KEY CLAIM: For each forced entry (p, L, S, R) -> S', there are exactly ms[q]
configs that have this context at p (varying the value at some far proc q).
One of these is the good config. The other ms[q]-1 are non-good.
All ms[q] configs transition to configs that also differ only at q.
So they form parallel orbits!

No wait, that's only true if q is far from p (dist ≥ 2).
"""

import itertools
from collections import defaultdict, Counter

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
                seq.append(nv)
                dfs(seq, remaining-1)
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
# THE PARALLEL ORBIT IDEA
# ============================================================
# If proc q is at distance ≥ 2 from every mover at every step,
# then shifting q does not change any mover context.
# So: bad_cfg[k] = good_cfg[k] with c[q] shifted by d.
# Same movers. Same contexts. Same transitions. Closed cycle.
# Disjoint (differ at q). Distinct (good are distinct, shift is uniform).

# The hno_safe hypothesis says NO such q exists.
# But we can still find a q that is far from MOST movers.
# At the steps where q IS in the mover's neighborhood:
# the context changes, but it STILL matches a forced entry.

# QUESTION: Is there always a proc q and value d such that:
# For EVERY step k, the mover's context at shift(good_cfg[k], q, d)
# matches some forced entry? Not necessarily the SAME forced entry
# as at good step k, but SOME forced entry.

# This would give: same movers, same transitions (via forced entries),
# closed cycle. SIMPLER than the forced-entry graph.

# ============================================================
# n=9, ms=[2,3,3,2,3,3,2,3,3]
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
    if canon not in seen:
        seen.add(canon)
        unique.append(w)
valid_words = [w for w in unique if abs(compute_displacement(w, n)) == 2*n]
all_combos = {}
for p in range(n):
    all_combos[p] = enumerate_state_sequences(ms[p], ms[p])

print(f"n={n}, ms={ms}, sweeps={len(valid_words)}")

# ============================================================
# For the FIRST word + combo, check the uniform shift approach
# ============================================================
word = valid_words[0]
combo = tuple(all_combos[p][0] for p in range(n))
configs = build_cycle_with_combo(ms, n, word, combo)
good_set = set(configs)
forced = extract_forced_entries(ms, n, word, configs)

print(f"\n{'='*72}")
print("UNIFORM SHIFT: bad[k] = good[k] with c[q] shifted by d")
print("Same movers as good cycle. Check if contexts still match forced entries.")
print(f"{'='*72}")

for q in range(n):
    for d in range(1, ms[q]):
        # Build shifted configs
        shifted = []
        for s in range(CL):
            c = list(configs[s])
            c[q] = (c[q] + d) % ms[q]
            shifted.append(tuple(c))

        # Check: is each shifted config non-good?
        disjoint = all(sc not in good_set for sc in shifted)
        # Check: distinct?
        distinct = len(set(shifted)) == CL
        # Check: at each step, does the mover have a matching forced entry?
        # AND does firing it give the next shifted config?
        all_priv = True
        all_step = True
        for s in range(CL):
            p = word[s]
            c = shifted[s]
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
            if p not in forced or (L,S,R) not in forced[p]:
                all_priv = False
                break
            Sp = forced[p][(L,S,R)]
            if Sp == S:
                all_priv = False
                break
            # Check: firing p at shifted[s] gives shifted[s+1]?
            nxt = list(c)
            nxt[p] = Sp
            expected = shifted[(s+1) % CL]
            if tuple(nxt) != expected:
                all_step = False
                break

        if all_priv and all_step and disjoint and distinct:
            print(f"  q=P{q}, d={d}: UNIFORM SHIFT WORKS! All props satisfied.")
        else:
            status = []
            if not all_priv: status.append("priv_fail")
            if not all_step: status.append("step_fail")
            if not disjoint: status.append("not_disjoint")
            if not distinct: status.append("not_distinct")
            # If priv fails, find which step
            if not all_priv:
                fail_steps = []
                for s in range(CL):
                    p = word[s]
                    c = shifted[s]
                    L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
                    if p not in forced or (L,S,R) not in forced[p]:
                        fail_steps.append((s, p, (L,S,R), "no_entry"))
                    elif forced[p][(L,S,R)] == S:
                        fail_steps.append((s, p, (L,S,R), "not_priv"))
                print(f"  q=P{q}, d={d}: {status}, fails at {len(fail_steps)} steps: {fail_steps[:3]}...")
            else:
                print(f"  q=P{q}, d={d}: {status}")

# ============================================================
# KEY FINDING: The uniform shift approach might NOT have all contexts
# matching forced entries. At steps where q is in the mover's 3-neighborhood,
# the context changes and might not be in the forced entry table.
#
# But: the forced entry table might not cover ALL possible contexts.
# It only covers the contexts that appear in the good cycle.
# A shifted context might be a NEW context not in the table.
#
# In that case, we CANNOT use forced entries — we need the actual system's
# transition function, which we don't know.
#
# So the uniform shift approach only works when q is far from ALL movers.
# Since hno_safe says no such q exists, we need a different approach.
# ============================================================

# ============================================================
# BACK TO FORCED-ENTRY GRAPH: verify it ALWAYS has a cycle for ALL ms layouts
# ============================================================
print(f"\n{'='*72}")
print("FORCED-ENTRY GRAPH: Cycle check for different ms layouts")
print(f"{'='*72}")

test_layouts = [
    [2,3,3,2,3,3,2,3,3],
    [3,2,3,3,2,3,3,2,3],
    [2,3,3,3,2,3,3,3,2],
]

for ms_test in test_layouts:
    n_test = len(ms_test)
    CL_test = sum(ms_test)
    target_fc_test = {p: ms_test[p] for p in range(n_test)}
    words_test = enumerate_exact_fc_words(ms_test, n_test, target_fc_test)
    seen_test = set()
    unique_test = []
    for w in words_test:
        canon = tuple(min(w[i:]+w[:i] for i in range(len(w))))
        if canon not in seen_test:
            seen_test.add(canon)
            unique_test.append(w)
    valid_test = [w for w in unique_test if abs(compute_displacement(w, n_test)) == 2*n_test]

    combos_test = {}
    for p in range(n_test):
        combos_test[p] = enumerate_state_sequences(ms_test[p], ms_test[p])

    print(f"\nms={ms_test}, sweeps={len(valid_test)}")

    total_pass = 0
    total_tests = 0
    for wi, w in enumerate(valid_test):
        for combo_idx in itertools.product(*[range(len(combos_test[p])) for p in range(n_test)]):
            combo_t = tuple(combos_test[p][combo_idx[p]] for p in range(n_test))
            cfgs = build_cycle_with_combo(ms_test, n_test, w, combo_t)
            if cfgs is None: continue
            gs = set(cfgs)
            fe = extract_forced_entries(ms_test, n_test, w, cfgs)
            total_tests += 1

            # Build forced-entry graph on non-good configs
            graph = {}
            for vals in itertools.product(*[range(m) for m in ms_test]):
                c = tuple(vals)
                if c in gs: continue
                for p in range(n_test):
                    L = c[(p-1)%n_test]; S = c[p]; R = c[(p+1)%n_test]
                    if p in fe and (L,S,R) in fe[p]:
                        Sp = fe[p][(L,S,R)]
                        if Sp != S:
                            nxt = list(c); nxt[p] = Sp; nxt = tuple(nxt)
                            if nxt not in gs:
                                graph[c] = (nxt, p)
                            break

            # Find any cycle
            visited = set()
            has_cycle = False
            for start in graph:
                if start in visited: continue
                path_set = set()
                cur = start
                while cur in graph and cur not in path_set and cur not in visited:
                    path_set.add(cur)
                    cur = graph[cur][0]
                if cur in path_set:
                    has_cycle = True
                visited.update(path_set)

            if has_cycle:
                total_pass += 1

    print(f"  Forced-entry graph has cycle: {total_pass}/{total_tests}")

# ============================================================
# EVEN SIMPLER: Does the forced-entry graph on non-good configs
# ALWAYS have a cycle? Can we prove this abstractly?
# ============================================================
print(f"\n{'='*72}")
print("WHY does the forced-entry graph always have a cycle?")
print(f"{'='*72}")

# Consider the "parallel orbit" idea more carefully.
# At each good step k, mover p_k fires, changing config c_k -> c_{k+1}.
# The mover changes proc p_k from S to S' while keeping all other procs fixed.
# The forced entry is: at proc p_k, context (L,S,R) -> S'.
#
# Now consider ANY config c' that agrees with c_k at positions p_k-1, p_k, p_k+1.
# That is: c'[p_k-1] = c_k[p_k-1], c'[p_k] = c_k[p_k], c'[p_k+1] = c_k[p_k+1].
# Then c' has the same forced entry, so p_k is privileged at c'.
# Firing p_k at c' gives c'' = c' with c''[p_k] = S'.
#
# KEY: c'' agrees with c_{k+1} at positions p_k-1, p_k, p_k+1.
# (Because c'[p_k-1]=c_k[p_k-1]=c_{k+1}[p_k-1] [mover doesn't change neighbors],
#  c''[p_k]=S'=c_{k+1}[p_k], c'[p_k+1]=c_k[p_k+1]=c_{k+1}[p_k+1].)
#
# But wait: at step k+1, the mover p_{k+1} might have p_k in its 3-neighborhood.
# If p_{k+1} is adjacent to p_k, then c'' might NOT agree with c_{k+1} at
# p_{k+1}'s context positions, because c'' could differ from c_{k+1} at
# positions outside {p_k-1, p_k, p_k+1}.
#
# Specifically: c'' agrees with c_{k+1} at p_k-1, p_k, p_k+1.
# But c'' might differ at other positions.
# At step k+1, mover p_{k+1} has context (c[p_{k+1}-1], c[p_{k+1}], c[p_{k+1}+1]).
# These positions must equal c_{k+1}'s values for the forced entry to apply.
# If p_{k+1} is NOT in {p_k-1, p_k, p_k+1}, this is not guaranteed.
#
# WAIT: I need to think about this differently. The parallel orbit idea
# shifts c' at a position q far from all movers. Then c'[q] differs from
# c_k[q] but all mover contexts are the same. This DOES work when q exists.
#
# When no such q exists, the orbit through forced entries is more complex.
# The mover at each step might be DIFFERENT because the contexts change.

# Let me check: in the forced-entry graph, how many non-good configs
# have NO outgoing edge (no forced privileged proc)?

ms_test = [2,3,3,2,3,3,2,3,3]
n_test = 9
CL_test = 24
w = valid_words[0]
combo = tuple(all_combos[p][0] for p in range(n_test))
cfgs = build_cycle_with_combo(ms_test, n_test, w, combo)
gs = set(cfgs)
fe = extract_forced_entries(ms_test, n_test, w, cfgs)

no_edge = 0
has_edge = 0
edge_to_good = 0  # has forced priv but leads to good config
for vals in itertools.product(*[range(m) for m in ms_test]):
    c = tuple(vals)
    if c in gs: continue
    found = False
    for p in range(n_test):
        L = c[(p-1)%n_test]; S = c[p]; R = c[(p+1)%n_test]
        if p in fe and (L,S,R) in fe[p]:
            Sp = fe[p][(L,S,R)]
            if Sp != S:
                nxt = list(c); nxt[p] = Sp; nxt = tuple(nxt)
                if tuple(nxt) in gs:
                    edge_to_good += 1
                else:
                    has_edge += 1
                found = True
                break
    if not found:
        no_edge += 1

print(f"Non-good configs: {no_edge + has_edge + edge_to_good}")
print(f"  With edge to non-good: {has_edge}")
print(f"  With edge to GOOD (absorbed): {edge_to_good}")
print(f"  With NO edge (no forced priv): {no_edge}")
print(f"  Ratio with edge: {(has_edge + edge_to_good) / (no_edge + has_edge + edge_to_good):.3f}")

# If we extend the graph to allow edges to good configs:
# Good configs also have forced transitions (to the next good config).
# So the extended graph on ALL configs is the forced-entry transition graph.
# The good cycle is one cycle. Non-good cycles are others.
# The graph is deterministic (smallest-index privileged).
# So it decomposes into trees feeding into cycles.
# Q: are there cycles BESIDES the good cycle?

print(f"\nFull forced-entry graph (all configs, smallest-index):")
graph_full = {}
for vals in itertools.product(*[range(m) for m in ms_test]):
    c = tuple(vals)
    for p in range(n_test):
        L = c[(p-1)%n_test]; S = c[p]; R = c[(p+1)%n_test]
        if p in fe and (L,S,R) in fe[p]:
            Sp = fe[p][(L,S,R)]
            if Sp != S:
                nxt = list(c); nxt[p] = Sp; graph_full[c] = (tuple(nxt), p)
                break

# Count cycles
visited = set()
cycle_configs = set()
cycle_count = 0
cycle_lens = []
for start in graph_full:
    if start in visited: continue
    path = []
    path_set = set()
    cur = start
    while cur in graph_full and cur not in path_set and cur not in visited:
        path.append(cur)
        path_set.add(cur)
        cur = graph_full[cur][0]
    if cur in path_set:
        cycle_start = path.index(cur)
        cycle = path[cycle_start:]
        cycle_count += 1
        cycle_lens.append(len(cycle))
        cycle_configs.update(cycle)
    visited.update(path_set)

print(f"  Total cycles: {cycle_count}")
print(f"  Cycle lengths: {Counter(cycle_lens)}")
print(f"  Good cycle among them: {any(all(c in gs for c in [cfgs[i] for i in range(CL_test)]) for _ in [1])}")

# Verify good cycle is one of them
good_cycle_found = False
for start in graph_full:
    if start != cfgs[0]: continue
    cur = start
    path = [cur]
    for _ in range(CL_test):
        cur = graph_full[cur][0]
        path.append(cur)
    if cur == start and len(set(path[:-1])) == CL_test:
        good_cycle_found = True
        # Check all are good
        all_good = all(c in gs for c in path[:-1])
        print(f"  Good cycle check: starts at cfg[0], length {CL_test}, all good: {all_good}")
print(f"  Non-good cycles: {cycle_count - (1 if good_cycle_found else 0)}")
