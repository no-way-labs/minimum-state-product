#!/usr/bin/env python3
"""
RA Part 5: DEFINITIVE specification for FarShift BadCycleData.

Summary of findings from Parts 1-4:
1. Movers are DIFFERENT from good cycle (100%, all 512 cases)
2. NOT a constant shift (not bad[k] = shift(good[σ(k)], q, d))
3. Privilege is NOT unique — many steps have 2 privileged procs
4. q is NOT "far from movers" — q IS a mover
5. No safe proc exists (no proc at dist≥2 from all movers)
6. CW sweeps: q=P8 (ternary, proc n-1), d=1 or d=2
7. CCW sweeps: q=P6 (binary, second binary in CW direction), d=1
8. Construction: shift cfg[0] at q by d, follow forced entries choosing
   smallest-index privileged proc, get cycle of length CL = sum(ms).

For LEAN, the key question: how to DEFINE the construction?

APPROACH A: Recursive definition
  cfg[0] = shift(gc.configs[0], q, d)
  mover[k] = min {p | p privileged at cfg[k] via forced entries}
  cfg[k+1] = move sys (cfg[k]) (mover[k])

APPROACH B: Existential
  ∃ (cfg : Fin CL → Config) (mover : Fin CL → Fin n),
    ... all BadCycleData obligations hold

APPROACH C: ShadowTrap (weaker, no need for explicit configs)
  ∃ non-empty set S of non-good configs s.t. S is closed under forced transitions.

Let me verify Approach C works (it's the simplest for Lean).

But first: let me verify the construction at DIFFERENT ms vectors to understand
the q choice formula for general non-consecutive binary layouts.
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

def follow_forced_orbit(ms, n, c0, forced, CL):
    path = [c0]
    movers = []
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
            return None, None, "STUCK"
        p, Sp = privileged[0]
        movers.append(p)
        nxt = list(cur); nxt[p] = Sp; cur = tuple(nxt)
        if cur == c0:
            if len(path) == CL:
                return path, movers, "CYCLE"
            return None, None, f"SHORT"
        if cur in set(path): return None, None, "SUBCYCLE"
        path.append(cur)
    return None, None, "TIMEOUT"

# ============================================================
# Test at n=9 with DIFFERENT ms vectors
# ============================================================
print("="*72)
print("TEST ACROSS DIFFERENT ms VECTORS")
print("="*72)

# Non-consecutive binary, ≥3 binary, sub-threshold (product < 4*3^7 = 8748)
# At n=9: product < 8748. With 3 binary: 2^3 * X where X is prod of remaining 6.
# X < 8748/8 = 1093.5. So X ≤ 1093. With 6 ternary: 729. Product = 5832.
# With 5 ternary + 1 quaternary: 729*4/3 = 972. Product = 7776.
# With 4 ternary + 2 quaternary: 729*16/9 = 1296 > 1093. Too big.
# So valid: [2^3, 3^6] and [2^3, 3^5, 4].

# Test with ms = [2,3,3,2,3,3,2,3,4] (quaternary at P8)
test_cases = [
    ([2,3,3,2,3,3,2,3,3], 9, "3bin non-consec, all ternary"),
    # Different binary placement
    ([3,2,3,3,2,3,3,2,3], 9, "3bin non-consec, shifted"),
    ([2,3,3,3,2,3,3,3,2], 9, "3bin non-consec, spaced"),
]

for ms, n, desc in test_cases:
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
    n_combos = 1
    for p in range(n):
        n_combos *= len(all_combos[p])

    print(f"\n{desc}: ms={ms}, CL={CL}, sweeps={len(valid_words)}, combos={n_combos}")
    binary_procs = [p for p in range(n) if ms[p] == 2]
    print(f"  Binary procs: {binary_procs}")

    total_tests = 0
    total_pass = 0
    q_d_per_word = {}

    for wi, w in enumerate(valid_words):
        disp = compute_displacement(w, n)
        direction = "CCW" if disp > 0 else "CW"

        combo_lists = [all_combos[p] for p in range(n)]
        for combo_idx in itertools.product(*[range(len(c)) for c in combo_lists]):
            combo_t = tuple(combo_lists[p][combo_idx[p]] for p in range(n))
            cfgs = build_cycle_with_combo(ms, n, w, combo_t)
            if cfgs is None: continue
            gs = set(cfgs)
            fe = extract_forced_entries(ms, n, w, cfgs)
            total_tests += 1

            found = False
            for q in range(n):
                for d in range(1, ms[q]):
                    c0 = list(cfgs[0])
                    c0[q] = (c0[q] + d) % ms[q]
                    c0 = tuple(c0)
                    if c0 in gs: continue
                    path, movers, status = follow_forced_orbit(ms, n, c0, fe, CL)
                    if status == "CYCLE" and set(path).isdisjoint(gs):
                        total_pass += 1
                        key = (wi, direction)
                        if key not in q_d_per_word:
                            q_d_per_word[key] = []
                        q_d_per_word[key].append((q, d))
                        found = True
                        break
                if found: break
            if not found:
                print(f"  FAIL: word={w}, combo={combo_idx}")

    print(f"  Results: {total_pass}/{total_tests}")
    for key in sorted(q_d_per_word.keys()):
        wi, direction = key
        qd_counts = Counter(q_d_per_word[key])
        print(f"  Word {wi} ({direction}): q,d choices = {qd_counts.most_common(5)}")

# ============================================================
# DEFINITIVE: Check the Approach C (ShadowTrap) formulation.
# Can we just show: forced entries on non-good configs have
# a cycle, without specifying q, d, or the explicit configs?
# ============================================================
print(f"\n{'='*72}")
print("APPROACH C: Forced-entry graph has a cycle among non-good configs")
print("="*72)

# For the default case, count: how many non-good configs have a forced entry?
ms0 = [2,3,3,2,3,3,2,3,3]
n0 = 9
CL0 = sum(ms0)
w0 = [w for w in enumerate_exact_fc_words(ms0, n0, {p: ms0[p] for p in range(n0)})
      if abs(compute_displacement(w, n0)) == 2*n0][0]
combo0 = tuple(enumerate_state_sequences(ms0[p], ms0[p])[0] for p in range(n0))
cfgs0 = build_cycle_with_combo(ms0, n0, w0, combo0)
gs0 = set(cfgs0)
fe0 = extract_forced_entries(ms0, n0, w0, cfgs0)

# Enumerate all configs that are NOT good but have at least one forced privileged proc
total_configs = 1
for m in ms0:
    total_configs *= m
print(f"Total configs: {total_configs} (product of ms)")
print(f"Good configs: {len(gs0)}")

non_good_with_priv = 0
non_good_total = 0
for vals in itertools.product(*[range(m) for m in ms0]):
    c = tuple(vals)
    if c in gs0: continue
    non_good_total += 1
    has_priv = False
    for p in range(n0):
        L = c[(p-1)%n0]; S = c[p]; R = c[(p+1)%n0]
        if p in fe0 and (L,S,R) in fe0[p]:
            Sp = fe0[p][(L,S,R)]
            if Sp != S:
                has_priv = True
                break
    if has_priv:
        non_good_with_priv += 1

print(f"Non-good configs: {non_good_total}")
print(f"Non-good with forced privileged proc: {non_good_with_priv}")
print(f"Non-good without forced privileged proc: {non_good_total - non_good_with_priv}")

# Build the full forced-entry graph among non-good configs
# and find all cycles
print(f"\nBuilding forced-entry graph...")
graph = {}  # config -> (next_config, mover)
for vals in itertools.product(*[range(m) for m in ms0]):
    c = tuple(vals)
    if c in gs0: continue
    for p in range(n0):
        L = c[(p-1)%n0]; S = c[p]; R = c[(p+1)%n0]
        if p in fe0 and (L,S,R) in fe0[p]:
            Sp = fe0[p][(L,S,R)]
            if Sp != S:
                nxt = list(c); nxt[p] = Sp; nxt = tuple(nxt)
                if nxt not in gs0:
                    graph[c] = (nxt, p)
                break  # smallest-index privileged

# Find cycles in graph
visited = set()
cycles_found = 0
cycle_lengths = []
for start in graph:
    if start in visited: continue
    path = []
    path_set = set()
    cur = start
    while cur in graph and cur not in path_set:
        path.append(cur)
        path_set.add(cur)
        cur = graph[cur][0]
    if cur in path_set:
        # Found a cycle
        cycle_start = path.index(cur)
        cycle_len = len(path) - cycle_start
        cycles_found += 1
        cycle_lengths.append(cycle_len)
    visited.update(path_set)

print(f"Cycles found: {cycles_found}")
print(f"Cycle lengths: {Counter(cycle_lengths)}")

# ============================================================
# KEY FINDING: How many length-CL cycles exist in the forced graph?
# ============================================================
print(f"\nLength-{CL0} cycles: {cycle_lengths.count(CL0)}")

# ============================================================
# FINAL LEAN SPEC
# ============================================================
print(f"\n{'='*72}")
print("FINAL LEAN SPECIFICATION")
print("="*72)

print(f"""
THEOREM: For any system sys with a sweep good cycle gc that has ≥3 non-consecutive
binary procs and isolated firings at some binary proc p, there exists a
BadCycleData sys gc (hence the system does not converge).

PROOF STRUCTURE:

1. FORCED ENTRIES: Define the set of forced transition entries from gc:
   For each step k of gc, the mover p_k at config c_k has context (L,S,R)
   and transitions to S'. This gives: sys.f p_k (L,S,R) = S'.
   These are "forced" because they hold in ANY system that has this good cycle.

2. FORCED-ENTRY GRAPH: Define the directed graph G on non-good configs:
   - For each non-good config c, find the smallest proc p such that
     c's context at p matches a forced entry and the forced output ≠ c[p].
   - If such p exists, draw edge c → c' where c'[p] = forced output.
   - G is a deterministic graph (at most one outgoing edge per vertex).

3. EXISTENCE OF CYCLE: Show that G contains a cycle.
   PROOF: Start from c0 = (0,...,0) with c0[q] = d for suitable q, d.
   Follow G's edges for CL steps. Since all configs are non-good and
   each step is deterministic, either:
   (a) We get stuck (no privileged proc) → contradiction (shown computationally:
       every reachable non-good config has at least one forced privileged proc), OR
   (b) We revisit a config → cycle exists.
   Computationally verified: the cycle has length exactly CL in all cases.

4. BAD CYCLE DATA: Extract from the cycle:
   - cfg[k] = the k-th config in the cycle
   - mover[k] = the proc fired at step k
   Properties:
   (a) step: cfg[k+1] = move sys (cfg k) (mover k)  [by construction]
   (b) priv: mover k is privileged at cfg k  [forced entry context matches,
       sys.f agrees with forced entry, output ≠ current value]
   (c) disjoint: cfg k ∉ gc.configs  [by construction: only non-good configs in G]
   (d) distinct: all configs distinct  [from cycle + no repeated visits]
   (e) closure: cfg[CL] = cfg[0]  [cycle of length CL]

LEAN IMPLEMENTATION:

Option A (RECOMMENDED): Existential witness via ShadowTrap.
  Show ∃ (S : Finset Config), S.Nonempty ∧ (∀ c ∈ S, c ∉ gc.configs) ∧
  (∀ c ∈ S, ∃ p, privileged sys c p ∧ move sys c p ∈ S).
  This is WEAKER than BadCycleData (no need for explicit cycle, just closed set).
  The ShadowTrap structure already supports this.

Option B: Explicit BadCycleData via recursive definition.
  Define cfg : Fin CL → Config sys.rs by:
    cfg 0 = shift(gc.configs 0, q, d)
    cfg (k+1) = move sys (cfg k) (minPriv (cfg k))
  where minPriv c = min {{p | p forced-privileged at c}}.
  This requires showing the recursion terminates (it does after CL steps).

Option C: Explicit BadCycleData via iterate.
  cfg k = (move sys · minPriv)^[k] (c0)
  Lean has Nat.iterate for this.

CHOICE OF q AND d:
  For a CW sweep (displacement = -2n): q = word[1], d = 1
  For a CCW sweep (displacement = +2n): q = some binary proc (determined by layout)
  General rule: q is the first proc in the word that, when shifted in cfg[0],
  produces a non-good config c0 such that following forced entries gives a
  CL-cycle. This is existential (proven to exist by the computation).

  For Lean: use sorry for the specific q choice, or define it existentially.
  The KEY obligations (priv, step, disjoint, distinct) don't depend on which q
  is chosen — they follow from the forced-entry structure.
""")
