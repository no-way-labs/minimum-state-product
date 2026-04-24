#!/usr/bin/env python3
"""
RA Part 5: Deep structure of the forced-entry bad cycle.

Observation from Part 4: the bad cycle at n=7 has:
- Same fire counts as good cycle
- Its own mover word (different from good)
- The bad cycle IS a good cycle for a different mover word!
- At the end of the cycle (steps 15-17), bad = good + (0,0,0,0,0,0,1)

Hypothesis: The bad cycle is the SAME INCREMENTING CYCLE but starting from
a different initial config (shifted by (0,...,0,1,0,...,0) at some "far" proc).

Test: Is the bad cycle = build_cycle(ms, n, bad_mover_word) starting from
the shifted initial config?
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

def get_good_cycle_with_combo(ms, n, word, combo):
    ell = len(word)
    fc_num = [0]*ell
    pc = [0]*n
    for s in range(ell):
        fc_num[s] = pc[word[s]]
        pc[word[s]] += 1
    configs = []
    state = [0]*n
    for s in range(ell):
        configs.append(tuple(state))
        p = word[s]
        state[p] = combo[p][fc_num[s]+1]
    return configs, fc_num

# ============================================================
n = 7
ms = [2,3,3,2,3,3,2]

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
combo0 = tuple(enumerate_state_sequences(ms[p], ms[p])[0] for p in range(n))
gc_configs, _ = get_good_cycle_with_combo(ms, n, w0, combo0)
good_set = set(gc_configs)

# Forced entries
mcx = defaultdict(dict)
for s in range(ell):
    p = w0[s]
    L = gc_configs[s][(p-1)%n]; S = gc_configs[s][p]; R = gc_configs[s][(p+1)%n]
    mcx[p][(L, S, R)] = gc_configs[(s+1)%ell][p]

# The bad cycle from Part 4
bad_configs = [
    (0, 0, 0, 0, 0, 0, 1),
    (0, 0, 0, 0, 0, 1, 1),
    (0, 0, 0, 0, 1, 1, 1),
    (0, 0, 0, 1, 1, 1, 1),
    (0, 0, 1, 1, 1, 1, 1),
    (0, 0, 1, 1, 1, 1, 0),
    (1, 0, 1, 1, 1, 1, 0),
    (1, 1, 1, 1, 1, 1, 0),
    (1, 1, 1, 1, 1, 2, 0),
    (1, 1, 1, 1, 2, 2, 0),
    (1, 1, 1, 1, 2, 0, 0),
    (1, 1, 1, 1, 0, 0, 0),
    (1, 1, 1, 0, 0, 0, 0),
    (1, 1, 2, 0, 0, 0, 0),
    (1, 1, 2, 0, 0, 0, 1),
    (0, 1, 2, 0, 0, 0, 1),
    (0, 2, 2, 0, 0, 0, 1),
    (0, 2, 0, 0, 0, 0, 1),
]
bad_movers = [5, 4, 3, 2, 6, 0, 1, 5, 4, 5, 4, 3, 2, 6, 0, 1, 2, 1]

print(f"n={n}, ms={ms}")
print(f"Good mover word: {list(w0)}")
print(f"Bad mover word:  {bad_movers}")

# The good cycle increments each position. Since transitions are incrementing
# (f(L,S,R) = (S+1) mod m when privileged), the configs just accumulate
# increments at each mover position.

# The bad cycle also uses incrementing transitions! Each step fires a proc
# and increments it by 1 mod m. So the bad cycle is ALSO an incrementing cycle,
# just with a different mover word and starting from (0,0,0,0,0,0,1).

# KEY INSIGHT: The bad cycle starts from initial config (0,...,0,1) and
# follows the BAD mover word with incrementing transitions.
# It returns to (0,...,0,1) after 18 steps.

# Verify: rebuild bad cycle from initial config + bad movers + incrementing
print(f"\n--- Verify bad cycle = incrementing cycle from shifted start ---")
init = (0, 0, 0, 0, 0, 0, 1)
rebuilt = [init]
cur = list(init)
for s in range(ell):
    p = bad_movers[s]
    cur[p] = (cur[p] + 1) % ms[p]
    rebuilt.append(tuple(cur))

print(f"Returns to start: {rebuilt[-1] == init}")
print(f"Distinct: {len(set(rebuilt[:ell])) == ell}")
match = all(rebuilt[s] == bad_configs[s] for s in range(ell))
print(f"Matches bad cycle: {match}")

# Now the REAL question: why does the BAD mover word produce a cycle
# that uses ONLY forced entries from the GOOD cycle?
#
# Because: the forced entries are EXACTLY the incrementing entries!
# At each good config, the mover is privileged (S differs from neighbor),
# and the transition is S' = (S+1) mod m. The forced entry is:
#   f_p(L, S, R) = (S+1) mod m   when (L,S,R) appears at mover step
#
# For the bad cycle, at each step, the mover fires the SAME incrementing
# transition (S+1 mod m), but the context (L,S,R) might be different.
# The key: the context at the bad config's mover position must ALSO appear
# in the good cycle's forced entries.

print(f"\n--- Context matching analysis ---")
for s in range(ell):
    p = bad_movers[s]
    bc = bad_configs[s]
    L = bc[(p-1)%n]; S = bc[p]; R = bc[(p+1)%n]
    ctx = (L, S, R)
    in_forced = ctx in mcx[p]
    forced_val = mcx[p].get(ctx, None)
    inc_val = (S + 1) % ms[p]
    print(f"  Step {s:2d}: P{p} ctx={ctx} forced={'Y' if in_forced else 'N'} "
          f"forced_val={forced_val} inc_val={inc_val} match={forced_val == inc_val}")

# NOW: what is the relationship between good word and bad word?
# Good: [0, 6, 5, 4, 3, 2, 1, 0, 6, 5, 4, 5, 4, 3, 2, 1, 2, 1]
# Bad:  [5, 4, 3, 2, 6, 0, 1, 5, 4, 5, 4, 3, 2, 6, 0, 1, 2, 1]
# The bad word is a ROTATION + rearrangement of the good word!
# Let me check if it's just a rotation.

print(f"\n--- Mover word relationship ---")
gw = list(w0)
bw = bad_movers
print(f"Good: {gw}")
print(f"Bad:  {bw}")

# Check if bad is a rotation of good
for rot in range(ell):
    rotated = gw[rot:] + gw[:rot]
    if rotated == bw:
        print(f"Bad = Good rotated by {rot}")
        break
else:
    print("Bad is NOT a rotation of Good")

# Check fire counts
from collections import Counter
print(f"Good fc: {Counter(gw)}")
print(f"Bad fc:  {Counter(bw)}")
print(f"Same fc: {Counter(gw) == Counter(bw)}")

# Check if bad word is also a sweep
bad_disp = compute_displacement(bw, n)
print(f"Good displacement: {compute_displacement(gw, n)}")
print(f"Bad displacement: {bad_disp}")

# ============================================================
# KEY STRUCTURAL INSIGHT
# ============================================================
print(f"\n{'='*72}")
print("KEY INSIGHT: The incrementing transition is context-independent")
print("="*72)

# For incrementing transitions, f_p(L,S,R) = (S+1) mod m_p when privileged.
# The RESULT depends only on S, not on L or R.
# But PRIVILEGE depends on L and R (privilege means S != L or S != R or similar).
#
# So for the BAD cycle to work, we need:
# 1. At each step, the mover is privileged at the bad config
# 2. The incrementing transition gives the correct next config
#
# Condition 2 is automatic: since transitions are incrementing, firing any
# privileged proc just increments it by 1.
#
# Condition 1 (privilege) is the key: the mover must have a forced entry
# context at the bad config. This means (L,S,R) at the mover must appear
# in the good cycle's forced entries for that proc.
#
# For the Lean proof: we don't need to specify WHICH bad cycle configs.
# We just need to show there EXISTS a valid starting config c0 and a
# valid mover word w' such that:
# a) c0 ∉ good_set
# b) Following w' with incrementing transitions from c0 returns to c0
# c) All intermediate configs ∉ good_set
# d) At each step, the mover is privileged (context matches a forced entry)
# e) All configs are distinct

# But WAIT: we don't even know the transition function IS incrementing!
# The good cycle USES incrementing transitions (each proc goes 0->1->2->0),
# but the system could have ANY transition function that produces these outputs.
# The forced entries tell us: f_p(L,S,R) = (S+1) mod m_p for the specific
# (L,S,R) contexts seen in the good cycle. But f_p at OTHER contexts
# can be anything.

# So the bad cycle must only use contexts that appear in the good cycle's
# forced entries. Let me verify this is the case.

print(f"\n--- All forced contexts per proc ---")
for p in range(n):
    ctxs = list(mcx[p].keys())
    print(f"  P{p} (m={ms[p]}): {ctxs}")
    # How many total contexts exist? m_{p-1} * m_p * m_{p+1}
    total = ms[(p-1)%n] * ms[p] * ms[(p+1)%n]
    print(f"    {len(ctxs)}/{total} forced ({100*len(ctxs)/total:.1f}%)")

# ============================================================
# FORMULA APPROACH: Construct bad cycle via "far proc shift"
# ============================================================
print(f"\n{'='*72}")
print("FORMULA: Far proc shift construction")
print("="*72)

# Pick proc q that's "far" from the initial mover.
# The bad cycle starts from (0,...,0) + e_q where e_q is +1 at position q.
# Then follow the SAME forced entries as the good cycle, but the movers
# may differ because the sweep direction changes.

# Actually, let me think about this differently. The bad cycle configs are:
# b[s] = (0,...,0,1,...,0) with 1 at position q, then accumulate increments
# from the bad mover word.
#
# BUT: for the Lean proof, we need to express the bad cycle in terms of
# the GOOD cycle's data (good configs + forced entries), not in terms of
# a separately-discovered bad mover word.
#
# The simplest approach for Lean: use the ShadowTrap structure.
# A ShadowTrap is a set of configs S such that:
# - S ∩ good = ∅
# - For every c in S, there exists a forced transition from c to some c' in S
# This implies non-convergence (trapped configs can never reach good).

# The ShadowTrap doesn't need movers or ordering — just a nonempty set with
# forced out-edges staying within the set.

# But the Lean uses BadCycleData, which is more structured:
# cfg, mover, disjoint, priv, step, distinct.

# Let me check: can we use a DIFFERENT Lean approach? Instead of BadCycleData,
# use ShadowTrap?

# Actually, let me re-read the Lean more carefully to see what's needed.

# For now, let me establish the formula:
# Given a good sweep cycle with mover word w, the bad cycle is obtained by:
# 1. Choose q = the proc farthest from w[0] on the ring
# 2. Start from c0 = (0,...,0) + e_q  (shift proc q by +1)
# 3. Follow forced transitions: at each step, find any proc p where the
#    context (L,S,R) at c matches a forced entry and S' != S. Fire it.
# 4. This produces a cycle of length CL that is disjoint from good.

# The question is: does this ALWAYS produce a valid cycle? And is the
# choice of which forced transition to fire at each step deterministic?

# At each step of the bad cycle, how many forced transitions are available?
print(f"\nForced transitions available at each bad config:")
for s in range(len(bad_configs)):
    c = bad_configs[s]
    available = []
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        if (L, S, R) in mcx[p]:
            Sp = mcx[p][(L, S, R)]
            if Sp != S:
                available.append(p)
    chosen = bad_movers[s]
    print(f"  [{s:2d}] {c} available={available} chosen=P{chosen}")
    # Is there always exactly one?

# ============================================================
# The REAL construction: good cycle's "incrementing wavefront"
# ============================================================
print(f"\n{'='*72}")
print("WAVEFRONT ANALYSIS")
print("="*72)

# Good cycle at n=7:
# Step 0: fire P0, config (0,0,0,0,0,0,0) -> (1,0,0,0,0,0,0)
# Step 1: fire P6, config (1,0,0,0,0,0,0) -> (1,0,0,0,0,0,1)
# ...
# The wavefront sweeps CW from P0: P0, P6, P5, P4, P3, P2, P1, then back
# This is a CW sweep that increments each proc.

# The bad cycle:
# Step 0: fire P5 at (0,0,0,0,0,0,1) -> increment to (0,0,0,0,0,1,1)
# The wavefront ALSO sweeps from right to left!
# P5, P4, P3, P2 (CW sweep of ternary procs 2-5)
# Then P6 (binary), P0 (binary), P1 (ternary)
# Then repeat pattern

# The bad cycle is just the SAME sweep starting from a shifted position!
# It's like the good cycle was "pushed forward" by shifting P6's state.

print(f"\nGood cycle:")
for s in range(ell):
    print(f"  [{s:2d}] fire P{w0[s]}: {gc_configs[s]} -> {gc_configs[(s+1)%ell]}")

print(f"\nBad cycle:")
for s in range(ell):
    p = bad_movers[s]
    c = bad_configs[s]
    nc = list(c); nc[p] = (c[p] + 1) % ms[p]; nc = tuple(nc)
    print(f"  [{s:2d}] fire P{p}: {c} -> {nc}")

# ============================================================
# CRITICAL TEST: Is shifting P6 (last binary proc on CW side)
# by +1 ALWAYS the construction?
# ============================================================
print(f"\n{'='*72}")
print("CRITICAL: Which proc is shifted?")
print("="*72)

# The bad cycle starts at (0,0,0,0,0,0,1). This is good cycle's start
# with P6 shifted by +1. P6 is binary (m=2), so shifting by +1 means flip.
# But the good cycle starts at (0,0,0,0,0,0,0), and the bad starts at
# (0,0,0,0,0,0,1). The offset is at P6 only.

# Is this universal? For all combos and sweeps?
all_cfgs = list(itertools.product(*(range(m) for m in ms)))
all_combos = list(itertools.product(*[enumerate_state_sequences(ms[p], ms[p]) for p in range(n)]))

print(f"Testing shift construction for all {len(sweeps)} sweeps x {len(all_combos)} combos...")

for wi, (word, _, disp) in enumerate(sweeps):
    for ci, combo in enumerate(all_combos):
        gc, _ = get_good_cycle_with_combo(ms, n, word, combo)
        gs = set(gc)

        mx = defaultdict(dict)
        for s in range(len(word)):
            p = word[s]
            L = gc[s][(p-1)%n]; S = gc[s][p]; R = gc[s][(p+1)%n]
            mx[p][(L, S, R)] = gc[(s+1)%len(word)][p]

        # Build graph and find cycle
        local_adj = {}
        for c in all_cfgs:
            if c in gs: continue
            edges = []
            for p in range(n):
                L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
                if (L, S, R) in mx[p]:
                    Sp = mx[p][(L, S, R)]
                    if Sp != S:
                        nc = list(c); nc[p] = Sp; nc = tuple(nc)
                        if nc not in gs:
                            edges.append((nc, p))
            if edges:
                local_adj[c] = edges

        # Follow first-edge orbit from first available config
        for start in local_adj:
            path = [start]
            path_set = {start}
            cur = start
            movers_list = []
            while cur in local_adj:
                nxt, p = local_adj[cur][0]
                movers_list.append(p)
                if nxt in path_set:
                    idx = path.index(nxt)
                    cyc = path[idx:]
                    cyc_movers = movers_list[idx:]
                    # Found cycle. What's the initial offset from good cycle?
                    # Find which step of good cycle aligns with cyc[0]
                    offset = tuple((cyc[0][p] - gc[0][p]) % ms[p] for p in range(n))
                    # How many positions differ?
                    ndiff = sum(1 for p in range(n) if offset[p] != 0)
                    if wi == 0 and ci == 0:
                        print(f"  Sweep {wi} combo {ci}: cycle start offset={offset} "
                              f"(differs at {ndiff} pos), cycle len={len(cyc)}")
                    break
                path.append(nxt)
                path_set.add(nxt)
                cur = nxt
            break

# Let me also check: what if we CONSTRUCT the bad cycle by shifting a specific
# proc and following forced transitions?
print(f"\n--- Direct shift construction test ---")
for q in range(n):
    # Shift proc q by +1 at starting config
    c0 = list(gc_configs[0])
    c0[q] = (c0[q] + 1) % ms[q]
    c0 = tuple(c0)

    if c0 in good_set:
        print(f"  Shift P{q}: overlaps good at start")
        continue

    # Follow forced transitions
    path = [c0]
    cur = c0
    ok = True
    for _ in range(ell + 5):
        # Find available forced transitions
        available = []
        for p in range(n):
            L = cur[(p-1)%n]; S = cur[p]; R = cur[(p+1)%n]
            if (L, S, R) in mcx[p]:
                Sp = mcx[p][(L, S, R)]
                if Sp != S:
                    nc = list(cur); nc[p] = Sp; nc = tuple(nc)
                    if nc not in good_set:
                        available.append((nc, p))
        if not available:
            print(f"  Shift P{q}: stuck at step {len(path)-1}, no forced transition")
            ok = False
            break
        nxt, p = available[0]
        if nxt == c0 and len(path) > 1:
            # Cycle found!
            print(f"  Shift P{q}: CYCLE of length {len(path)} "
                  f"(expected {ell}), match={'YES' if len(path)==ell else 'NO'}")
            ok = True

            # Verify all BadCycleData properties
            bcyc = path
            bmov = []
            cur2 = c0
            for s in range(len(bcyc)):
                for p2 in range(n):
                    L = cur2[(p2-1)%n]; S = cur2[p2]; R = cur2[(p2+1)%n]
                    if (L, S, R) in mcx[p2]:
                        Sp = mcx[p2][(L, S, R)]
                        if Sp != S:
                            nc2 = list(cur2); nc2[p2] = Sp; nc2 = tuple(nc2)
                            if nc2 not in good_set:
                                if s < len(bcyc) - 1 and nc2 == bcyc[s+1]:
                                    bmov.append(p2)
                                    cur2 = nc2
                                    break
                                elif s == len(bcyc) - 1 and nc2 == c0:
                                    bmov.append(p2)
                                    cur2 = nc2
                                    break
                else:
                    ok = False

            if ok and len(bmov) == len(bcyc):
                # Full verification
                disjoint = all(c not in good_set for c in bcyc)
                distinct = len(set(bcyc)) == len(bcyc)
                print(f"    disjoint={disjoint} distinct={distinct}")
            break
        if nxt in set(path):
            # Inner cycle (not back to start)
            idx = path.index(nxt)
            print(f"  Shift P{q}: inner cycle at step {len(path)}, cycle len={len(path)-idx}")
            ok = False
            break
        path.append(nxt)
        cur = nxt
    else:
        if ok:
            print(f"  Shift P{q}: no cycle found within {ell+5} steps")
