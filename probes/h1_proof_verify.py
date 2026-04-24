#!/usr/bin/env python3
"""
VERIFICATION OF THE PROOF MECHANISM.

Theorem: For {2,3} state sizes, n>=5, >=3 binary, sub-threshold product,
sandwiched ternary t, if a good cycle has a (1,1) phase at t:
  CASE A (>=3 consecutive binary): EC at the middle proc q (all-binary context).
  CASE B (no 3 consecutive binary): EC at the sandwiched ternary t.

This verifies the key lemmas used in the proof:

LEMMA A1: In Case A, q has fc(q) = 2.
LEMMA A2: In Case A, q has >= 5 distinct nonmover contexts.
LEMMA A3: In Case A, at least one mover context of q equals some nonmover context.

LEMMA B1: In Case B, the sandwiched ternary t has EC.
  (If not at t, then at one of its binary neighbors with ctx_space=12.)

Actually from the data, in Case B:
  - EC ALWAYS occurs at t (fc=3: 778 cycles, fc=6: 76 cycles).
  - EC also occurs at binary neighbors sometimes.

Let me verify LEMMA A3 more carefully: WHY must mover overlap nonmover at q?

In a (1,1) phase at t:
  - bL fires once (flip), bR fires once (flip).
  - All remote procs fire (contributing to the walk).
  - The walk goes through all procs in the ring.

For q (all-binary-context, distance >=2 from t):
  q fires exactly twice in the whole cycle.
  Between q's two firings: the config at q cycles through contexts.

The (1,1) phase constrains the GLOBAL cycle structure. With only 8 possible
contexts at q and fc(q)=2 (2 mover appearances), the 2 mover contexts use
2 of the 8 slots. The remaining 6+ distinct nonmover contexts must also fit
in the 8 slots. So |mover_distinct ∪ nonmover_distinct| can be at most 8.
With 2 mover + 5 nonmover: that's 7 total if no overlap, which fits in 8.
Need: overlap > 0, i.e., |M ∪ N| + overlap = |M| + |N|, and we need
|M ∪ N| <= 8.

From data: |M|=2, |N|=4..5. So |M ∪ N| <= 2+5 = 7 if no overlap.
With overlap=0: 7 <= 8, which FITS. So pure pigeonhole on 8 DOESN'T work!

The overlap must come from the STRUCTURE, not just counting.
Let me look at this more carefully.
"""
from collections import Counter
from itertools import product as iproduct

def enumerate_good_cycles(ms, n, max_length=20):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length: return
        if len(word) >= n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            nc = list(config)
            nc[nxt] = (nc[nxt] + 1) % ms[nxt]
            nf = list(fc)
            nf[nxt] += 1
            word.append(nxt)
            dfs(word, nf, tuple(nc))
            word.pop()
    for p in range(n):
        first = list(start)
        first[p] = (first[p] + 1) % ms[p]
        dfs([p], [1 if i == p else 0 for i in range(n)], tuple(first))
    return results

def build_configs(ms, n, word):
    L = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(L):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]: return None
    if len(set(configs[:L])) != L: return None
    return configs[:L]

def is_wrap_adjacent(word, n):
    return abs(word[-1] - word[0]) % n in (1, n-1)

# Focus on Case A: ms=[2,2,2,2,3], q=1 or q=2
n = 5
ms = [2, 2, 2, 2, 3]
t = 4
bL, bR = 3, 0
q = 2  # all-binary: neighbors are 1 and 3, both binary
qL, qR = 1, 3

words = enumerate_good_cycles(ms, n, 20)

print("="*70)
print("WHY DOES OVERLAP OCCUR AT q?")
print("="*70)

# Trace the specific mechanism.
# q fires at s1, s2 with fc(q)=2.
# Mover ctx at s1: (configs[s1][qL], configs[s1][q], configs[s1][qR]).
# Mover ctx at s2: (configs[s2][qL], configs[s2][q], configs[s2][qR]).
# Since q is binary: configs[s2][q] = 1 - configs[s1][q].

# The walk structure: in a (1,1) phase at t=4 with bL=3, bR=0:
# Phase walk pattern: 3, 2, 1, 0 or 0, 1, 2, 3 (traversal through the ring).
# So q=2 fires in the middle of the traversal.

# In a traversal phase [3,2,1,0]: q fires at step where mover=2.
# q is between 1 and 3 in the ring. When q fires:
#   - qL=1 has value determined by whether it has fired yet in this phase.
#   - qR=3 has value determined by whether it has fired yet.
# In pattern [3,2,1,0]: 3 fires first, then 2, then 1, then 0.
#   When q=2 fires: qR=3 has already fired (value flipped), qL=1 has not.
# In pattern [0,1,2,3]: 0 fires first, then 1, then 2, then 3.
#   When q=2 fires: qL=1 has already fired, qR=3 has not.

# Between different phases: q's value is constant (it doesn't fire between phases).
# So nonmover contexts at q in one phase have q_val = (value after last q firing).
# In the NEXT traversal, q fires again, seeing different neighbor values.

# KEY INSIGHT: the two traversals go in OPPOSITE directions.
# One (1,1) phase has walk [3,2,1,0] (right-to-left), another has [0,1,2,3] (left-to-right).
# Or same direction but different t-value phases.

# In the right-to-left traversal:
#   qR fires before q, qL fires after q.
#   Mover ctx at q: (old_qL, q_val, new_qR) = (qL_before, q_val, 1-qR_before)
# In the left-to-right traversal:
#   qL fires before q, qR fires after q.
#   Mover ctx at q: (new_qL, q_val', qR_before') = (1-qL_before', q_val', qR_before')

# Actually let me just look at all the walk patterns and see what's happening.

# Collect: for each (1,1) cycle, the pair of walk patterns in the two (1,1) phases
# (or all phases).

total = 0
overlap_from_traversal = 0

for word in words:
    configs = build_configs(ms, n, word)
    if configs is None: continue
    if not is_wrap_adjacent(word, n): continue
    L = len(word)
    fc = Counter(word)

    # Find all (1,1) phases at t
    t_steps = [s for s in range(L) if word[s] == t]
    ft = len(t_steps)
    phases_11 = []
    for idx in range(ft):
        k1 = t_steps[idx]
        k2 = t_steps[(idx+1)%ft]
        phase = []
        s = (k1+1)%L
        while s != k2:
            phase.append(s)
            s = (s+1)%L
        J = sum(1 for s in phase if word[s] == bL)
        K = sum(1 for s in phase if word[s] == bR)
        if J == 1 and K == 1:
            movers = tuple(word[s] for s in phase)
            phases_11.append((k1, k2, phase, movers))

    if not phases_11: continue
    total += 1

    # Mover and nonmover at q
    mover_set = set()
    nonmover_set = set()
    for s in range(L):
        ctx = (configs[s][qL], configs[s][q], configs[s][qR])
        if word[s] == q: mover_set.add(ctx)
        else: nonmover_set.add(ctx)

    overlap = mover_set & nonmover_set

    if total <= 5 and overlap:
        print(f"\nword={word}, L={L}, fc={dict(fc)}")
        print(f"  (1,1) phases: {len(phases_11)}")
        for i, (k1, k2, phase, movers) in enumerate(phases_11):
            print(f"    phase {i}: k1={k1}->k2={k2}, movers={movers}")

        # q's firing steps
        q_steps = [s for s in range(L) if word[s] == q]
        print(f"  q fires at: {q_steps}")
        for s in q_steps:
            ctx = (configs[s][qL], configs[s][q], configs[s][qR])
            print(f"    step {s}: mover ctx = {ctx}")

        # Overlapping contexts
        for ctx in overlap:
            print(f"  OVERLAP: {ctx}")
            # Find where it appears as mover and nonmover
            for s in range(L):
                c = (configs[s][qL], configs[s][q], configs[s][qR])
                if c == ctx:
                    role = "MOVER" if word[s] == q else "nonmover"
                    print(f"    step {s}: {role}, global mover={word[s]}")

# ===== The REAL mechanism =====
# Let me check: does the overlapping context at q come from the same
# q_val (own value) in both roles?
print("\n" + "="*70)
print("OVERLAP MECHANISM: same own_val in both roles?")
print("="*70)

same_val = 0
diff_val = 0

for word in words:
    configs = build_configs(ms, n, word)
    if configs is None: continue
    if not is_wrap_adjacent(word, n): continue
    L = len(word)

    t_steps = [s for s in range(L) if word[s] == t]
    ft = len(t_steps)
    has_11 = False
    for idx in range(ft):
        k1 = t_steps[idx]
        k2 = t_steps[(idx+1)%ft]
        phase = []
        s = (k1+1)%L
        while s != k2:
            phase.append(s)
            s = (s+1)%L
        J = sum(1 for s in phase if word[s] == bL)
        K = sum(1 for s in phase if word[s] == bR)
        if J == 1 and K == 1:
            has_11 = True
            break
    if not has_11: continue

    mover_steps = {s: (configs[s][qL], configs[s][q], configs[s][qR])
                   for s in range(L) if word[s] == q}
    nonmover_steps = {s: (configs[s][qL], configs[s][q], configs[s][qR])
                      for s in range(L) if word[s] != q}

    mover_set = set(mover_steps.values())
    nonmover_set = set(nonmover_steps.values())
    overlap = mover_set & nonmover_set

    for ctx in overlap:
        # Find mover step and nonmover step with this context
        m_step = [s for s, c in mover_steps.items() if c == ctx][0]
        n_step = [s for s, c in nonmover_steps.items() if c == ctx][0]
        if configs[m_step][q] == configs[n_step][q]:
            same_val += 1
        else:
            diff_val += 1

print(f"Overlap with same own_val: {same_val}")
print(f"Overlap with diff own_val: {diff_val}")
# Of course same val -- the context INCLUDES own_val!
# (L, S, R) with S = own_val. If contexts match, S matches.

print("\n" + "="*70)
print("The proof mechanism is: FIRST NONMOVER = LAST MOVER CONTEXT")
print("="*70)
# In interval I2 (between q's second and first firing), q has value v.
# The first step of I2 has some context (a, v, b) where a, b are neighbor vals.
# The last step of I2 ends at q's first mover step, with context (a', v, b').
# The mover ctx at s1 (first firing) is (a', v, b').
# Is (a', v, b') = some nonmover ctx?
# Yes, if the SAME (a', b') pair appears at some nonmover step in I2.
# The first step of I2: (c, v, d) where c, d are values right after q's second firing.
# The last step BEFORE s1: context may differ due to neighbor changes.
# But the context AT step s1 is the mover context. We need it at some earlier step.

# KEY: The walk in a (1,1) phase TRAVERSES through q.
# When the walk traverses L-to-R: qL fires, then q fires, then qR fires.
#   At q's mover step: qL has ALREADY fired (new value), qR hasn't (old value).
#   After q fires: q changes.
#   Then at qR's nonmover step (before qR fires): ctx at q = (new_qL, new_q, old_qR).
#   But q is nonmover here, and new_qL, new_q are from AFTER q's firing.

# The "traversal return" from BinSCC is the relevant mechanism.
# In a through-walk, the walk passes through q's position.
# The nonmover context at q RIGHT BEFORE q fires = same left neighbor value,
# same right neighbor value, different own value (from before q fired).
# That's NOT the same as the mover context (different own value).
#
# BUT: in the COMPLEMENTARY interval, the same (L, R) pair might appear
# when q has the same own value as the mover context.

# Let me check: is the overlap always between I2 nonmover and s1 mover?
# (same q_val, same interval)

overlap_locations = Counter()  # (s_mover_idx, overlap_in_which_interval) -> count

for word in words:
    configs = build_configs(ms, n, word)
    if configs is None: continue
    if not is_wrap_adjacent(word, n): continue
    L = len(word)

    t_steps = [s for s in range(L) if word[s] == t]
    ft = len(t_steps)
    has_11 = False
    for idx in range(ft):
        k1 = t_steps[idx]
        k2 = t_steps[(idx+1)%ft]
        phase = []
        s = (k1+1)%L
        while s != k2:
            phase.append(s)
            s = (s+1)%L
        J = sum(1 for s in phase if word[s] == bL)
        K = sum(1 for s in phase if word[s] == bR)
        if J == 1 and K == 1:
            has_11 = True
            break
    if not has_11: continue

    q_steps = sorted(s for s in range(L) if word[s] == q)
    if len(q_steps) != 2: continue
    s1, s2 = q_steps

    # Interval I1: (s1, s2) - q has value after s1 fire
    # Interval I2: (s2, s1) - q has value after s2 fire = original value

    # Mover contexts
    mctx1 = (configs[s1][qL], configs[s1][q], configs[s1][qR])
    mctx2 = (configs[s2][qL], configs[s2][q], configs[s2][qR])

    # Check overlap: which mover ctx appears as nonmover, in which interval?
    for s in range(L):
        if word[s] == q: continue
        ctx = (configs[s][qL], configs[s][q], configs[s][qR])
        if ctx == mctx1:
            # mctx1 has q_val = v. Nonmover with q_val=v is in I2.
            in_i1 = False
            ss = (s1+1)%L
            while ss != s2:
                if ss == s: in_i1 = True
                ss = (ss+1)%L
            interval = "I1" if in_i1 else "I2"
            overlap_locations[("s1", interval)] += 1
        if ctx == mctx2:
            in_i1 = False
            ss = (s1+1)%L
            while ss != s2:
                if ss == s: in_i1 = True
                ss = (ss+1)%L
            interval = "I1" if in_i1 else "I2"
            overlap_locations[("s2", interval)] += 1

print("Overlap locations:")
for key, cnt in sorted(overlap_locations.items()):
    print(f"  Mover at {key[0]}, nonmover in {key[1]}: {cnt}")
