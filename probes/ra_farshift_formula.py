#!/usr/bin/env python3
"""
RA: Extract the exact bad-cycle formula for FarShift.lean sorry 6.

Key idea from the Lean file: for a sweep good cycle with non-consecutive binary,
if processor q is "far" from all movers (dist >= 2 at every step), then shifting
q's value by +1 mod m_q gives a bad cycle with identical mover contexts.

This script:
1. Extracts good cycle + forced bad cycle for concrete example
2. Tests the "single far-proc shift" hypothesis
3. Verifies all BadCycleData properties
4. Tests universality across all sweeps x combos
"""

import itertools
from collections import defaultdict

# ============================================================
# Core utilities
# ============================================================

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
    """Build good cycle configs for given mover word and state-sequence combo."""
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

def ring_dist(a, b, n):
    """Minimum distance on ring of size n."""
    d = abs(a - b) % n
    return min(d, n - d)

# ============================================================
# PART 1: Extract good + bad cycle for one concrete example
# ============================================================
print("=" * 72)
print("PART 1: Concrete example at n=9")
print("=" * 72)

n = 9
ms = [2,3,3,2,3,3,2,3,3]
target_fc = {p: ms[p] for p in range(n)}

# Get sweep mover words
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
print(f"Found {len(sweeps)} sweep cycles")

# Use first sweep, first combo
w0, _, d0 = sweeps[0]
ell = len(w0)
combo0 = tuple(enumerate_state_sequences(ms[p], ms[p])[0] for p in range(n))
gc_configs, fc_num = get_good_cycle_with_combo(ms, n, w0, combo0)
good_set = set(gc_configs)

print(f"Mover word: {list(w0)}")
print(f"Cycle length: {ell}")
print(f"Combo: {combo0}")

# ============================================================
# PART 1a: Find "far" processors at each step
# ============================================================
print(f"\n--- Far processor analysis ---")
for s in range(ell):
    p = w0[s]
    far = [q for q in range(n) if ring_dist(p, q, n) >= 2]
    print(f"  Step {s:2d}: mover=P{p}, far procs={far}")

# Which procs are far from ALL movers at ALL steps?
always_far = []
for q in range(n):
    if all(ring_dist(w0[s], q, n) >= 2 for s in range(ell)):
        always_far.append(q)
print(f"\nProcs far from ALL movers at ALL steps: {always_far}")
# This will be empty for sweeps (movers visit all procs)

# Which procs are far from the mover at EACH step?
# For each step, the mover is w0[s], and procs at dist >= 2 are "safe to shift"
# The key insight: we don't need q to be far at ALL steps,
# just at the steps where the mover is near q!
# Actually for the shift to work, we need q to be far from the mover at EVERY step.
# Since it's a sweep, the mover visits every proc, so no proc is always far.

# BUT WAIT — the Lean file says "no safe proc" (hno_safe). So the construction
# must work even without a globally-far proc. Let me re-read the Lean...
# The Lean says:
#   hno_safe : ¬∃ q, ∀ k, mover(k) ≠ q ∧ mover(k) ≠ left(q) ∧ mover(k) ≠ right(q)
# So hno_safe says there is NO safe processor (no proc always at dist ≥ 2).
# Yet the construction still works! So it must be something else.

# Let me re-examine: the forced-entry approach from the previous RA.
# The previous RA found a bad cycle by:
# 1. Building the transition table from forced entries
# 2. Finding a cycle in the forced-entry graph among non-good configs
# This is more general than a simple shift.

# Let me try the SHIFT approach first and see if it works.
print(f"\n--- Testing single-proc shift ---")
for q in range(n):
    # Shift proc q by +1 mod m_q
    shifted = []
    for s in range(ell):
        c = list(gc_configs[s])
        c[q] = (c[q] + 1) % ms[q]
        shifted.append(tuple(c))

    # Check disjoint
    disjoint = all(c not in good_set for c in shifted)
    # Check distinct
    distinct = len(set(shifted)) == ell

    # Check privilege + step
    priv_ok = True
    step_ok = True
    for s in range(ell):
        p = w0[s]
        gc_c = gc_configs[s]
        sh_c = shifted[s]

        # Mover context at good config
        gc_L = gc_c[(p-1)%n]; gc_S = gc_c[p]; gc_R = gc_c[(p+1)%n]
        # Mover context at shifted config
        sh_L = sh_c[(p-1)%n]; sh_S = sh_c[p]; sh_R = sh_c[(p+1)%n]

        # For privilege: need same (L,S,R) context (so same privilege)
        # Context is preserved iff q is not in {p-1, p, p+1} mod n
        if sh_L != gc_L or sh_S != gc_S or sh_R != gc_R:
            priv_ok = False
            break

        # For step: firing p at shifted[s] should give shifted[s+1]
        # Since context is identical, transition gives same result
        # So shifted[s+1] should equal shifted[s] with p fired
        gc_next = gc_configs[(s+1) % ell]
        sh_next = shifted[(s+1) % ell]
        # The mover p gets the same new value as in good cycle
        fired = list(sh_c)
        fired[p] = gc_next[p]  # Same transition result
        # But wait: if q == p, the shift affects the mover!
        # Actually: fired[p] should be the transition result at (sh_L, sh_S, sh_R)
        # Since (sh_L, sh_S, sh_R) == (gc_L, gc_S, gc_R), result is same
        fired = tuple(fired)
        if fired != sh_next:
            step_ok = False
            break

    status = "GOOD" if (disjoint and distinct and priv_ok and step_ok) else ""
    if not disjoint: status = "overlap"
    elif not priv_ok: status = "priv_fail"
    elif not step_ok: status = "step_fail"
    elif not distinct: status = "dup"

    print(f"  Shift P{q} (m={ms[q]}): disjoint={disjoint} priv={priv_ok} step={step_ok} distinct={distinct} [{status}]")

# ============================================================
# PART 1b: More careful shift analysis
# ============================================================
print(f"\n--- Multi-proc shift analysis ---")
# Try shifting multiple procs. For each subset of procs, shift all by +1.
# But that's 2^9 = 512 subsets. Let's try all single + some doubles.

# First, let's understand WHY single-proc shift fails.
# For a sweep, every proc is a mover at some step. When proc q is the mover,
# shifting q changes S in the context (L, S, R). This changes:
# 1. Whether q is privileged (S might differ from L or R differently)
# 2. The transition result (S' depends on S)
# So shifting the mover position breaks things.

# KEY INSIGHT: What if we shift q by an amount that preserves privilege?
# For a binary proc (m=2), shifting by +1 flips 0<->1.
# For a ternary proc (m=3), shifting by +1 gives 0->1->2->0.

# Actually, let me think about this differently.
# The previous RA said the bad cycle has 11 different offsets (not constant).
# Let me extract the ACTUAL bad cycle from forced entries and compare.

print(f"\n{'='*72}")
print("PART 2: Extract forced-entry bad cycle")
print("=" * 72)

# Build transition table from good cycle's mover entries
mcx = defaultdict(dict)
for s in range(ell):
    p = w0[s]
    L = gc_configs[s][(p-1)%n]; S = gc_configs[s][p]; R = gc_configs[s][(p+1)%n]
    mcx[p][(L, S, R)] = gc_configs[(s+1)%ell][p]

print(f"Forced mover entries: {sum(len(v) for v in mcx.values())}")
for p in sorted(mcx.keys()):
    print(f"  P{p} (m={ms[p]}): {dict(mcx[p])}")

# Find all non-good configs with forced privilege
all_cfgs = list(itertools.product(*(range(m) for m in ms)))
forced_adj = defaultdict(list)
for c in all_cfgs:
    if c in good_set: continue
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        if (L, S, R) in mcx[p]:
            Sp = mcx[p][(L, S, R)]
            if Sp != S:
                nc = list(c); nc[p] = Sp; nc = tuple(nc)
                if nc not in good_set:
                    forced_adj[c].append((nc, p))

# Find trap (iterative sink removal)
trap = set(c for c in forced_adj if forced_adj[c])
changed = True
while changed:
    changed = False
    to_remove = set()
    for c in trap:
        if not any(nc in trap for nc, p in forced_adj[c]):
            to_remove.add(c)
    if to_remove:
        trap -= to_remove
        changed = True

print(f"Trap size: {len(trap)}")

# BFS for cycle from a trap config
start = next(iter(trap))
visited = {start: ([], [])}
queue = [start]
bad_cycle = None
bad_movers = None
while queue:
    cur = queue.pop(0)
    for nxt, p in forced_adj[cur]:
        if nxt == start and visited[cur][0]:
            path = visited[cur][0] + [cur]
            movers = visited[cur][1] + [p]
            if bad_cycle is None or len(path) < len(bad_cycle):
                bad_cycle = path
                bad_movers = movers
            break
        if nxt in trap and nxt not in visited:
            visited[nxt] = (visited[cur][0] + [cur], visited[cur][1] + [p])
            if len(visited[nxt][0]) < 50:
                queue.append(nxt)

print(f"Bad cycle length: {len(bad_cycle)}")
print(f"Bad movers: {bad_movers}")
print(f"Good movers: {list(w0)}")
print(f"Movers match: {bad_movers == list(w0)}")

# ============================================================
# PART 2a: Compare bad cycle to good cycle — extract offset
# ============================================================
print(f"\n--- Offset analysis ---")
for s in range(min(ell, len(bad_cycle))):
    gc = gc_configs[s]
    bc = bad_cycle[s]
    offset = tuple((b - g) % m for g, b, m in zip(gc, bc, ms))
    print(f"  Step {s:2d}: good={gc} bad={bc} offset={offset} mover=P{w0[s]}/P{bad_movers[s]}")

offsets = [tuple((b - g) % m for g, b, m in zip(gc_configs[s], bad_cycle[s], ms)) for s in range(len(bad_cycle))]
unique_offsets = set(offsets)
print(f"\nUnique offsets: {len(unique_offsets)}")
for o in sorted(unique_offsets):
    count = offsets.count(o)
    print(f"  {o} appears {count} times")

# ============================================================
# PART 3: Try the "far shift" approach properly
# ============================================================
print(f"\n{'='*72}")
print("PART 3: Far-shift approach (shift q at steps where q is far)")
print("=" * 72)

# The idea: don't shift q at ALL steps. Only shift q by a fixed amount,
# but the shift is ALWAYS present (constant offset at position q).
# For this to work: at every step s, when mover is p = w0[s],
# we need q NOT in {p-1, p, p+1} mod n.
#
# For a sweep, every proc appears as mover, so there's no proc that's
# always far. BUT: what if we shift a proc q at steps where q ISN'T the mover
# or the mover's neighbor, and DON'T shift at steps where q IS the mover?
#
# That gives a NON-constant offset: d[s] has d_q = 1 when far, d_q = 0 when near.
# This is what the previous RA found (11 different offsets = non-constant).
#
# BUT WAIT: if the offset changes between steps, we need to verify that
# the transition ALSO produces the correct next offset. This is subtle.
#
# Let me instead try a COMPLETELY different approach: the actual "far shift"
# construction from the Lean docstring.

# Actually, let me re-read the Lean more carefully.
# It says "shifting a ternary processor q that is far from all movers (dist >= 2
# at every step)". But we just showed no such proc exists for sweeps!
#
# UNLESS: the Lean uses a weaker notion. Let me check if hno_safe is an
# assumption (ruling out the safe-proc case) or a consequence.
#
# Looking at the Lean: hno_safe is a HYPOTHESIS of the theorem.
# So the theorem ASSUMES there's no safe proc, and still constructs a bad cycle.
# This means the construction works WITHOUT a globally-far proc.
#
# So what IS the construction? Let me think about this from scratch.

# The previous RA found that the bad cycle uses ONLY forced mover entries.
# These are the entries f_p(L,S,R) that the good cycle forces.
# The bad cycle reuses these same entries at non-good configs.
#
# The key question: is the bad cycle a CONSTANT offset of the good cycle?
# If so, the formula is simple: bad[s] = good[s] + d (mod ms).

# Let me check if there EXISTS a constant offset d that works.
print("Testing all constant offsets d...")
all_ms_vals = [list(range(m)) for m in ms]
found_good_d = []

# For each possible d (excluding all-zero):
# We need: for each step s with mover p:
# 1. (good[s] + d) not in good_set
# 2. Mover p privileged at (good[s] + d) — needs same (L,S,R) or equiv privilege
# 3. Firing p at (good[s]+d) gives (good[s+1]+d)
# 4. All (good[s]+d) distinct

# Condition 3 requires: the transition at p with context
#   (good_L + d_{p-1}, good_S + d_p, good_R + d_{p+1}) mod ms
# gives (good_S' + d_p) mod ms[p], where good_S' = result of firing at good config.
#
# Since transition is f_p(L,S,R) (from the table), we need:
#   f_p(L+d_{p-1}, S+d_p, R+d_{p+1}) = f_p(L,S,R) + d_p  (mod ms[p])
# where f is the forced entry value.

# Let me check this for all possible d:
total_configs = 1
for m in ms:
    total_configs *= m
print(f"Total possible offsets: {total_configs - 1}")

# Too many (23327). Let me check structured offsets.
# First: offsets where d_p = 0 for all binary p (since shifting binary is flip)
# and d_p ∈ {0,1,2} for ternary p.
# Binary positions: 0, 3, 6
binary_pos = [p for p in range(n) if ms[p] == 2]
ternary_pos = [p for p in range(n) if ms[p] == 3]
print(f"Binary positions: {binary_pos}")
print(f"Ternary positions: {ternary_pos}")

valid_offsets = []
# Try: shift only at ternary positions
for shifts in itertools.product(*[range(ms[p]) for p in range(n)]):
    d = list(shifts)
    if all(d[p] == 0 for p in range(n)):
        continue  # Skip zero offset

    # Build shifted configs
    shifted = []
    for s in range(ell):
        c = tuple((gc_configs[s][p] + d[p]) % ms[p] for p in range(n))
        shifted.append(c)

    # Check disjoint
    if any(c in good_set for c in shifted):
        continue

    # Check distinct
    if len(set(shifted)) != ell:
        continue

    # Check privilege + step (mover context must match)
    ok = True
    for s in range(ell):
        p = w0[s]
        gc_c = gc_configs[s]
        sh_c = shifted[s]
        gc_L = gc_c[(p-1)%n]; gc_S = gc_c[p]; gc_R = gc_c[(p+1)%n]
        sh_L = sh_c[(p-1)%n]; sh_S = sh_c[p]; sh_R = sh_c[(p+1)%n]

        # Check if shifted context is in the forced table
        if (sh_L, sh_S, sh_R) not in mcx[p]:
            ok = False
            break

        # Check step: firing p at shifted[s] should give shifted[s+1]
        sh_next_p = mcx[p][(sh_L, sh_S, sh_R)]
        expected_next = shifted[(s+1) % ell]
        actual_next = list(sh_c)
        actual_next[p] = sh_next_p
        if tuple(actual_next) != expected_next:
            ok = False
            break

    if ok:
        valid_offsets.append(tuple(d))

print(f"\nValid constant offsets: {len(valid_offsets)}")
for d in valid_offsets[:20]:
    print(f"  d = {d}")

# ============================================================
# PART 4: Is the BFS bad cycle one of these constant offsets?
# ============================================================
if valid_offsets:
    print(f"\n--- Checking if BFS bad cycle matches a constant offset ---")
    for d in valid_offsets:
        shifted = [tuple((gc_configs[s][p] + d[p]) % ms[p] for p in range(n)) for s in range(ell)]
        if set(shifted) == set(bad_cycle):
            print(f"  MATCH: d = {d}")
            # Check if ordering matches too
            if shifted == bad_cycle:
                print(f"    Exact ordering match!")
            else:
                # Find rotation
                for rot in range(ell):
                    if shifted[rot:] + shifted[:rot] == bad_cycle:
                        print(f"    Ordering match with rotation {rot}")
                        break

# ============================================================
# PART 5: Universal verification across all sweeps x combos
# ============================================================
print(f"\n{'='*72}")
print("PART 5: Universal verification")
print("=" * 72)

# For each sweep word, for each combo, check if valid constant offsets exist
all_combos = list(itertools.product(*[enumerate_state_sequences(ms[p], ms[p]) for p in range(n)]))
print(f"Sweeps: {len(sweeps)}, Combos per sweep: {len(all_combos)}")

universal_offsets = None  # offsets that work for ALL sweeps x combos
total_tests = 0
all_pass = True

for wi, (word, _, disp) in enumerate(sweeps):
    for ci, combo in enumerate(all_combos):
        gc, fc = get_good_cycle_with_combo(ms, n, word, combo)
        gs = set(gc)

        # Build forced entries for this combo
        mx = defaultdict(dict)
        for s in range(ell):
            p = word[s]
            L = gc[s][(p-1)%n]; S = gc[s][p]; R = gc[s][(p+1)%n]
            mx[p][(L, S, R)] = gc[(s+1)%ell][p]

        # Test each valid offset from Part 3
        combo_valid = set()
        for d in valid_offsets:
            shifted = [tuple((gc[s][p] + d[p]) % ms[p] for p in range(n)) for s in range(ell)]

            if any(c in gs for c in shifted):
                continue
            if len(set(shifted)) != ell:
                continue

            ok = True
            for s in range(ell):
                p = word[s]
                sh_c = shifted[s]
                sh_L = sh_c[(p-1)%n]; sh_S = sh_c[p]; sh_R = sh_c[(p+1)%n]
                if (sh_L, sh_S, sh_R) not in mx[p]:
                    ok = False
                    break
                sh_next_p = mx[p][(sh_L, sh_S, sh_R)]
                expected_next = shifted[(s+1) % ell]
                actual_next = list(sh_c)
                actual_next[p] = sh_next_p
                if tuple(actual_next) != expected_next:
                    ok = False
                    break

            if ok:
                combo_valid.add(d)

        if not combo_valid:
            print(f"  FAIL: sweep {wi}, combo {ci} — no valid constant offset!")
            all_pass = False
        else:
            if universal_offsets is None:
                universal_offsets = combo_valid
            else:
                universal_offsets &= combo_valid

        total_tests += 1

print(f"Total tests: {total_tests}")
print(f"All pass: {all_pass}")
if universal_offsets:
    print(f"Offsets valid for ALL sweeps x combos: {len(universal_offsets)}")
    for d in sorted(universal_offsets):
        print(f"  d = {d}")
else:
    print(f"No universal offset across all sweeps x combos")
    # Check per-sweep universality
    print(f"\nPer-sweep analysis:")
    for wi, (word, _, disp) in enumerate(sweeps):
        sweep_offsets = None
        for ci, combo in enumerate(all_combos):
            gc, fc = get_good_cycle_with_combo(ms, n, word, combo)
            gs = set(gc)
            mx = defaultdict(dict)
            for s in range(ell):
                p = word[s]
                L = gc[s][(p-1)%n]; S = gc[s][p]; R = gc[s][(p+1)%n]
                mx[p][(L, S, R)] = gc[(s+1)%ell][p]

            combo_valid = set()
            for d in valid_offsets:
                shifted = [tuple((gc[s][p] + d[p]) % ms[p] for p in range(n)) for s in range(ell)]
                if any(c in gs for c in shifted): continue
                if len(set(shifted)) != ell: continue
                ok = True
                for s in range(ell):
                    p = word[s]
                    sh_c = shifted[s]
                    sh_L = sh_c[(p-1)%n]; sh_S = sh_c[p]; sh_R = sh_c[(p+1)%n]
                    if (sh_L, sh_S, sh_R) not in mx[p]:
                        ok = False; break
                    sh_next_p = mx[p][(sh_L, sh_S, sh_R)]
                    expected_next = shifted[(s+1) % ell]
                    actual_next = list(sh_c); actual_next[p] = sh_next_p
                    if tuple(actual_next) != expected_next:
                        ok = False; break
                if ok: combo_valid.add(d)

            if sweep_offsets is None:
                sweep_offsets = combo_valid
            else:
                sweep_offsets &= combo_valid

        print(f"  Sweep {wi}: {len(sweep_offsets) if sweep_offsets else 0} universal offsets")
        if sweep_offsets:
            for d in sorted(sweep_offsets)[:5]:
                print(f"    d = {d}")
