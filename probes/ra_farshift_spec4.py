#!/usr/bin/env python3
"""
RA Part 4: Pin down the choice of q (proc to shift) and prove it.

Findings so far:
- CW sweeps: q=P8 (proc n-1), d=1 or 2
- CCW sweeps: q=P6 (a binary proc!), d=1

q is NOT always ternary (P6 is binary at ms[6]=2).
q is NOT always adjacent to the sweep boundary.

Let me investigate what q really is.

For CW sweep: word starts at P0, sweeps CW (0,8,7,6,...,1).
  q=P8 = the first non-starting proc in the sweep direction.

For CCW sweep: word starts at P0, sweeps CCW (0,1,2,...,8).
  q=P6 = a binary proc far from the start.
  But why P6 specifically?

Let me check: do OTHER values of q also work?
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

def follow_forced_orbit(ms, n, c0, forced, good_set, CL):
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
            return None, None, f"SHORT_CYCLE_{len(path)}"
        if cur in set(path): return None, None, "SUBCYCLE"
        path.append(cur)
    return None, None, "TIMEOUT"

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

# ============================================================
# For each sweep word × combo: which (q, d) pairs work?
# ============================================================
print("="*72)
print("EXHAUSTIVE (q, d) search for each sweep word × combo")
print("="*72)

for wi, w in enumerate(valid_words):
    disp = compute_displacement(w, n)
    direction = "CCW" if disp > 0 else "CW"

    # Just use first combo for speed
    combo = tuple(all_combos[p][0] for p in range(n))
    cfgs = build_cycle_with_combo(ms, n, w, combo)
    if cfgs is None: continue
    gs = set(cfgs)
    fe = extract_forced_entries(ms, n, w, cfgs)

    working_qd = []
    for q in range(n):
        for d in range(1, ms[q]):
            c0 = list(cfgs[0])
            c0[q] = (c0[q] + d) % ms[q]
            c0 = tuple(c0)
            if c0 in gs: continue
            path, movers, status = follow_forced_orbit(ms, n, c0, fe, gs, CL)
            if status == "CYCLE" and set(path).isdisjoint(gs):
                working_qd.append((q, d))

    print(f"\n  Word {wi} ({direction}): {list(w)[:15]}...")
    print(f"  Working (q, d): {working_qd}")

    # For each working q: what is the relationship between q and the mover word?
    for q, d in working_qd:
        # When does q appear in the good mover word?
        q_steps = [s for s in range(CL) if w[s] == q]
        # When do q's neighbors appear?
        qL = (q-1) % n
        qR = (q+1) % n
        qL_steps = [s for s in range(CL) if w[s] == qL]
        qR_steps = [s for s in range(CL) if w[s] == qR]
        print(f"    q=P{q} (ms={ms[q]}), d={d}: q fires at steps {q_steps}")
        print(f"      P{qL} fires at steps {qL_steps}")
        print(f"      P{qR} fires at steps {qR_steps}")

        # Is q a "safe" proc? (never mover, never adjacent to mover)
        is_safe = all(abs(w[s] - q) % n > 1 and abs(w[s] - q) % n < n-1 for s in range(CL))
        print(f"      q is safe (never in mover's 3-neighborhood): {is_safe}")

        # Minimum distance from q to any mover in the word
        min_dist = min(min((q - w[s]) % n, (w[s] - q) % n) for s in range(CL))
        print(f"      Min ring distance from q to any mover: {min_dist}")

# ============================================================
# For ALL words × ALL combos: does q=P8 (CW) or q=P6 (CCW) always work?
# ============================================================
print(f"\n{'='*72}")
print("UNIVERSAL: Does fixed (q,d) per direction work for ALL combos?")
print("="*72)

for wi, w in enumerate(valid_words):
    disp = compute_displacement(w, n)
    direction = "CCW" if disp > 0 else "CW"

    q_fixed = 8 if direction == "CW" else 6

    total, success = 0, 0
    all_d_choices = []

    combo_lists = [all_combos[p] for p in range(n)]
    for combo_idx in itertools.product(*[range(len(c)) for c in combo_lists]):
        combo_t = tuple(combo_lists[p][combo_idx[p]] for p in range(n))
        cfgs = build_cycle_with_combo(ms, n, w, combo_t)
        if cfgs is None: continue
        gs = set(cfgs)
        fe = extract_forced_entries(ms, n, w, cfgs)
        total += 1

        found = False
        for d in range(1, ms[q_fixed]):
            c0 = list(cfgs[0])
            c0[q_fixed] = (c0[q_fixed] + d) % ms[q_fixed]
            c0 = tuple(c0)
            if c0 in gs: continue
            path, movers, status = follow_forced_orbit(ms, n, c0, fe, gs, CL)
            if status == "CYCLE" and set(path).isdisjoint(gs):
                success += 1
                all_d_choices.append(d)
                found = True
                break
        if not found:
            print(f"  FAIL: word {wi}, combo {combo_idx}")

    from collections import Counter
    print(f"  Word {wi} ({direction}): {success}/{total} with q=P{q_fixed}")
    if all_d_choices:
        print(f"    d choices: {Counter(all_d_choices)}")

# ============================================================
# DEEPER: Is there a UNIVERSAL q that works for ALL words?
# ============================================================
print(f"\n{'='*72}")
print("CRITICAL: Is there a universal q formula?")
print("="*72)

# The Lean code hypothesizes p with isolated firings.
# The q might be RELATED to p. Let's check.
# Binary procs: P0, P3, P6.
# Isolated firings: a binary proc that fires twice but never consecutively.

# In the CW words (words 0-3): all have P0 firing at steps 0 and 9.
# Mover at step 1 is P8, step 10 is P8 → P0's firings are isolated (P8≠P0).
# So p = P0 has isolated firings.
# q = P8 = (p - 1) mod n = the proc just before p in CW direction.

# In the CCW words (words 4-7): all have P0 firing at steps 0 and 15.
# Mover at step 1 is P1, step 16 is P1 → P0's firings are isolated (P1≠P0).
# So p = P0 has isolated firings.
# q = P6 = ... not obviously related to P0.

# Let me check: for CCW, is P6 the binary proc farthest from P0?
# Binary procs: P0, P3, P6. Distances from P0: P3=3, P6=3.
# P6 = (P0 - 3) mod 9. Hmm.

# Actually: P6 is binary. d=1 means shifting from 0 to 1.
# For binary procs, ms[q]=2, so d=1 is the only choice.
# For ternary, d=1 or d=2.

# For CW: q=P8 is ternary, works with d=1 or d=2.
# For CCW: q=P6 is binary, works with d=1 only.

# REAL QUESTION: Which proc q works for ANY sweep word?
# Let's think about it differently:
# The construction shifts q's value in the starting config.
# For this to produce a valid bad cycle:
# 1. c0 = good_cfg[0] with c0[q] shifted must not be in good_set
# 2. Following forced entries must close back to c0

# Since good_cfg[0] = (0,0,...,0), shifting q means c0[q] = d.
# For d to not create a good config: (0,...,d,...,0) must not be a good config.
# Usually true since good configs have specific patterns.

# KEY INSIGHT: The construction doesn't depend on q being safe (far from movers).
# P6 IS a mover in CCW sweeps (fires at steps like 8, 21, etc.).
# P8 IS a mover in CW sweeps (fires at steps 1, 10, 12).

# So the "far from movers" description in FarShift.lean is WRONG.

print("CRITICAL FINDING:")
print("The 'far from movers' framing in FarShift.lean is INCORRECT.")
print("The shifted proc q IS a mover (appears in the word).")
print("What matters is that the forced entries create a closed orbit.")

# ============================================================
# SIMPLEST SPECIFICATION: Just try all q and d
# For Lean: q and d exist (existential), found by the construction.
# ============================================================

# But for Lean, we need a DETERMINISTIC choice. Can we give one?
# Let me check: for CW, q = (word[0] - 1) mod n = P8.
# For CCW, q = ? Let me look at what's special about P6.

# For CCW word 4: [0,1,2,1,2,3,4,5,4,5,6,7,8,7,8,0,1,2,3,4,5,6,7,8]
# The stutters happen at: 1-2 (P2,P1), 4-5 (P5,P4), 7-8 (P8,P7)
# Wait: stutters = consecutive pairs where direction reverses.
# Looking at the word: 0,1,2,1,2,3,4,5,4,5,6,7,8,7,8,...
# Turnaround at step 2→3: goes 2→1 (down), then 1→2 (up)
# First turnaround involves P1-P2.
# Second turnaround at step 8→9: goes 4→5 (up), then 5→4 (down)... no.

# Actually in CCW: direction = increasing proc indices.
# The stutters (turnarounds) in word 4 occur at:
# step 2: P2 → step 3: P1 (goes down, turnaround)
# step 4: P2 → step 5: P3 (goes up again)
# step 8: P4 → step 9: P5 (continues up)... wait
# step 7: P5 → step 8: P4 (goes down)
# step 9: P5 → step 10: P6 (continues up)
# step 12: P8 → step 13: P7 (goes down)
# step 14: P8 → step 15: P0 (wraps)

# The turnaround points (local minima) are where the sweep reverses.
# For a stuttered sweep, there are multiple turnarounds.

# Let me just check: does q=P6 relate to the binary proc p with isolated firings?
# In the Lean theorem, p is a binary proc with isolated firings.
# p = P0 has isolated firings in CCW words.
# q = P6. How is P6 related to P0?
# P6 is the binary proc at distance 3 CCW from P0 (6 = 0-3 mod 9).

# Actually, let me check if P3 or P0 also works for CCW:
w = valid_words[4]  # CCW
combo = tuple(all_combos[p][0] for p in range(n))
cfgs = build_cycle_with_combo(ms, n, w, combo)
gs = set(cfgs)
fe = extract_forced_entries(ms, n, w, cfgs)

print(f"\nWord 4 (CCW): {list(w)}")
for q in range(n):
    for d in range(1, ms[q]):
        c0 = list(cfgs[0])
        c0[q] = (c0[q] + d) % ms[q]
        c0 = tuple(c0)
        if c0 in gs: continue
        path, movers, status = follow_forced_orbit(ms, n, c0, fe, gs, CL)
        if status == "CYCLE":
            ok = set(path).isdisjoint(gs)
            print(f"  q=P{q}, d={d}: {status}, len={len(path)}, disjoint={ok}")
        elif status != "STUCK":
            print(f"  q=P{q}, d={d}: {status}")

# ============================================================
# FINAL SPEC: The construction uses an EXISTENTIAL q.
# For any sweep good cycle with ≥3 non-consecutive binary and
# isolated firings at some binary proc, THERE EXISTS q and d such
# that the forced-entry orbit from shifting q by d produces a
# valid bad cycle of length CL.
#
# The Lean proof structure should be:
# 1. Show that the forced entries from the good cycle determine a
#    transition function on the set of configs adjacent to good configs.
# 2. Show that this function has a fixed point (cycle) of length CL.
# 3. Show this cycle is disjoint from good configs.
#
# Actually, a cleaner approach: define the bad cycle EXISTENTIALLY.
# We don't need to give q explicitly. We just need to show existence.
# But for Lean, we need a concrete witness...
# ============================================================

# ============================================================
# ALTERNATIVE: Safe proc shift (the original FarShift idea)
# Is there ALWAYS a proc that is safe (far from all movers)?
# ============================================================
print(f"\n{'='*72}")
print("SAFE PROC CHECK: Is there a proc far from ALL movers?")
print("="*72)

for wi, w in enumerate(valid_words):
    disp = compute_displacement(w, n)
    direction = "CCW" if disp > 0 else "CW"

    for q in range(n):
        # Check: is q at distance ≥ 2 from every mover at every step?
        safe = True
        for s in range(CL):
            p = w[s]
            dist = min((q - p) % n, (p - q) % n)
            if dist < 2:
                safe = False
                break
        if safe:
            print(f"  Word {wi} ({direction}): P{q} is safe (dist≥2 from all movers)")
            break
    else:
        print(f"  Word {wi} ({direction}): NO safe proc exists!")

# ============================================================
# TRULY SAFE: dist ≥ 2 from EVERY mover (not just from shifted proc)
# If a safe proc exists, shifting it by +1 preserves ALL contexts.
# This is the CLEAN version.
# ============================================================
print(f"\n{'='*72}")
print("TRULY SAFE (dist≥2): Does shifting preserve ALL contexts?")
print("="*72)

for wi, w in enumerate(valid_words):
    disp = compute_displacement(w, n)
    direction = "CCW" if disp > 0 else "CW"
    combo = tuple(all_combos[p][0] for p in range(n))
    cfgs = build_cycle_with_combo(ms, n, w, combo)
    if cfgs is None: continue
    gs = set(cfgs)

    for q in range(n):
        safe = True
        for s in range(CL):
            p = w[s]
            dist = min((q - p) % n, (p - q) % n)
            if dist < 2:
                safe = False
                break
        if not safe: continue

        for d in range(1, ms[q]):
            # Shift q by d
            c0 = list(cfgs[0])
            c0[q] = (c0[q] + d) % ms[q]
            c0 = tuple(c0)
            if c0 in gs: continue

            # Check: does the shifted cycle have same movers and contexts?
            bad_cfgs = []
            for s in range(CL):
                bc = list(cfgs[s])
                bc[q] = (bc[q] + d) % ms[q]
                bad_cfgs.append(tuple(bc))

            # Check that movers match and contexts match
            all_match = True
            for s in range(CL):
                p = w[s]
                # Good context
                gc = cfgs[s]
                gL = gc[(p-1)%n]; gS = gc[p]; gR = gc[(p+1)%n]
                # Bad context
                bc = bad_cfgs[s]
                bL = bc[(p-1)%n]; bS = bc[p]; bR = bc[(p+1)%n]
                if (gL, gS, gR) != (bL, bS, bR):
                    all_match = False
                    break

            if all_match:
                disjoint = all(bc not in gs for bc in bad_cfgs)
                distinct = len(set(bad_cfgs)) == CL
                closed = True  # same movers same contexts → same transitions → closed
                print(f"  Word {wi} ({direction}): q=P{q} d={d} SAFE SHIFT WORKS! disjoint={disjoint} distinct={distinct}")
            else:
                print(f"  Word {wi} ({direction}): q=P{q} d={d} contexts DON'T match (should be impossible)")

# ============================================================
# hno_safe hypothesis check
# ============================================================
print(f"\n{'='*72}")
print("hno_safe check: The Lean theorem ASSUMES no safe proc exists.")
print("If a safe proc exists, a simpler argument applies.")
print("="*72)
print("So FarShift handles the case where NO proc has dist≥2 from ALL movers.")
print("In this case, the construction must use a proc that IS in some mover's neighborhood.")
print("This is why the construction is subtle — the shift changes some contexts,")
print("and the bad cycle follows forced entries through DIFFERENT movers.")
