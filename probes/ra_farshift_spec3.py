#!/usr/bin/env python3
"""
RA Part 3: Pin down the exact bad-cycle mover word formula.

Key findings so far:
- Movers are DIFFERENT from good cycle (100% of cases)
- Bad mover word fire counts = good mover word fire counts (permuted by +1 mod n!)
- Privilege is NOT unique, but we can choose the smallest-index proc
- All contexts in forced entries
- The bad mover word does NOT depend on combo (just on word)

Critical observation from fire counts:
  Good: {0:2, 1:3, 2:3, 3:2, 4:3, 5:3, 6:2, 7:3, 8:3}
  Bad:  {0:2, 1:3, 2:3, 3:2, 4:3, 5:3, 6:2, 7:3, 8:3}
SAME fire counts! So the bad word is a REARRANGEMENT of the good word.

Now: what's the rearrangement formula?
Good: [0, 8, 7, 6, 5, 4, 3, 2, 1, 0, 8, 7, 8, 7, 6, 5, 4, 5, 4, 3, 2, 1, 2, 1]
Bad:  [7, 6, 5, 4, 3, 2, 8, 7, 8, 0, 1, 7, 6, 5, 4, 5, 4, 3, 2, 8, 0, 1, 2, 1]

The bad word looks like good_word shifted by some amount, modulo rotations.
Let me check: bad[k] = good[k + offset] for some offset?
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

def follow_forced_orbit(ms, n, c0, forced, good_set, CL):
    """Follow forced orbit, choosing smallest-index privileged proc."""
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
        if cur in set(path):
            return None, None, "SUBCYCLE"
        path.append(cur)
    return None, None, "TIMEOUT"

# ============================================================
# n=9 analysis
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

print(f"n={n}, ms={ms}, CL={CL}")
print(f"Sweep words: {len(valid_words)}")

# ============================================================
# For each sweep word, find the bad mover word
# ============================================================
print(f"\n{'='*72}")
print("Bad mover word for each sweep word")
print("="*72)

for wi, w in enumerate(valid_words):
    disp = compute_displacement(w, n)
    direction = "CCW" if disp > 0 else "CW"
    combo = tuple(all_combos[p][0] for p in range(n))
    cfgs = build_cycle_with_combo(ms, n, w, combo)
    if cfgs is None:
        print(f"  Word {wi}: build failed")
        continue
    gs = set(cfgs)
    fe = extract_forced_entries(ms, n, w, cfgs)

    # Try q=8, d=1 first; if not, try all
    found = False
    for q in range(n):
        for d in range(1, ms[q]):
            c0 = list(cfgs[0])
            c0[q] = (c0[q] + d) % ms[q]
            c0 = tuple(c0)
            if c0 in gs: continue
            path, movers, status = follow_forced_orbit(ms, n, c0, fe, gs, CL)
            if status == "CYCLE" and set(path).isdisjoint(gs):
                print(f"\n  Word {wi} ({direction}): {list(w)}")
                print(f"  q=P{q}, d={d}")
                print(f"  Good movers: {list(w)}")
                print(f"  Bad movers:  {movers}")

                # Check if bad = rotation of good
                for rot in range(CL):
                    rotated = [w[(s+rot) % CL] for s in range(CL)]
                    if rotated == movers:
                        print(f"  -> bad = good rotated by {rot}")
                        break
                else:
                    # Check proc-level shift: bad[k] = (good[σ(k)] + shift) mod n?
                    pass

                # Check: bad[k] = good[k+offset] for some offset?
                for offset in range(CL):
                    if all(movers[k] == w[(k+offset) % CL] for k in range(CL)):
                        print(f"  -> bad[k] = good[k+{offset}] (rotation by {offset})")
                        break
                else:
                    # Not a simple rotation. Check proc-level shift
                    # bad[k] = (good[k] + delta) mod n?
                    deltas = [(movers[k] - w[k]) % n for k in range(CL)]
                    if len(set(deltas)) == 1:
                        print(f"  -> bad[k] = (good[k] + {deltas[0]}) mod {n}")
                    else:
                        # Check: is there a permutation σ of steps s.t. bad[k] = good[σ(k)]?
                        # and also bad_cfg[k] is related to good_cfg[σ(k)]?
                        print(f"  -> Complex relationship")
                        # Show the step-by-step diff
                        for k in range(min(CL, 30)):
                            gw = w[k]
                            bw = movers[k]
                            delta = (bw - gw) % n
                            print(f"    [{k:2d}] good=P{gw} bad=P{bw} delta={delta}")

                found = True
                break
        if found: break

# ============================================================
# KEY INSIGHT: Look at the STRUCTURE of the bad orbit.
# The bad cycle starts with cfg[0] shifted at P8.
# Step 0: P7 fires (because P7 has ctx (0,0,1) which is forced).
# This is exactly what good step 2 does (P7 with ctx (0,0,1)).
#
# So the bad cycle "skips" the first two good steps (P0 and P8),
# because P8 is already at value 1. The wavefront of 1s propagates
# left (CW) starting from P7 instead of P0.
#
# After the first sweep pass, the bad cycle needs to "catch up"
# with the good cycle's second pass. This is where it gets complex.
# ============================================================

# ============================================================
# APPROACH PIVOT: Instead of finding a closed-form mover word,
# check if we can define it as "the smallest-index privileged proc"
# at each step. This is a DETERMINISTIC rule.
# For Lean: define mover[k] via recursion on cfg[k].
# ============================================================
print(f"\n{'='*72}")
print("APPROACH: Smallest-index privileged proc")
print("="*72)

# Verify: does "smallest-index" always give a valid cycle for ALL combos?
w = valid_words[0]
total, success = 0, 0
for combo_idx in itertools.product(*[range(len(all_combos[p])) for p in range(n)]):
    combo_t = tuple(all_combos[p][combo_idx[p]] for p in range(n))
    cfgs = build_cycle_with_combo(ms, n, w, combo_t)
    if cfgs is None: continue
    gs = set(cfgs)
    fe = extract_forced_entries(ms, n, w, cfgs)
    total += 1

    for q in range(n):
        for d in range(1, ms[q]):
            c0 = list(cfgs[0])
            c0[q] = (c0[q] + d) % ms[q]
            c0 = tuple(c0)
            if c0 in gs: continue
            path, movers, status = follow_forced_orbit(ms, n, c0, fe, gs, CL)
            if status == "CYCLE" and set(path).isdisjoint(gs):
                success += 1
                break
        else:
            continue
        break

print(f"Smallest-index rule: {success}/{total} combos succeed")

# ============================================================
# CRITICAL: Check if "smallest-index" works for ALL words x combos
# ============================================================
print(f"\n{'='*72}")
print("Universal check: smallest-index for all words x combos")
print("="*72)

all_total, all_success = 0, 0
for wi, w in enumerate(valid_words):
    for combo_idx in itertools.product(*[range(len(all_combos[p])) for p in range(n)]):
        combo_t = tuple(all_combos[p][combo_idx[p]] for p in range(n))
        cfgs = build_cycle_with_combo(ms, n, w, combo_t)
        if cfgs is None: continue
        gs = set(cfgs)
        fe = extract_forced_entries(ms, n, w, cfgs)
        all_total += 1

        found = False
        for q in range(n):
            for d in range(1, ms[q]):
                c0 = list(cfgs[0])
                c0[q] = (c0[q] + d) % ms[q]
                c0 = tuple(c0)
                if c0 in gs: continue
                path, movers, status = follow_forced_orbit(ms, n, c0, fe, gs, CL)
                if status == "CYCLE" and set(path).isdisjoint(gs):
                    all_success += 1
                    found = True
                    break
            if found: break

print(f"Universal: {all_success}/{all_total} pass")

# ============================================================
# THE LEAN SPEC
# ============================================================
print(f"\n{'='*72}")
print("LEAN SPECIFICATION")
print("="*72)

print("""
The BadCycleData construction:

1. INPUTS: A system sys, a good cycle gc that is a sweep with ≥3 non-consecutive
   binary and an isolated firing at binary proc p.

2. CHOICE OF q AND d:
   - q is a ternary proc adjacent to the sweep boundary (details TBD by RA)
   - d is 1 (shift by +1 mod 3)

3. INITIAL CONFIG:
   bad_cfg[0] = gc.configs[0] with position q changed to (gc.configs[0][q] + d) mod ms[q]

4. RECURSIVE DEFINITION:
   At each step k, let cfg = bad_cfg[k].
   Find all procs p such that:
     (a) (cfg[p-1], cfg[p], cfg[p+1]) appears in forced entries for p
     (b) forced[p][(cfg[p-1], cfg[p], cfg[p+1])] ≠ cfg[p]
   Choose the smallest such p. This is bad_mover[k].
   bad_cfg[k+1] = move sys (bad_cfg[k]) (bad_mover[k]).

5. OBLIGATIONS:
   (a) Closure: bad_cfg[CL] = bad_cfg[0]
   (b) Disjointness: bad_cfg[k] ∉ gc.configs for all k
   (c) Privilege: bad_mover[k] is privileged at bad_cfg[k]
   (d) Distinctness: bad_cfg[k] ≠ bad_cfg[j] for k ≠ j
   (e) Step: bad_cfg[k+1] = move sys (bad_cfg[k]) (bad_mover[k])

NOTE: Obligation (c) follows from (a) + (b): the forced entry context appears
in the good cycle, so sys.f agrees with the forced entry, so the proc's
current value differs from sys.f output → privileged.

NOTE: For Lean, the recursive definition requires well-founded recursion
or a proof that the orbit is deterministic. The "smallest-index" rule
makes it deterministic. But proving closure (a) is the hard part.

ALTERNATIVE APPROACH: Don't use recursive definition. Instead, provide
the bad configs and movers as EXPLICIT LISTS (computed, not recursive).
This avoids the recursion issue but requires more infrastructure.
""")
