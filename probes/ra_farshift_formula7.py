#!/usr/bin/env python3
"""
RA Part 7: Understand why sweep 2 at n=7 fails single-proc shift,
and what the forced-entry bad cycle looks like there.

Also: determine if MULTI-proc shift works, or if we need a different approach.

And critically: what about n>=9? At n=9 single-proc shift works 512/512.
Is n>=9 enough for the Lean theorem (which has hn : sys.rs.n >= 9)?
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
# The Lean theorem has hn : sys.rs.n >= 9
# So we only need n >= 9!
# At n=9, single-proc shift works 512/512.
# Let's verify this is robust and understand the formula.
# ============================================================
print("="*72)
print("FOCUS: n >= 9 (Lean hypothesis)")
print("="*72)

n = 9
ms = [2,3,3,2,3,3,2,3,3]
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

all_combos = list(itertools.product(*[enumerate_state_sequences(ms[p], ms[p]) for p in range(n)]))
all_cfgs = list(itertools.product(*(range(m) for m in ms)))

print(f"n={n}, ms={ms}")
print(f"Sweeps: {len(sweeps)}")
print(f"Combos: {len(all_combos)}")

# For each sweep, show the mover word and identify the shift proc
for wi, (word, _, disp) in enumerate(sweeps):
    print(f"\n  Sweep {wi}: disp={disp:+d}")
    print(f"    Word: {list(word)}")
    # First mover
    first_mover = word[0]
    # Direction: if word[0]->word[1] goes CW (diff=1 mod n), it's CW sweep
    diff01 = (word[1] - word[0]) % n
    direction = "CW" if diff01 == 1 else "CCW"
    print(f"    Start P{first_mover}, direction={direction}")

    # Which ternary proc is adjacent to start and opposite to sweep direction?
    # For CCW sweep (word goes 0,8,7,...), the sweep goes "left" (decreasing)
    # The proc "behind" the start is P1 (one step CW from P0)
    # For CW sweep, the proc behind is the one on the CCW side of start
    if direction == "CCW":
        behind = (first_mover + 1) % n  # CW neighbor
    else:
        behind = (first_mover - 1) % n  # CCW neighbor

    print(f"    Behind proc: P{behind} (m={ms[behind]})")

# ============================================================
# DETAILED: For sweep 0, all combos, which (q, shift) works?
# ============================================================
print(f"\n{'='*72}")
print("DETAILED: All working (q, shift) for sweep 0")
print("="*72)

def test_shift(ms, n, gc_configs, good_set, mcx, q, shift_amount=1):
    ell = len(gc_configs)
    c0 = list(gc_configs[0])
    c0[q] = (c0[q] + shift_amount) % ms[q]
    c0 = tuple(c0)
    if c0 in good_set:
        return None, "overlap_start"
    path = [c0]
    movers = []
    cur = c0
    for step in range(ell + 5):
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
            return None, f"stuck"
        nxt, p = available[0]
        movers.append(p)
        if nxt == c0:
            if len(path) == ell:
                return (path, movers), "success"
            else:
                return None, f"wrong_len_{len(path)}"
        if nxt in set(path):
            return None, "inner_cycle"
        path.append(nxt)
        cur = nxt
    return None, "no_return"

word = sweeps[0][0]

# Check all combos
combo_working = defaultdict(int)
for ci, combo in enumerate(all_combos):
    gc, _ = get_good_cycle_with_combo(ms, n, word, combo)
    gs = set(gc)
    mx = defaultdict(dict)
    for s in range(len(word)):
        p = word[s]
        L = gc[s][(p-1)%n]; S = gc[s][p]; R = gc[s][(p+1)%n]
        mx[p][(L, S, R)] = gc[(s+1)%len(word)][p]

    working = []
    for q in range(n):
        for shift in range(1, ms[q]):
            result, status = test_shift(ms, n, gc, gs, mx, q, shift)
            if result:
                working.append((q, shift))
                combo_working[(q, shift)] += 1
    if ci < 8:
        print(f"  Combo {ci}: {working}")

print(f"\nShift frequency across all {len(all_combos)} combos:")
for (q, sh), cnt in sorted(combo_working.items()):
    pct = 100 * cnt / len(all_combos)
    print(f"  P{q} shift={sh}: {cnt}/{len(all_combos)} ({pct:.0f}%)")

# ============================================================
# KEY QUESTION: Is there one (q, shift) that works for ALL combos
# of a given sweep? If so, which one?
# ============================================================
print(f"\n{'='*72}")
print("KEY: Universal shifts per sweep")
print("="*72)

for wi, (word, _, disp) in enumerate(sweeps):
    universal = {}
    for q in range(n):
        for shift in range(1, ms[q]):
            works_all = True
            for ci, combo in enumerate(all_combos):
                gc, _ = get_good_cycle_with_combo(ms, n, word, combo)
                gs = set(gc)
                mx = defaultdict(dict)
                for s in range(len(word)):
                    p = word[s]
                    L = gc[s][(p-1)%n]; S = gc[s][p]; R = gc[s][(p+1)%n]
                    mx[p][(L, S, R)] = gc[(s+1)%len(word)][p]
                result, _ = test_shift(ms, n, gc, gs, mx, q, shift)
                if not result:
                    works_all = False
                    break
            if works_all:
                universal[(q, shift)] = True

    print(f"  Sweep {wi} (disp={disp:+d}, start=P{word[0]}): universal shifts = {list(universal.keys())}")

# ============================================================
# THE FORMULA: For each sweep, which proc to shift?
# ============================================================
print(f"\n{'='*72}")
print("FORMULA EXTRACTION")
print("="*72)

# From the output above, identify which ternary proc to shift.
# Hypothesis: shift the ternary proc that is:
# - Adjacent to the start proc
# - On the OPPOSITE side from the sweep direction
# E.g., sweep starts at P0 going CCW (0,8,7,...), shift P1 (CW side)

# Let me check this for all 8 sweeps
for wi, (word, _, disp) in enumerate(sweeps):
    first = word[0]
    diff01 = (word[1] - word[0]) % n
    if diff01 == n-1:
        direction = "CCW"
        behind = (first + 1) % n
    else:
        direction = "CW"
        behind = (first - 1) % n

    # Also check: "ahead" proc (in sweep direction)
    if direction == "CCW":
        ahead = (first - 1) % n
    else:
        ahead = (first + 1) % n

    print(f"  Sweep {wi}: start=P{first}, dir={direction}, behind=P{behind}(m={ms[behind]}), ahead=P{ahead}(m={ms[ahead]})")
