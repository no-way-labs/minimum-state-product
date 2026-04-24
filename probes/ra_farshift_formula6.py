#!/usr/bin/env python3
"""
RA Part 6: The formula.

Finding: Shift the binary proc that is FARTHEST from the first mover in the
good cycle. At n=7 with ms=[2,3,3,2,3,3,2], the first mover is P0 and
the farthest binary proc is P6 (dist=1 on ring, but P3 is dist=3).

Wait, P6 is distance 1 from P0, not the farthest. Let me re-examine.

Actually the key might be: shift the LAST binary proc that fires before
the sweep reverses direction. Or: shift any binary proc that's at distance >= 2
from the INITIAL mover.

Let me just test all procs systematically at both n=7 and n=9 to find the rule.
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

def ring_dist(a, b, n):
    d = abs(a - b) % n
    return min(d, n - d)

def test_shift(ms, n, gc_configs, good_set, mcx, q, shift_amount=1):
    """Test if shifting proc q by shift_amount gives a valid bad cycle."""
    ell = len(gc_configs)

    # Shifted starting config
    c0 = list(gc_configs[0])
    c0[q] = (c0[q] + shift_amount) % ms[q]
    c0 = tuple(c0)

    if c0 in good_set:
        return None, "overlap_start"

    # Follow forced transitions
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
            return None, f"stuck_step{step}"

        nxt, p = available[0]
        movers.append(p)

        if nxt == c0:
            if len(path) == ell:
                return (path, movers), "success"
            else:
                return None, f"wrong_len_{len(path)}"

        if nxt in set(path):
            return None, f"inner_cycle_step{step}"

        path.append(nxt)
        cur = nxt

    return None, "no_return"

def full_verify(ms, n, bad_configs, bad_movers, good_set, mcx):
    """Verify all BadCycleData properties."""
    ell = len(bad_configs)

    disjoint = all(c not in good_set for c in bad_configs)
    distinct = len(set(bad_configs)) == ell

    priv_ok = True
    step_ok = True
    for s in range(ell):
        p = bad_movers[s]
        c = bad_configs[s]
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]

        if (L, S, R) not in mcx[p]:
            priv_ok = False; break
        Sp = mcx[p][(L, S, R)]
        if Sp == S:
            priv_ok = False; break

        nc = list(c); nc[p] = Sp; nc = tuple(nc)
        expected = bad_configs[(s+1) % ell]
        if nc != expected:
            step_ok = False; break

    return disjoint and distinct and priv_ok and step_ok

# ============================================================
# TEST AT BOTH n=7 AND n=9
# ============================================================
for n, ms in [(7, [2,3,3,2,3,3,2]), (9, [2,3,3,2,3,3,2,3,3])]:
    print(f"\n{'='*72}")
    print(f"n={n}, ms={ms}")
    print(f"{'='*72}")

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

    print(f"Sweeps: {len(sweeps)}, Combos: {len(all_combos)}")

    binary_pos = [p for p in range(n) if ms[p] == 2]
    ternary_pos = [p for p in range(n) if ms[p] == 3]
    print(f"Binary: {binary_pos}, Ternary: {ternary_pos}")

    # For each sweep, for each combo, test which single-proc shifts work
    for wi, (word, _, disp) in enumerate(sweeps[:2]):  # First 2 sweeps
        print(f"\n  Sweep {wi}: word={list(word)[:10]}... disp={disp}")

        for ci, combo in enumerate(all_combos[:4]):  # First 4 combos
            gc, _ = get_good_cycle_with_combo(ms, n, word, combo)
            gs = set(gc)

            mx = defaultdict(dict)
            for s in range(len(word)):
                p = word[s]
                L = gc[s][(p-1)%n]; S = gc[s][p]; R = gc[s][(p+1)%n]
                mx[p][(L, S, R)] = gc[(s+1)%len(word)][p]

            results = []
            for q in range(n):
                for shift in range(1, ms[q]):
                    result, status = test_shift(ms, n, gc, gs, mx, q, shift)
                    if result:
                        results.append((q, shift, status))

            working = [(q, sh) for q, sh, st in results]
            print(f"    Combo {ci}: working shifts = {working}")

    # Now exhaustive: for EVERY sweep x combo, does AT LEAST ONE shift work?
    print(f"\n  Exhaustive test: all sweeps x combos...")
    total = 0
    pass_count = 0
    shift_stats = defaultdict(int)

    for wi, (word, _, disp) in enumerate(sweeps):
        for ci, combo in enumerate(all_combos):
            gc, _ = get_good_cycle_with_combo(ms, n, word, combo)
            gs = set(gc)

            mx = defaultdict(dict)
            for s in range(len(word)):
                p = word[s]
                L = gc[s][(p-1)%n]; S = gc[s][p]; R = gc[s][(p+1)%n]
                mx[p][(L, S, R)] = gc[(s+1)%len(word)][p]

            found = False
            for q in range(n):
                for shift in range(1, ms[q]):
                    result, status = test_shift(ms, n, gc, gs, mx, q, shift)
                    if result:
                        bad_configs, bad_movers = result
                        ok = full_verify(ms, n, bad_configs, bad_movers, gs, mx)
                        if ok:
                            found = True
                            shift_stats[(q, shift)] += 1
                            break
                if found:
                    break

            total += 1
            if found:
                pass_count += 1
            else:
                print(f"    FAIL: sweep {wi}, combo {ci}")

    print(f"  Pass: {pass_count}/{total}")
    print(f"  Shift stats (which q,shift worked first):")
    for (q, sh), cnt in sorted(shift_stats.items()):
        print(f"    P{q} shift={sh}: {cnt} times")

# ============================================================
# NOW: What's special about the working shifts?
# ============================================================
print(f"\n{'='*72}")
print("ANALYSIS: What determines which shifts work?")
print("="*72)

# At n=7: P6 shift=1 works. P6 is the binary proc at position 6.
# The mover word starts at P0, so P6 is adjacent to P0 (dist=1).
# But P2 and P3 also work (inner cycle at later step, meaning shift
# starts further in and catches up).
#
# The fundamental question for Lean: can we always find a working shift?
# And what's the simplest characterization?

# Test: for each sweep, find ALL working (q, shift) pairs
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
combo0 = tuple(enumerate_state_sequences(ms[p], ms[p])[0] for p in range(n))
all_cfgs = list(itertools.product(*(range(m) for m in ms)))

print(f"\nn=7: All working shifts for first sweep, first combo:")
word = sweeps[0][0]
gc, _ = get_good_cycle_with_combo(ms, n, word, combo0)
gs = set(gc)
mx = defaultdict(dict)
for s in range(len(word)):
    p = word[s]
    L = gc[s][(p-1)%n]; S = gc[s][p]; R = gc[s][(p+1)%n]
    mx[p][(L, S, R)] = gc[(s+1)%len(word)][p]

for q in range(n):
    for shift in range(1, ms[q]):
        result, status = test_shift(ms, n, gc, gs, mx, q, shift)
        label = "WORKS" if result else status
        if result:
            bad_c, bad_m = result
            ok = full_verify(ms, n, bad_c, bad_m, gs, mx)
            label = f"VALID (len={len(bad_c)})" if ok else f"INVALID ({status})"
        dist = ring_dist(q, word[0], n)
        print(f"  P{q} (m={ms[q]}) shift={shift} dist_from_start={dist}: {label}")
