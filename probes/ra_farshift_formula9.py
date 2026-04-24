#!/usr/bin/env python3
"""
RA Part 9: Final formula verification.

FORMULA CANDIDATE:
For a stuttered sweep starting at proc p0:
- If sweep goes CCW (p0, p0-1, p0-2, ...): shift q = (p0+1) % n by combo[q][1]
- If sweep goes CW (p0, p0+1, p0+2, ...): shift q = (p0-1) % n by combo[q][1]

combo[q][1] is the value q transitions to after its first firing (= 1 for seq (0,1,2,0), = 2 for seq (0,2,1,0)).

For binary procs: combo[q][1] = 1 always (only one option: 0->1->0).

Verify at n=9, 11 (general n).
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

def test_shift_full(ms, n, gc_configs, good_set, mcx, q, shift_amount):
    """Test if shifting proc q gives a valid bad cycle. Returns (bad_configs, bad_movers) or None."""
    ell = len(gc_configs)
    c0 = list(gc_configs[0])
    c0[q] = (c0[q] + shift_amount) % ms[q]
    c0 = tuple(c0)
    if c0 in good_set:
        return None
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
            return None
        nxt, p = available[0]
        movers.append(p)
        if nxt == c0:
            if len(path) == ell:
                # Verify all properties
                disjoint = all(c not in good_set for c in path)
                distinct = len(set(path)) == ell
                step_ok = True
                for s in range(ell):
                    pp = movers[s]
                    c = path[s]
                    L = c[(pp-1)%n]; S = c[pp]; R = c[(pp+1)%n]
                    if (L, S, R) not in mcx[pp]:
                        step_ok = False; break
                    Sp = mcx[pp][(L, S, R)]
                    nc = list(c); nc[pp] = Sp
                    expected = path[(s+1)%ell]
                    if tuple(nc) != expected:
                        step_ok = False; break
                if disjoint and distinct and step_ok:
                    return (path, movers)
            return None
        if nxt in set(path):
            return None
        path.append(nxt)
        cur = nxt
    return None

# ============================================================
# TEST THE FORMULA
# ============================================================

for n, ms in [(9, [2,3,3,2,3,3,2,3,3])]:
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

    total = 0
    pass_count = 0
    fail_count = 0

    for wi, (word, _, disp) in enumerate(sweeps):
        first_mover = word[0]
        diff01 = (word[1] - word[0]) % n

        if diff01 == n-1:  # CCW
            q = (first_mover + 1) % n  # behind = CW side
        else:  # CW
            q = (first_mover - 1) % n  # behind = CCW side

        for ci, combo in enumerate(all_combos):
            gc, _ = get_good_cycle_with_combo(ms, n, word, combo)
            gs = set(gc)
            mx = defaultdict(dict)
            for s in range(len(word)):
                p = word[s]
                L = gc[s][(p-1)%n]; S = gc[s][p]; R = gc[s][(p+1)%n]
                mx[p][(L, S, R)] = gc[(s+1)%len(word)][p]

            # Formula: shift q by combo[q][1]
            shift_amount = combo[q][1]
            result = test_shift_full(ms, n, gc, gs, mx, q, shift_amount)

            total += 1
            if result:
                pass_count += 1
            else:
                fail_count += 1
                # Try other shifts
                other_works = False
                for sh in range(1, ms[q]):
                    if sh == shift_amount: continue
                    r2 = test_shift_full(ms, n, gc, gs, mx, q, sh)
                    if r2:
                        other_works = True
                        print(f"  FORMULA WRONG: sweep {wi} combo {ci}: "
                              f"combo[q={q}][1]={shift_amount} fails, shift={sh} works "
                              f"(seq_q={combo[q]})")
                        break
                if not other_works:
                    print(f"  NO SHIFT WORKS: sweep {wi} combo {ci}")

    print(f"\nFormula results: {pass_count}/{total} pass")

    # If formula doesn't work 100%, try alternative: shift by 1 always
    if pass_count < total:
        print(f"\nTrying shift=1 always:")
        p1 = 0
        for wi, (word, _, disp) in enumerate(sweeps):
            first_mover = word[0]
            diff01 = (word[1] - word[0]) % n
            if diff01 == n-1:
                q = (first_mover + 1) % n
            else:
                q = (first_mover - 1) % n
            for ci, combo in enumerate(all_combos):
                gc, _ = get_good_cycle_with_combo(ms, n, word, combo)
                gs = set(gc)
                mx = defaultdict(dict)
                for s in range(len(word)):
                    p = word[s]
                    L = gc[s][(p-1)%n]; S = gc[s][p]; R = gc[s][(p+1)%n]
                    mx[p][(L, S, R)] = gc[(s+1)%len(word)][p]
                r = test_shift_full(ms, n, gc, gs, mx, q, 1)
                if r: p1 += 1
        print(f"  shift=1: {p1}/{total}")

        print(f"\nTrying: shift q by amount that makes c0 different from ALL good configs")
        print(f"(actually c0 is always different since gc[0] is all-zeros)")
        print(f"Let me try: just try shift=1 then shift=2")
        p_either = 0
        for wi, (word, _, disp) in enumerate(sweeps):
            first_mover = word[0]
            diff01 = (word[1] - word[0]) % n
            if diff01 == n-1:
                q = (first_mover + 1) % n
            else:
                q = (first_mover - 1) % n
            for ci, combo in enumerate(all_combos):
                gc, _ = get_good_cycle_with_combo(ms, n, word, combo)
                gs = set(gc)
                mx = defaultdict(dict)
                for s in range(len(word)):
                    p = word[s]
                    L = gc[s][(p-1)%n]; S = gc[s][p]; R = gc[s][(p+1)%n]
                    mx[p][(L, S, R)] = gc[(s+1)%len(word)][p]
                r1 = test_shift_full(ms, n, gc, gs, mx, q, 1)
                r2 = test_shift_full(ms, n, gc, gs, mx, q, 2) if ms[q] > 2 else None
                if r1 or r2: p_either += 1
                else:
                    print(f"  BOTH FAIL: sweep {wi} combo {ci} q={q}")
        print(f"  shift 1 or 2: {p_either}/{total}")

    # ============================================================
    # DEEPER: What determines shift=1 vs shift=2?
    # We know it's combo[q][1] = seq_q[1] for ternary.
    # The state sequence determines the transition order:
    # seq=(0,1,2,0) means 0->1->2->0 ("incrementing")
    # seq=(0,2,1,0) means 0->2->1->0 ("decrementing")
    #
    # After shifting q by d, the new value at q is d.
    # The first time q fires in the bad cycle, it transitions d -> next_val.
    # For the forced entry to match, we need the context at q to be
    # a forced entry where S = d.
    #
    # If seq_q = (0,1,2,0), the forced entries have S in {0,1,2} at the
    # 3 firing steps. After shift by 1: S=1 at step when good has S=0.
    # The context (L,1,R) must be a forced entry.
    # ============================================================

    # Let me check: what's the actual forced entry context at q in the bad cycle?
    word = sweeps[0][0]
    combo_inc = list(all_combos[0])  # seq8 = (0,1,2,0)
    combo_dec = list(all_combos[1])  # seq8 = (0,2,1,0)

    for label, combo in [("inc", combo_inc), ("dec", combo_dec)]:
        gc, _ = get_good_cycle_with_combo(ms, n, word, tuple(combo))
        gs = set(gc)
        mx = defaultdict(dict)
        for s in range(len(word)):
            p = word[s]
            L = gc[s][(p-1)%n]; S = gc[s][p]; R = gc[s][(p+1)%n]
            mx[p][(L, S, R)] = gc[(s+1)%len(word)][p]

        q = 8  # P8 for CCW sweep starting at P0
        for sh in [1, 2]:
            result = test_shift_full(ms, n, gc, gs, mx, q, sh)
            works = "WORKS" if result else "FAILS"
            print(f"\n  {label} (seq8={combo[8]}), shift P8 by {sh}: {works}")
            if result:
                bad_c, bad_m = result
                # Show first few steps
                for s in range(min(6, len(bad_c))):
                    p = bad_m[s]
                    c = bad_c[s]
                    ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
                    print(f"    [{s}] fire P{p} ctx={ctx}")

    # ============================================================
    # THE REAL FORMULA: For any system with the good cycle,
    # the shift amount for proc q must ensure that:
    # 1. The shifted initial config c0 = (0,...,0,d,...,0) is not in good_set
    # 2. At every step, some proc has a forced-entry context
    # 3. The orbit closes in CL steps
    #
    # For Lean: use the ShadowTrap approach.
    # Define trap = {c not in good : forall p with forced entry context at c,
    #   the transition leads to another non-good config with forced entry context}
    # Show trap is nonempty.
    #
    # Actually the SIMPLEST Lean approach:
    # 1. The forced entries are f_p(L,S,R) = (S+1) mod m_p for specific (L,S,R)
    # 2. Show that ALL configs of the form (0,...,0,d,0,...,0) for d != 0 at
    #    a ternary q far from the first mover have at least one forced transition
    # 3. The forced transition graph on non-good configs has a cycle
    # 4. This cycle is the bad cycle
    #
    # But proving step 3 analytically is hard without an explicit formula.
    #
    # SIMPLEST LEAN APPROACH: Use decidability for n=9..K for some K,
    # then an asymptotic argument for n > K.
    # But the Lean theorem has general n >= 9, so we need general n.
    # ============================================================

    # ============================================================
    # Let me check: does the formula shift_amount = combo[q][1] work
    # for the ALTERNATIVE choice of q?
    # ============================================================
    print(f"\n{'='*72}")
    print("Alternative q choices")
    print("="*72)

    # For each sweep, try ALL ternary procs as q
    for wi, (word, _, disp) in enumerate(sweeps[:2]):
        first_mover = word[0]
        diff01 = (word[1] - word[0]) % n
        direction = "CCW" if diff01 == n-1 else "CW"

        print(f"\n  Sweep {wi}: start=P{first_mover}, dir={direction}")

        for q in range(n):
            # Try shift = combo[q][1] for each combo
            pass_q = 0
            for ci, combo in enumerate(all_combos):
                gc, _ = get_good_cycle_with_combo(ms, n, word, combo)
                gs = set(gc)
                mx = defaultdict(dict)
                for s in range(len(word)):
                    p = word[s]
                    L = gc[s][(p-1)%n]; S = gc[s][p]; R = gc[s][(p+1)%n]
                    mx[p][(L, S, R)] = gc[(s+1)%len(word)][p]
                sh = combo[q][1]
                r = test_shift_full(ms, n, gc, gs, mx, q, sh)
                if r: pass_q += 1

            # Also try shift=1 always
            pass_q1 = 0
            for ci, combo in enumerate(all_combos):
                gc, _ = get_good_cycle_with_combo(ms, n, word, combo)
                gs = set(gc)
                mx = defaultdict(dict)
                for s in range(len(word)):
                    p = word[s]
                    L = gc[s][(p-1)%n]; S = gc[s][p]; R = gc[s][(p+1)%n]
                    mx[p][(L, S, R)] = gc[(s+1)%len(word)][p]
                r = test_shift_full(ms, n, gc, gs, mx, q, 1)
                if r: pass_q1 += 1

            dist = min((q - first_mover) % n, (first_mover - q) % n)
            print(f"    q=P{q} (m={ms[q]}, dist={dist}): "
                  f"combo[q][1]={pass_q}/{len(all_combos)} shift=1={pass_q1}/{len(all_combos)}")
