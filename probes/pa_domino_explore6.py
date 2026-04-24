#!/usr/bin/env python3
"""
PA Domino Exploration 6: Find the EC mechanism in the sorry branch.

The sorry branch has:
- 3 consecutive binary at {i, t, rr}
- t has isolated firings, fc(t) ≥ 2
- Odd parity at one/both neighbors in min firing gap
- Phase dispatch fails for the extracted phase

Question: WHERE does EC come from? At which processor?
"""

from itertools import product as iproduct
from collections import Counter

def find_ec_detailed(n, ms, word):
    """Find EC at each proc and return the overlapping context."""
    ell = len(word)
    start = tuple(0 for _ in range(n))
    cfgs = [list(start)]
    for i in range(ell):
        c = list(cfgs[-1])
        c[word[i]] = (c[word[i]] + 1) % ms[word[i]]
        cfgs.append(c)

    ec_at = {}
    for p in range(n):
        mover_ctxs = {}
        nonmover_ctxs = {}
        for s in range(ell):
            ctx = (cfgs[s][(p-1)%n], cfgs[s][p], cfgs[s][(p+1)%n])
            if word[s] == p:
                if ctx in nonmover_ctxs:
                    ec_at[p] = (ctx, s, nonmover_ctxs[ctx], 'mover_hits_nm')
                    break
                mover_ctxs.setdefault(ctx, s)
            else:
                if ctx in mover_ctxs:
                    ec_at[p] = (ctx, mover_ctxs[ctx], s, 'nm_hits_mover')
                    break
                nonmover_ctxs.setdefault(ctx, s)
    return ec_at

def check_sorry_branch(n, ms, binary_triple, max_cycles=5000, verbose_count=10):
    """Enumerate cycles in the sorry branch and analyze EC."""
    i_pos, t_pos, rr_pos = binary_triple

    start = tuple(0 for _ in range(n))
    results = []

    def dfs(word, fc, config):
        if len(results) >= max_cycles: return
        if len(word) > 6*n: return
        if len(word) >= n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
                return
        remaining = 6*n - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining: return
        for nxt in range(n):
            if abs(nxt - word[-1]) % n not in [1, n-1]: continue
            if len(results) >= max_cycles: return
            word.append(nxt)
            nf = list(fc); nf[nxt] += 1
            nc = list(config); nc[nxt] = (nc[nxt]+1) % ms[nxt]
            dfs(word, nf, tuple(nc))
            word.pop()

    for p in range(n):
        if len(results) >= max_cycles: break
        first = list(start); first[p] = (first[p]+1) % ms[p]
        dfs([p], [1 if j==p else 0 for j in range(n)], tuple(first))

    def winding(word):
        w = 0
        for idx in range(len(word)):
            d = (word[(idx+1)%len(word)] - word[idx]) % n
            if d == 1: w += 1
            elif d == n-1: w -= 1
        return w

    zw = [w for w in results if winding(w) == 0]

    # Statistics
    ec_proc_stats = Counter()
    ec_proc_type_stats = Counter()  # (proc_position_type, state_count) → count
    total_sorry = 0
    no_ec = 0
    verbose_shown = 0

    for word in zw:
        ell = len(word)
        fc = Counter(word)
        if fc[t_pos] < 2: continue

        # Check isolated at t
        t_steps = [s for s in range(ell) if word[s] == t_pos]
        isolated = True
        for s in t_steps:
            if word[(s+1) % ell] == t_pos or word[(s-1) % ell] == t_pos:
                isolated = False
                break
        if not isolated: continue

        # Min gap + odd parity check
        min_gap = float('inf')
        min_a = None
        for idx in range(len(t_steps)):
            a = t_steps[idx]
            b = t_steps[(idx+1) % len(t_steps)]
            if b <= a: b += ell
            gap = b - a
            if gap < min_gap:
                min_gap = gap
                min_a, min_b_raw = a, (b % ell if b >= ell else b)

        a = min_a
        b = min_b_raw
        if b > a:
            J_gap = sum(1 for s in range(a+1, b) if word[s] == i_pos)
            K_gap = sum(1 for s in range(a+1, b) if word[s] == rr_pos)
        else:
            J_gap = sum(1 for s in range(a+1, b+ell) if word[s%ell] == i_pos)
            K_gap = sum(1 for s in range(a+1, b+ell) if word[s%ell] == rr_pos)

        if J_gap % 2 == 0 and K_gap % 2 == 0:
            continue  # even parity → different branch

        # Check dispatch on SOME phase (extracted phase)
        # In reality, exists_ternaryPhase picks a specific phase.
        # Let's check if ANY phase fails dispatch.
        phases = []
        for idx in range(len(t_steps)):
            a2 = t_steps[idx]
            b2 = t_steps[(idx+1) % len(t_steps)]
            if b2 <= a2: b2 += ell
            J = sum(1 for s in range(a2+1, b2) if word[s%ell] == i_pos)
            K = sum(1 for s in range(a2+1, b2) if word[s%ell] == rr_pos)
            phases.append((J, K))

        # Check if the min-gap phase fails dispatch
        mg_phase = phases[t_steps.index(min_a)]
        J_mg, K_mg = mg_phase
        dispatched = (J_mg % 2 == 0 and K_mg % 2 == 0) or (J_mg >= 2 and K_mg == 0) or (J_mg == 0 and K_mg >= 2)
        if dispatched:
            continue  # dispatch succeeds → different branch

        total_sorry += 1

        # Find EC
        ec = find_ec_detailed(n, ms, word)
        if not ec:
            no_ec += 1
            if verbose_shown < verbose_count:
                print(f"  NO EC: word={word}")
                verbose_shown += 1
            continue

        for p in ec:
            # Classify: which proc relative to the binary triple?
            if p == t_pos:
                pos_type = 't'
            elif p == i_pos:
                pos_type = 'i'
            elif p == rr_pos:
                pos_type = 'rr'
            elif p == (i_pos - 1) % n:
                pos_type = 'left(i)'
            elif p == (rr_pos + 1) % n:
                pos_type = 'right(rr)'
            else:
                pos_type = 'far'
            ec_proc_stats[pos_type] += 1
            ec_proc_type_stats[(pos_type, ms[p])] += 1

        if verbose_shown < verbose_count:
            ec_procs = list(ec.keys())
            ec_positions = []
            for p in ec_procs:
                if p == t_pos: ec_positions.append('t')
                elif p == i_pos: ec_positions.append('i')
                elif p == rr_pos: ec_positions.append('rr')
                elif p == (i_pos-1)%n: ec_positions.append('left(i)')
                elif p == (rr_pos+1)%n: ec_positions.append('right(rr)')
                else: ec_positions.append(f'p{p}')
            print(f"  EC at {ec_positions}, phases={phases}, fc_t={fc[t_pos]}")
            verbose_shown += 1

    return total_sorry, no_ec, ec_proc_stats, ec_proc_type_stats

print("="*70)
print("SORRY BRANCH EC ANALYSIS")
print("="*70)

# n=5
n = 5
for ms, bt in [([2,2,2,3,3], (0,1,2)), ([3,2,2,2,3], (1,2,3))]:
    print(f"\nn={n}, ms={ms}, binary triple={bt}")
    total, no_ec, proc_stats, type_stats = check_sorry_branch(n, ms, bt)
    print(f"  Total sorry-branch cycles: {total}")
    print(f"  No EC: {no_ec}")
    print(f"  EC proc distribution: {dict(proc_stats)}")
    print(f"  EC proc type detail: {dict(type_stats)}")

# n=7
n = 7
ms = [3, 3, 2, 2, 2, 3, 3]
bt = (2, 3, 4)
print(f"\nn={n}, ms={ms}, binary triple={bt}")
total, no_ec, proc_stats, type_stats = check_sorry_branch(n, ms, bt)
print(f"  Total sorry-branch cycles: {total}")
print(f"  No EC: {no_ec}")
print(f"  EC proc distribution: {dict(proc_stats)}")
print(f"  EC proc type detail: {dict(type_stats)}")
