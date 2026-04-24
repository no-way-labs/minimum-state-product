#!/usr/bin/env python3
"""RA12 v2: Winding analysis for no-EC good cycles.

Focused approach: use smaller n (5,6,7) where enumeration is tractable,
plus targeted analysis of the n=9 bounce cycle structure.

For the n=9 case, we construct the CLB-style bounce cycle analytically
rather than enumerating all cycles.
"""

from collections import Counter
from itertools import product as iproduct
import sys


def get_binary_positions(ms):
    return [i for i, m in enumerate(ms) if m == 2]


def are_consecutive(positions, n):
    for i in range(len(positions)):
        for j in range(i+1, len(positions)):
            if abs(positions[i] - positions[j]) % n in (1, n-1):
                return True
    return False


def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= 2*n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
            return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n)
                      if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining:
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


def build_cycle(ms, n, word):
    ell = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:ell])) != ell:
        return None
    return configs[:ell]


def is_wrap_adjacent(word, n):
    return abs(word[-1] - word[0]) % n in (1, n-1)


def canonicalize_word(word):
    best = word
    for i in range(len(word)):
        rot = word[i:] + word[:i]
        if rot < best:
            best = rot
    return best


def compute_total_displacement(word, n):
    total = 0
    ell = len(word)
    for i in range(ell):
        cur = word[i]
        nxt = word[(i+1) % ell]
        diff = (nxt - cur) % n
        if diff == 1:
            total += 1
        elif diff == n - 1:
            total -= 1
        else:
            raise ValueError(f"Non-adjacent step: {cur} -> {nxt}")
    return total


def has_entry_conflict_at_any_proc(word, cycle, ms, n):
    ell = len(word)
    for p in range(n):
        mover_contexts = set()
        nonmover_contexts = set()
        for s in range(ell):
            L = cycle[s][(p-1) % n]
            S = cycle[s][p]
            R = cycle[s][(p+1) % n]
            ctx = (L, S, R)
            if word[s] == p:
                mover_contexts.add(ctx)
            else:
                nonmover_contexts.add(ctx)
        if mover_contexts & nonmover_contexts:
            return True
    return False


def has_safe_processor(word, n):
    fired = set(word)
    for p in range(n):
        neighbors = {(p-1) % n, p, (p+1) % n}
        if not (neighbors & fired):
            return True, p
    return False, None


def count_cw_steps(word, n):
    cw = 0
    ell = len(word)
    for i in range(ell):
        cur = word[i]
        nxt = word[(i+1) % ell]
        diff = (nxt - cur) % n
        if diff == 1:
            cw += 1
    return cw


def enumerate_state_sequences(m, k):
    seqs = []
    def dfs(seq, remaining):
        if remaining == 0:
            if seq[-1] == 0:
                seqs.append(tuple(seq))
            return
        for nv in range(m):
            if nv != seq[-1]:
                if remaining == 1 and nv != 0:
                    continue
                seq.append(nv)
                dfs(seq, remaining - 1)
                seq.pop()
    dfs([0], k)
    return seqs


def check_all_state_combos_ec(word, ms, n, max_combos=200000):
    """Check if every state-sequence combo has EC."""
    ell = len(word)
    fc = Counter(word)

    proc_seqs = {}
    total = 1
    for p in range(n):
        k = fc[p]
        proc_seqs[p] = enumerate_state_sequences(ms[p], k)
        total *= len(proc_seqs[p])

    if total > max_combos:
        return None, None, total, []

    proc_steps = {p: [] for p in range(n)}
    for s in range(ell):
        proc_steps[word[s]].append(s)

    no_ec_count = 0
    no_ec_examples = []
    checked = 0

    # Use itertools.product for cleaner iteration
    proc_list = list(range(n))
    seq_lists = [proc_seqs[p] for p in proc_list]

    for combo in iproduct(*seq_lists):
        checked += 1
        # Build config sequence
        configs = [[0]*n for _ in range(ell)]
        state = [0]*n
        configs[0] = list(state)
        for s in range(ell):
            p = word[s]
            firing_idx = proc_steps[p].index(s) if s == proc_steps[p][0] else None
            # Find which firing this is
            cnt = 0
            for prev in proc_steps[p]:
                if prev < s:
                    cnt += 1
                elif prev == s:
                    break
            new_val = combo[p][cnt + 1]
            state[p] = new_val
            if s + 1 < ell:
                configs[s+1] = list(state)

        # Check EC
        has_ec = False
        for q in range(n):
            mover_ctx = set()
            nonmover_ctx = set()
            for s in range(ell):
                L = configs[s][(q-1) % n]
                S = configs[s][q]
                R = configs[s][(q+1) % n]
                ctx = (L, S, R)
                if word[s] == q:
                    mover_ctx.add(ctx)
                else:
                    nonmover_ctx.add(ctx)
            if mover_ctx & nonmover_ctx:
                has_ec = True
                break

        if not has_ec:
            no_ec_count += 1
            if len(no_ec_examples) < 3:
                no_ec_examples.append(combo)

    return no_ec_count == 0, no_ec_count, checked, no_ec_examples


def classify_cycle(word, ms, n):
    ell = len(word)
    disp = compute_total_displacement(word, n)
    cw = count_cw_steps(word, n)
    ccw = ell - cw
    safe, safe_p = has_safe_processor(word, n)

    if safe:
        branch = "Branch 1: safe processor"
    elif disp == 0:
        if cw == 0:
            branch = "Branch 2: zero winding, cw=0 (pure CCW)"
        else:
            branch = "Branch 3: zero winding, cw>0 (sorrys 1,4a-c)"
    elif abs(disp) >= 2 * n:
        branch = "Branch 4a: sweep (sorry 6)"
    elif abs(disp) == n:
        branch = "Branch 4b: odd-winding (sorry 7)"
    else:
        branch = f"Branch 4?: disp={disp} unexpected"

    return {
        'disp': disp,
        'cw': cw,
        'ccw': ccw,
        'safe': safe,
        'safe_proc': safe_p,
        'branch': branch,
    }


# ============================================================
# Part 1: Smaller n where enumeration is tractable
# ============================================================
print("=" * 72)
print("PART 1: Exhaustive analysis at n=5,6,7")
print("=" * 72)

for n_val, max_len in [(5, 16), (6, 20), (7, 24)]:
    print(f"\n{'='*60}")
    print(f"n = {n_val}")
    print(f"{'='*60}")

    threshold = 4 * (3 ** (n_val - 2))

    # Generate all non-consecutive binary multisets
    from itertools import combinations
    multisets = []
    for num_bin in range(3, n_val + 1):
        for positions in combinations(range(n_val), num_bin):
            pos_set = set(positions)
            consec = any((p+1) % n_val in pos_set for p in positions)
            if consec:
                continue
            ms = [3] * n_val
            for p in positions:
                ms[p] = 2
            prod = 1
            for m in ms:
                prod *= m
            if prod < threshold:
                multisets.append(ms)

    print(f"Sub-threshold non-consecutive-binary multisets: {len(multisets)}")

    global_branch_counts = Counter()
    global_no_ec_branches = Counter()

    for ms in multisets:
        bp = get_binary_positions(ms)
        prod = 1
        for m in ms:
            prod *= m

        words = enumerate_mover_words(ms, n_val, max_len)

        # Deduplicate
        seen = set()
        unique = []
        for w in words:
            canon = canonicalize_word(w)
            if canon not in seen:
                seen.add(canon)
                unique.append(w)

        valid = [w for w in unique
                 if is_wrap_adjacent(w, n_val) and build_cycle(ms, n_val, w) is not None]

        if not valid:
            continue

        cycle_info = []
        for w in valid:
            info = classify_cycle(w, ms, n_val)
            cycle = build_cycle(ms, n_val, w)

            # Check EC with incrementing transition
            has_ec_inc = has_entry_conflict_at_any_proc(w, cycle, ms, n_val)

            # Check all state combos
            result = check_all_state_combos_ec(w, ms, n_val)
            if result[0] is not None:
                all_ec = result[0]
                no_ec_count = result[1]
            else:
                all_ec = None
                no_ec_count = None

            global_branch_counts[info['branch']] += 1

            if all_ec is not None and not all_ec:
                global_no_ec_branches[info['branch']] += 1
                cycle_info.append((w, info, no_ec_count, result[2]))

        if cycle_info:
            print(f"\n  ms={ms}, prod={prod}, binary@{bp}")
            print(f"  {len(valid)} cycles, {len(cycle_info)} have no-EC combos:")
            for w, info, nec, tot in cycle_info[:5]:
                print(f"    CL={len(w)} disp={info['disp']:+d} cw={info['cw']} "
                      f"safe={info['safe']} no_ec={nec}/{tot} | {info['branch']}")

    print(f"\n  GLOBAL branch distribution (all cycles):")
    for b in sorted(global_branch_counts.keys()):
        print(f"    {b}: {global_branch_counts[b]}")

    print(f"\n  GLOBAL no-EC cycles by branch:")
    for b in sorted(global_no_ec_branches.keys()):
        print(f"    {b}: {global_no_ec_branches[b]}")


# ============================================================
# Part 2: Analytical construction of n=9 bounce cycles
# ============================================================
print("\n" + "=" * 72)
print("PART 2: Analytical n=9 bounce cycle construction")
print("=" * 72)

n = 9

# The CLB bounce cycle for endpoint-binary ms=(2,3,...,3,2):
# Goes 0,1,2,...,8,7,6,...,1 (up-down bounce)
# But for ms=[2,3,3,2,3,3,2,3,3] the binary are at 0,3,6

# Let's construct bounce-like cycles for all-odd-gap
# Binary at 0,3,6 fire 2x each, ternary at 1,2,4,5,7,8 fire 3x each
# Total fires = 3*2 + 6*3 = 24

# A bounce cycle on 9 nodes: 0,1,2,3,4,5,6,7,8,7,6,5,4,3,2,1 (length 16, repeat...)
# But we need exact fire counts.

# Let's think about what displacement a bounce cycle has.
# Up sweep: 0->1->2->...->8 = +8 steps (8 CW)
# Down sweep: 8->7->6->...->0 = -8 steps (8 CCW)
# Total disp = 8 - 8 = 0 for one full bounce
# But fire counts: each interior proc fires 2x per bounce, endpoints fire 1x
# For binary (2-state) procs at 0,3,6: need fire 2x each
# For ternary (3-state) procs: need fire 3x each

# A single up-down bounce (0->8->0) has CL=16, each proc fires 2x (except endpoints 1x)
# That gives binary procs 2 fires (good for 2-state), but ternary need 3.
# So we need 1.5 bounces = up-down-up? That's CL=24.

# Up (0->8): fires 0,1,2,3,4,5,6,7,8 once each
# Down (8->0): fires 8,7,6,5,4,3,2,1,0 once each
# Up (0->8): fires 0,1,2,3,4,5,6,7,8 once each
# Total: endpoints fire 3x, interior fire 3x, but positions 0 and 8 fire 3x
# Wait, need to be more careful.

# Actually for up-down-up bounce:
# 0,1,2,3,4,5,6,7,8,7,6,5,4,3,2,1,0,1,2,3,4,5,6,7,8
# That's 25 steps, CL=24 (last step wraps to first)
# Mover word: [0,1,2,3,4,5,6,7,8,7,6,5,4,3,2,1,0,1,2,3,4,5,6,7]
# Wait, let me count fires:
# Proc 0: fires at steps 0, 16 = 2 times
# Proc 1: fires at steps 1, 15, 17 = 3 times
# Proc 2: fires at steps 2, 14, 18 = 3 times
# ...
# Proc 8: fires at step 8 = 1 time

# That's wrong for a cycle. Let me think again.

# For a mover word of length L that forms a cycle:
# word = [w_0, w_1, ..., w_{L-1}]
# w_{L-1} and w_0 must be ring-adjacent
# The cycle visits L distinct configs

# Let me just construct specific bounce words and compute their properties.

def make_bounce_word_updownup(n):
    """Construct up-down-up bounce: 0,1,...,n-1,n-2,...,1,0,1,...,n-1
    But last position must be adjacent to first (0)."""
    word = []
    # Up: 0 to n-1
    for i in range(n):
        word.append(i)
    # Down: n-2 to 0
    for i in range(n-2, -1, -1):
        word.append(i)
    # Up: 1 to n-1
    for i in range(1, n):
        word.append(i)
    # CL = n + (n-1) + (n-1) = 3n-2
    # Last = n-1, first = 0: adjacent if ring
    # But for n=9: last=8, first=0, adjacent!
    return tuple(word)

def make_bounce_word_updown(n):
    """Up then down: 0,1,...,n-1,n-2,...,1"""
    word = []
    for i in range(n):
        word.append(i)
    for i in range(n-2, 0, -1):
        word.append(i)
    # CL = n + (n-2) = 2n-2
    # Last = 1, first = 0: adjacent
    return tuple(word)

for label, word_fn in [("up-down-up (3n-2)", make_bounce_word_updownup),
                        ("up-down (2n-2)", make_bounce_word_updown)]:
    w = word_fn(n)
    fc = Counter(w)
    ell = len(w)

    print(f"\n--- {label}, CL={ell} ---")
    print(f"  Word: {list(w)}")
    print(f"  Fire counts: {dict(sorted(fc.items()))}")

    try:
        disp = compute_total_displacement(w, n)
        cw = count_cw_steps(w, n)
        ccw = ell - cw
        print(f"  Total displacement: {disp}")
        print(f"  CW steps: {cw}, CCW steps: {ccw}")
        print(f"  Winding number: {disp}/{n} = {disp/n}")
        safe, sp = has_safe_processor(w, n)
        print(f"  Safe processor: {safe} (proc={sp})")
    except Exception as e:
        print(f"  Error: {e}")


# ============================================================
# Part 3: Small n=5 deep dive with all-odd-gap type
# ============================================================
print("\n" + "=" * 72)
print("PART 3: Deep dive n=5, ms=[2,3,2,3,2] (alternating)")
print("=" * 72)

n = 5
ms = [2,3,2,3,2]
bp = get_binary_positions(ms)
prod = 1
for m in ms:
    prod *= m
threshold = 4 * 3**(n-2)
print(f"ms={ms}, prod={prod}, threshold={threshold}")
print(f"Binary at {bp}, non-consecutive: {not are_consecutive(bp, n)}")

words = enumerate_mover_words(ms, n, 16)
seen = set()
unique = []
for w in words:
    canon = canonicalize_word(w)
    if canon not in seen:
        seen.add(canon)
        unique.append(w)
valid = [w for w in unique if is_wrap_adjacent(w, n) and build_cycle(ms, n, w) is not None]
print(f"Valid cycles: {len(valid)}")

branch_counts = Counter()
no_ec_by_branch = Counter()
no_ec_cycles = []

for w in valid:
    info = classify_cycle(w, ms, n)
    cycle = build_cycle(ms, n, w)
    result = check_all_state_combos_ec(w, ms, n)
    branch_counts[info['branch']] += 1

    if result[0] is not None and not result[0]:
        no_ec_by_branch[info['branch']] += 1
        no_ec_cycles.append((w, info, result[1], result[2]))

print(f"\nAll branches:")
for b in sorted(branch_counts.keys()):
    print(f"  {b}: {branch_counts[b]}")

print(f"\nNo-EC cycles by branch:")
for b in sorted(no_ec_by_branch.keys()):
    print(f"  {b}: {no_ec_by_branch[b]}")

print(f"\nDetailed no-EC cycles:")
for w, info, nec, tot in no_ec_cycles:
    print(f"  word={list(w)}")
    print(f"  CL={len(w)} disp={info['disp']:+d} cw={info['cw']} ccw={info['ccw']} "
          f"safe={info['safe']} | {info['branch']}")
    print(f"  no_ec={nec}/{tot}")


# ============================================================
# Part 4: n=6 deep dive
# ============================================================
print("\n" + "=" * 72)
print("PART 4: Deep dive n=6")
print("=" * 72)

n = 6
threshold = 4 * 3**(n-2)

# All non-consecutive 3-binary multisets at n=6
multisets_n6 = []
for positions in combinations(range(n), 3):
    pos_set = set(positions)
    consec = any((p+1) % n in pos_set for p in positions)
    if consec:
        continue
    ms = [3] * n
    for p in positions:
        ms[p] = 2
    prod = 1
    for m in ms:
        prod *= m
    if prod < threshold:
        multisets_n6.append(ms)

print(f"Sub-threshold 3-binary non-consecutive multisets: {len(multisets_n6)}")

for ms in multisets_n6:
    bp = get_binary_positions(ms)
    prod = 1
    for m in ms:
        prod *= m

    words = enumerate_mover_words(ms, n, 20)
    seen = set()
    unique = []
    for w in words:
        canon = canonicalize_word(w)
        if canon not in seen:
            seen.add(canon)
            unique.append(w)
    valid = [w for w in unique if is_wrap_adjacent(w, n) and build_cycle(ms, n, w) is not None]

    if not valid:
        continue

    branch_counts = Counter()
    no_ec_by_branch = Counter()
    no_ec_list = []

    for w in valid:
        info = classify_cycle(w, ms, n)
        result = check_all_state_combos_ec(w, ms, n)
        branch_counts[info['branch']] += 1
        if result[0] is not None and not result[0]:
            no_ec_by_branch[info['branch']] += 1
            no_ec_list.append((w, info, result[1], result[2]))

    print(f"\nms={ms}, prod={prod}, binary@{bp}, {len(valid)} cycles")
    print(f"  Branches: {dict(sorted(branch_counts.items()))}")
    if no_ec_list:
        print(f"  NO-EC by branch: {dict(sorted(no_ec_by_branch.items()))}")
        for w, info, nec, tot in no_ec_list[:3]:
            print(f"    CL={len(w)} disp={info['disp']:+d} cw={info['cw']} "
                  f"safe={info['safe']} no_ec={nec}/{tot} | {info['branch']}")
    else:
        print(f"  ALL cycles have EC for all combos")


# ============================================================
# Part 5: n=7 with focus on no-EC
# ============================================================
print("\n" + "=" * 72)
print("PART 5: Deep dive n=7")
print("=" * 72)

n = 7
threshold = 4 * 3**(n-2)

multisets_n7 = []
for num_bin in range(3, n+1):
    for positions in combinations(range(n), num_bin):
        pos_set = set(positions)
        consec = any((p+1) % n in pos_set for p in positions)
        if consec:
            continue
        ms = [3] * n
        for p in positions:
            ms[p] = 2
        prod = 1
        for m in ms:
            prod *= m
        if prod < threshold:
            multisets_n7.append(ms)

print(f"Sub-threshold non-consecutive-binary multisets: {len(multisets_n7)}")

for ms in multisets_n7:
    bp = get_binary_positions(ms)
    prod = 1
    for m in ms:
        prod *= m

    words = enumerate_mover_words(ms, n, 22)
    seen = set()
    unique = []
    for w in words:
        canon = canonicalize_word(w)
        if canon not in seen:
            seen.add(canon)
            unique.append(w)
    valid = [w for w in unique if is_wrap_adjacent(w, n) and build_cycle(ms, n, w) is not None]

    if not valid:
        continue

    branch_counts = Counter()
    no_ec_by_branch = Counter()
    no_ec_list = []

    for w in valid:
        info = classify_cycle(w, ms, n)
        # Only do full EC check if displacement is interesting
        result = check_all_state_combos_ec(w, ms, n, max_combos=500000)
        branch_counts[info['branch']] += 1
        if result[0] is not None and not result[0]:
            no_ec_by_branch[info['branch']] += 1
            no_ec_list.append((w, info, result[1], result[2]))

    print(f"\nms={ms}, prod={prod}, binary@{bp}, {len(valid)} cycles")
    for b in sorted(branch_counts.keys()):
        print(f"  {b}: {branch_counts[b]}")
    if no_ec_list:
        print(f"  NO-EC by branch: {dict(sorted(no_ec_by_branch.items()))}")
        for w, info, nec, tot in no_ec_list[:3]:
            print(f"    CL={len(w)} disp={info['disp']:+d} cw={info['cw']} "
                  f"safe={info['safe']} no_ec={nec}/{tot} | {info['branch']}")


# ============================================================
# Part 6: Direct n=9 analysis with limited enumeration
# ============================================================
print("\n" + "=" * 72)
print("PART 6: n=9 targeted analysis")
print("=" * 72)

n = 9
ms_aog = [2,3,3,2,3,3,2,3,3]
bp = get_binary_positions(ms_aog)
prod_aog = 1
for m in ms_aog:
    prod_aog *= m
threshold = 4 * 3**7

print(f"All-odd-gap: ms={ms_aog}, prod={prod_aog}, threshold={threshold}")
print(f"Binary at {bp}")

# Minimum CL = 3*2 + 6*3 = 24
# The fc=1 (minimum fire count) cycles have CL=24
# Try to enumerate just CL=24

# For CL=24: binary procs fire 2x, ternary fire 3x
# This is a very constrained problem
# Each binary fires exactly 2x, each ternary fires exactly 3x

print(f"\nConstructing bounce-type words for n=9, CL=24...")

# A systematic approach: BFS/DFS with exact fire count constraints
def enumerate_exact_fc_words(ms, n, target_fc):
    """Enumerate mover words with exact fire counts."""
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    total_len = sum(target_fc.values())
    results = []

    def dfs(word, fc):
        if len(word) == total_len:
            # Check wrap adjacency
            if abs(word[-1] - word[0]) % n in (1, n-1):
                # Check config returns to start
                config = [0] * n
                for p in word:
                    config[p] = (config[p] + 1) % ms[p]
                if all(c == 0 for c in config):
                    results.append(tuple(word))
            return

        last = word[-1]
        for nxt in ring_adj[last]:
            if fc[nxt] < target_fc[nxt]:
                fc[nxt] += 1
                word.append(nxt)
                # Pruning: remaining capacity
                remaining = total_len - len(word)
                needed = sum(target_fc[p] - fc[p] for p in range(n))
                if needed <= remaining:
                    dfs(word, fc)
                word.pop()
                fc[nxt] -= 1

    for p in range(n):
        fc = {q: 0 for q in range(n)}
        fc[p] = 1
        dfs([p], fc)

    return results

target_fc = {}
for p in range(n):
    target_fc[p] = ms_aog[p]  # binary fire 2x, ternary fire 3x

print(f"Target fire counts: {target_fc}")
print(f"Total CL: {sum(target_fc.values())}")
print(f"Enumerating (this may take a while)...")

import time
t0 = time.time()
words_n9 = enumerate_exact_fc_words(ms_aog, n, target_fc)
t1 = time.time()
print(f"Found {len(words_n9)} words in {t1-t0:.1f}s")

# Deduplicate
seen = set()
unique_n9 = []
for w in words_n9:
    canon = canonicalize_word(w)
    if canon not in seen:
        seen.add(canon)
        unique_n9.append(w)
print(f"Unique (up to rotation): {len(unique_n9)}")

# Check which form valid cycles (distinct configs)
valid_n9 = []
for w in unique_n9:
    cycle = build_cycle(ms_aog, n, w)
    if cycle is not None:
        valid_n9.append(w)
print(f"Valid cycles (distinct configs): {len(valid_n9)}")

# Classify all
branch_counts_n9 = Counter()
disp_counts_n9 = Counter()
for w in valid_n9:
    info = classify_cycle(w, ms_aog, n)
    branch_counts_n9[info['branch']] += 1
    disp_counts_n9[info['disp']] += 1

print(f"\nDisplacement distribution:")
for d in sorted(disp_counts_n9.keys()):
    print(f"  disp={d:+3d}: {disp_counts_n9[d]} cycles")

print(f"\nBranch distribution:")
for b in sorted(branch_counts_n9.keys()):
    print(f"  {b}: {branch_counts_n9[b]}")

# Check EC on a sample
print(f"\nEC analysis on sample...")
no_ec_n9 = []
for i, w in enumerate(valid_n9):
    if i >= 20:  # limit to first 20 for speed
        break
    info = classify_cycle(w, ms_aog, n)
    result = check_all_state_combos_ec(w, ms_aog, n, max_combos=100000)
    if result[0] is not None and not result[0]:
        no_ec_n9.append((w, info, result[1], result[2]))
    if result[0] is not None:
        status = "ALL EC" if result[0] else f"{result[1]} no-EC/{result[2]}"
    else:
        status = f"skipped ({result[2]} combos)"
    print(f"  #{i}: CL={len(w)} disp={info['disp']:+d} safe={info['safe']} "
          f"| {info['branch']} | {status}")

if no_ec_n9:
    print(f"\n*** {len(no_ec_n9)} NO-EC cycles found at n=9 ***")
    for w, info, nec, tot in no_ec_n9:
        print(f"  CL={len(w)} disp={info['disp']:+d} cw={info['cw']} "
              f"safe={info['safe']} | {info['branch']} | no_ec={nec}/{tot}")

print("\nDone.")
