#!/usr/bin/env python3
"""RA12 v3: Fast winding analysis for no-EC good cycles.

Focus: displacement/winding classification. Use incrementing-transition
EC check (fast) to identify EC-free cycles, then do full state-combo
check only on those.
"""
import sys
from collections import Counter
from itertools import combinations, product as iproduct
import time


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


def enumerate_exact_fc_words(ms, n, target_fc):
    """Enumerate mover words with exact fire counts."""
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    total_len = sum(target_fc[p] for p in range(n))
    results = []
    def dfs(word, fc):
        if len(word) == total_len:
            if abs(word[-1] - word[0]) % n in (1, n-1):
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
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:ell])) != ell:
        return None
    return configs[:ell]


def canonicalize_word(word):
    best = word
    for i in range(len(word)):
        rot = word[i:] + word[:i]
        if rot < best:
            best = rot
    return best


def compute_displacement(word, n):
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
    return total


def has_ec_incrementing(word, cycle, ms, n):
    """Check EC using incrementing transition (fast)."""
    ell = len(word)
    for p in range(n):
        mover = set()
        nonmover = set()
        for s in range(ell):
            L = cycle[s][(p-1) % n]
            S = cycle[s][p]
            R = cycle[s][(p+1) % n]
            ctx = (L, S, R)
            if word[s] == p:
                mover.add(ctx)
            else:
                nonmover.add(ctx)
        if mover & nonmover:
            return True
    return False


def has_safe_processor(word, n):
    fired = set(word)
    for p in range(n):
        neighbors = {(p-1) % n, p, (p+1) % n}
        if not (neighbors & fired):
            return True, p
    return False, None


def count_cw(word, n):
    cw = 0
    ell = len(word)
    for i in range(ell):
        diff = (word[(i+1) % ell] - word[i]) % n
        if diff == 1:
            cw += 1
    return cw


def classify(word, ms, n):
    disp = compute_displacement(word, n)
    cw = count_cw(word, n)
    ccw = len(word) - cw
    safe, sp = has_safe_processor(word, n)

    if safe:
        branch = "B1:safe"
    elif disp == 0:
        if cw == 0:
            branch = "B2:zw_cw0"
        else:
            branch = "B3:zw_cw>0"
    elif abs(disp) >= 2*n:
        branch = "B4a:sweep"
    elif abs(disp) == n:
        branch = "B4b:odd-wind"
    else:
        branch = f"B4?:disp={disp}"
    return disp, cw, ccw, safe, sp, branch


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


def check_all_combos_ec(word, ms, n, max_combos=50000):
    """Full state-combo EC check. Returns (all_ec, no_ec_count, total)."""
    ell = len(word)
    fc = Counter(word)

    proc_seqs = {}
    total = 1
    for p in range(n):
        k = fc[p]
        proc_seqs[p] = enumerate_state_sequences(ms[p], k)
        total *= len(proc_seqs[p])

    if total > max_combos:
        return None, None, total

    proc_steps = {p: [] for p in range(n)}
    for s in range(ell):
        proc_steps[word[s]].append(s)

    # Build firing index map: for step s, which firing number is it?
    firing_num = [0] * ell
    proc_count = [0] * n
    for s in range(ell):
        p = word[s]
        firing_num[s] = proc_count[p]
        proc_count[p] += 1

    no_ec = 0
    seq_lists = [proc_seqs[p] for p in range(n)]

    for combo in iproduct(*seq_lists):
        # Build config at each step
        state = [0] * n
        has_ec = False

        # Collect (proc, context, is_mover) tuples
        mover_ctx = [set() for _ in range(n)]
        nonmover_ctx = [set() for _ in range(n)]

        for s in range(ell):
            # Record context BEFORE firing
            for q in range(n):
                ctx = (state[(q-1) % n], state[q], state[(q+1) % n])
                if word[s] == q:
                    mover_ctx[q].add(ctx)
                else:
                    nonmover_ctx[q].add(ctx)

            # Apply firing
            p = word[s]
            fn = firing_num[s]
            state[p] = combo[p][fn + 1]

        for q in range(n):
            if mover_ctx[q] & nonmover_ctx[q]:
                has_ec = True
                break

        if not has_ec:
            no_ec += 1

    return no_ec == 0, no_ec, total


# ============================================================
print("=" * 72)
print("RA12: WINDING ANALYSIS FOR NO-EC GOOD CYCLES")
print("=" * 72)
sys.stdout.flush()

for n_val, max_len_val in [(5, 16), (6, 20), (7, 24)]:
    print(f"\n{'='*60}")
    print(f"n = {n_val}, threshold = {4 * 3**(n_val-2)}")
    print(f"{'='*60}")
    sys.stdout.flush()

    threshold = 4 * 3**(n_val - 2)

    # Generate non-consecutive binary multisets
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

    print(f"Multisets: {len(multisets)}")

    all_branch = Counter()
    no_ec_inc_branch = Counter()  # no EC with incrementing
    no_ec_any_branch = Counter()  # no EC with ANY transition

    for ms in multisets:
        bp = [i for i, m in enumerate(ms) if m == 2]
        prod = 1
        for m in ms:
            prod *= m

        t0 = time.time()
        words = enumerate_mover_words(ms, n_val, max_len_val)
        t1 = time.time()

        # Deduplicate
        seen = set()
        unique = []
        for w in words:
            canon = canonicalize_word(w)
            if canon not in seen:
                seen.add(canon)
                unique.append(w)

        # Filter valid
        valid = []
        for w in unique:
            if abs(w[-1] - w[0]) % n_val not in (1, n_val-1):
                continue
            cycle = build_cycle(ms, n_val, w)
            if cycle is not None:
                valid.append((w, cycle))

        if not valid:
            continue

        # First pass: classify all and check incrementing EC
        no_inc_ec = []  # cycles without incrementing-EC
        for w, cycle in valid:
            disp, cw, ccw, safe, sp, branch = classify(w, ms, n_val)
            all_branch[branch] += 1

            if not has_ec_incrementing(w, cycle, ms, n_val):
                no_inc_ec.append((w, cycle, disp, cw, ccw, safe, sp, branch))
                no_ec_inc_branch[branch] += 1

        # Second pass: for no-inc-EC cycles, check all combos
        no_any_ec = []
        for w, cycle, disp, cw, ccw, safe, sp, branch in no_inc_ec:
            result = check_all_combos_ec(w, ms, n_val, max_combos=100000)
            if result[0] is not None and not result[0]:
                no_any_ec.append((w, disp, cw, safe, sp, branch, result[1], result[2]))
                no_ec_any_branch[branch] += 1
            elif result[0] is None:
                # Too many combos - report as unknown
                no_any_ec.append((w, disp, cw, safe, sp, branch, '?', result[2]))
                no_ec_any_branch[branch + "(unk)"] += 1

        if no_any_ec:
            print(f"\n  ms={ms} prod={prod} bin@{bp}: {len(valid)} cycles, "
                  f"{len(no_inc_ec)} no-inc-EC, {len(no_any_ec)} no-ANY-EC")
            for w, disp, cw, safe, sp, branch, nec, tot in no_any_ec[:5]:
                print(f"    CL={len(w)} disp={disp:+d} cw={cw} safe={safe}({sp}) "
                      f"no_ec={nec}/{tot} | {branch}")
        sys.stdout.flush()

    print(f"\n  --- TOTALS for n={n_val} ---")
    print(f"  All cycles by branch: {dict(sorted(all_branch.items()))}")
    print(f"  No-inc-EC by branch: {dict(sorted(no_ec_inc_branch.items()))}")
    print(f"  No-ANY-EC by branch: {dict(sorted(no_ec_any_branch.items()))}")
    sys.stdout.flush()


# ============================================================
# n=9: Targeted enumeration
# ============================================================
print(f"\n{'='*60}")
print(f"n = 9: TARGETED ENUMERATION")
print(f"{'='*60}")
sys.stdout.flush()

n = 9
threshold = 4 * 3**7
print(f"Threshold: {threshold}")

# Test multisets
test_ms = [
    ([2,3,3,2,3,3,2,3,3], "all-odd-gap"),
    ([2,3,2,3,2,3,3,3,3], "3bin@0,2,4"),
    ([2,3,3,3,2,3,3,3,2], "gaps-of-2"),
]

for ms, label in test_ms:
    bp = [i for i, m in enumerate(ms) if m == 2]
    prod = 1
    for m in ms:
        prod *= m

    print(f"\n--- {label}: ms={ms}, prod={prod}, bin@{bp} ---")
    sys.stdout.flush()

    # Enumerate with exact fire counts (CL = sum of ms[p])
    target_fc = {p: ms[p] for p in range(n)}
    cl = sum(ms[p] for p in range(n))
    print(f"  Minimum CL = {cl}")

    t0 = time.time()
    words = enumerate_exact_fc_words(ms, n, target_fc)
    t1 = time.time()
    print(f"  Raw words: {len(words)} ({t1-t0:.1f}s)")
    sys.stdout.flush()

    # Deduplicate
    seen = set()
    unique = []
    for w in words:
        canon = canonicalize_word(w)
        if canon not in seen:
            seen.add(canon)
            unique.append(w)
    print(f"  Unique: {len(unique)}")

    # Build cycles
    valid = []
    for w in unique:
        cycle = build_cycle(ms, n, w)
        if cycle is not None:
            valid.append((w, cycle))
    print(f"  Valid cycles: {len(valid)}")

    # Classify
    branch_cnt = Counter()
    disp_cnt = Counter()
    no_inc_ec = []

    for w, cycle in valid:
        disp, cw, ccw, safe, sp, branch = classify(w, ms, n)
        branch_cnt[branch] += 1
        disp_cnt[disp] += 1

        if not has_ec_incrementing(w, cycle, ms, n):
            no_inc_ec.append((w, cycle, disp, cw, ccw, safe, sp, branch))

    print(f"\n  Displacement dist: {dict(sorted(disp_cnt.items()))}")
    print(f"  Branch dist: {dict(sorted(branch_cnt.items()))}")
    print(f"  No-inc-EC: {len(no_inc_ec)}")

    if no_inc_ec:
        # Check all combos on no-inc-EC cycles
        no_any_ec = []
        for w, cycle, disp, cw, ccw, safe, sp, branch in no_inc_ec:
            result = check_all_combos_ec(w, ms, n, max_combos=200000)
            if result[0] is not None and not result[0]:
                no_any_ec.append((w, disp, cw, safe, sp, branch, result[1], result[2]))
            elif result[0] is None:
                no_any_ec.append((w, disp, cw, safe, sp, branch, '?', result[2]))

        print(f"  No-ANY-EC: {len(no_any_ec)}")
        no_ec_branches = Counter()
        for w, disp, cw, safe, sp, branch, nec, tot in no_any_ec:
            no_ec_branches[branch] += 1
            print(f"    CL={len(w)} disp={disp:+d} cw={cw} safe={safe}({sp}) "
                  f"no_ec={nec}/{tot} | {branch}")

        if no_ec_branches:
            print(f"\n  No-EC branch summary: {dict(sorted(no_ec_branches.items()))}")

    sys.stdout.flush()

print("\n" + "=" * 72)
print("DONE")
print("=" * 72)
