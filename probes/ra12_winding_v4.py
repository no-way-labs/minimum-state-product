#!/usr/bin/env python3
"""RA12 v4: Extended winding analysis at n=9 + all sub-threshold multisets.

Key finding from v3: ALL no-EC cycles at n=9 all-odd-gap are SWEEPS (|disp|=18=2n).
Now check all sub-threshold multisets systematically.
"""
import sys
from collections import Counter
from itertools import combinations, product as iproduct
import time


def enumerate_exact_fc_words(ms, n, target_fc):
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
        diff = (word[(i+1) % ell] - word[i]) % n
        if diff == 1:
            total += 1
        elif diff == n - 1:
            total -= 1
    return total


def has_ec_incrementing(word, cycle, ms, n):
    ell = len(word)
    for p in range(n):
        mover = set()
        nonmover = set()
        for s in range(ell):
            ctx = (cycle[s][(p-1) % n], cycle[s][p], cycle[s][(p+1) % n])
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
        if not ({(p-1) % n, p, (p+1) % n} & fired):
            return True, p
    return False, None


def count_cw(word, n):
    cw = 0
    ell = len(word)
    for i in range(ell):
        if (word[(i+1) % ell] - word[i]) % n == 1:
            cw += 1
    return cw


def classify(word, ms, n):
    disp = compute_displacement(word, n)
    cw = count_cw(word, n)
    safe, sp = has_safe_processor(word, n)
    if safe:
        return disp, cw, safe, sp, "B1:safe"
    elif disp == 0:
        return disp, cw, safe, sp, ("B2:zw_cw0" if cw == 0 else "B3:zw_cw>0")
    elif abs(disp) >= 2*n:
        return disp, cw, safe, sp, "B4a:sweep"
    elif abs(disp) == n:
        return disp, cw, safe, sp, "B4b:odd-wind"
    else:
        return disp, cw, safe, sp, f"B4?:disp={disp}"


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


def check_all_combos_ec(word, ms, n, max_combos=200000):
    ell = len(word)
    fc = Counter(word)
    proc_seqs = {}
    total = 1
    for p in range(n):
        proc_seqs[p] = enumerate_state_sequences(ms[p], fc[p])
        total *= len(proc_seqs[p])
    if total > max_combos:
        return None, None, total

    proc_steps = {p: [] for p in range(n)}
    for s in range(ell):
        proc_steps[word[s]].append(s)
    firing_num = [0] * ell
    pc = [0] * n
    for s in range(ell):
        p = word[s]
        firing_num[s] = pc[p]
        pc[p] += 1

    no_ec = 0
    for combo in iproduct(*[proc_seqs[p] for p in range(n)]):
        state = [0] * n
        mover_ctx = [set() for _ in range(n)]
        nonmover_ctx = [set() for _ in range(n)]
        for s in range(ell):
            for q in range(n):
                ctx = (state[(q-1) % n], state[q], state[(q+1) % n])
                if word[s] == q:
                    mover_ctx[q].add(ctx)
                else:
                    nonmover_ctx[q].add(ctx)
            p = word[s]
            state[p] = combo[p][firing_num[s] + 1]
        has_ec = any(mover_ctx[q] & nonmover_ctx[q] for q in range(n))
        if not has_ec:
            no_ec += 1
    return no_ec == 0, no_ec, total


# ============================================================
print("=" * 72)
print("RA12 v4: COMPREHENSIVE n=9 WINDING ANALYSIS")
print("=" * 72)
sys.stdout.flush()

n = 9
threshold = 4 * 3**7

# Generate ALL sub-threshold non-consecutive-binary multisets
all_ms = []
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
            # Canonicalize by gap pattern to avoid redundant rotations
            all_ms.append((ms, positions))

print(f"Total non-consecutive >=3 binary sub-threshold: {len(all_ms)}")

# Group by sorted gap pattern
gap_groups = {}
for ms, positions in all_ms:
    bp = sorted(positions)
    nb = len(bp)
    gaps = tuple(sorted([(bp[(i+1)%nb] - bp[i]) % n for i in range(nb)]))
    prod = 1
    for m in ms:
        prod *= m
    key = (nb, gaps, prod)
    if key not in gap_groups:
        gap_groups[key] = []
    gap_groups[key].append((ms, positions))

print(f"Distinct gap patterns: {len(gap_groups)}")
for key in sorted(gap_groups.keys()):
    nb, gaps, prod = key
    print(f"  {nb} binary, gaps={gaps}, prod={prod}: {len(gap_groups[key])} orientations")
sys.stdout.flush()

# For each gap pattern, test ONE representative
print(f"\n{'='*60}")
print("Testing one representative per gap pattern")
print(f"{'='*60}")
sys.stdout.flush()

grand_total = Counter()  # branch -> count
grand_no_ec_inc = Counter()
grand_no_ec_any = Counter()
all_no_ec_details = []

for key in sorted(gap_groups.keys()):
    nb, gaps, prod = key
    ms, positions = gap_groups[key][0]

    print(f"\n--- {nb}bin gaps={gaps} prod={prod} ms={ms} ---")
    sys.stdout.flush()

    target_fc = {p: ms[p] for p in range(n)}
    cl = sum(ms[p] for p in range(n))

    t0 = time.time()
    words = enumerate_exact_fc_words(ms, n, target_fc)
    t1 = time.time()

    # Deduplicate
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

    print(f"  CL={cl}, raw={len(words)}, unique={len(unique)}, valid={len(valid)} ({t1-t0:.1f}s)")

    if not valid:
        print(f"  No valid cycles")
        continue

    # Classify
    branch_cnt = Counter()
    disp_cnt = Counter()
    no_inc_ec = []

    for w, cycle in valid:
        disp, cw, safe, sp, branch = classify(w, ms, n)
        branch_cnt[branch] += 1
        disp_cnt[disp] += 1
        grand_total[branch] += 1

        if not has_ec_incrementing(w, cycle, ms, n):
            no_inc_ec.append((w, cycle, disp, cw, safe, sp, branch))
            grand_no_ec_inc[branch] += 1

    print(f"  Disp: {dict(sorted(disp_cnt.items()))}")
    print(f"  Branch: {dict(sorted(branch_cnt.items()))}")
    print(f"  No-inc-EC: {len(no_inc_ec)}")

    if no_inc_ec:
        # Full combo check
        no_any_ec = []
        for w, cycle, disp, cw, safe, sp, branch in no_inc_ec:
            result = check_all_combos_ec(w, ms, n)
            if result[0] is not None and not result[0]:
                no_any_ec.append((w, disp, cw, safe, sp, branch, result[1], result[2]))
                grand_no_ec_any[branch] += 1
                all_no_ec_details.append((ms, w, disp, cw, safe, branch, result[1], result[2]))
            elif result[0] is None:
                no_any_ec.append((w, disp, cw, safe, sp, branch, '?', result[2]))
                grand_no_ec_any[branch + "(unk)"] += 1
                all_no_ec_details.append((ms, w, disp, cw, safe, branch+"(unk)", '?', result[2]))

        print(f"  No-ANY-EC: {len(no_any_ec)}")
        for w, disp, cw, safe, sp, branch, nec, tot in no_any_ec[:5]:
            print(f"    CL={len(w)} disp={disp:+d} cw={cw} safe={safe}({sp}) "
                  f"no_ec={nec}/{tot} | {branch}")
    sys.stdout.flush()

# ============================================================
print(f"\n{'='*72}")
print("GRAND SUMMARY")
print(f"{'='*72}")
print(f"\nAll cycles by branch: {dict(sorted(grand_total.items()))}")
print(f"No-inc-EC by branch: {dict(sorted(grand_no_ec_inc.items()))}")
print(f"No-ANY-EC by branch: {dict(sorted(grand_no_ec_any.items()))}")

if all_no_ec_details:
    print(f"\nAll no-EC cycles:")
    for ms, w, disp, cw, safe, branch, nec, tot in all_no_ec_details:
        bp = [i for i, m in enumerate(ms) if m == 2]
        print(f"  ms={ms} bin@{bp} CL={len(w)} disp={disp:+d} cw={cw} safe={safe} "
              f"no_ec={nec}/{tot} | {branch}")

    # Key question answers
    print(f"\n--- KEY ANSWERS ---")
    branches_seen = set(b for _, _, _, _, _, b, _, _ in all_no_ec_details)
    print(f"Branches with no-EC cycles: {branches_seen}")
    print(f"Any odd-winding (B4b)? {'B4b:odd-wind' in branches_seen}")
    print(f"Any sweep (B4a)? {'B4a:sweep' in branches_seen}")
    print(f"Any zero-winding (B3)? {'B3:zw_cw>0' in branches_seen}")

    disps = set(d for _, _, d, _, _, _, _, _ in all_no_ec_details)
    print(f"Displacement values: {sorted(disps)}")
    print(f"|disp|/n values: {sorted(set(abs(d)//n for d in disps if d != 0))}")

print("\nDone.")
