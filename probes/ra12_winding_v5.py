#!/usr/bin/env python3
"""RA12 v5: Detailed sweep word structure + n=8 check + word examples."""
import sys
from collections import Counter
from itertools import combinations, product as iproduct


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
        firing_num[s] = pc[word[s]]
        pc[word[s]] += 1

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
        if not any(mover_ctx[q] & nonmover_ctx[q] for q in range(n)):
            no_ec += 1
    return no_ec == 0, no_ec, total


# ============================================================
print("=" * 72)
print("RA12 v5: SWEEP WORD STRUCTURE")
print("=" * 72)
sys.stdout.flush()

# Show the 8 no-EC sweep words at n=9
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

print(f"\nn=9, ms={ms}")
print(f"Total valid cycles: {len(valid)}")

# Show all sweep cycles (|disp| = 2n = 18)
print(f"\nSWEEP CYCLES (|disp| = {2*n}):")
sweep_count = 0
for w, cycle in valid:
    disp = compute_displacement(w, n)
    if abs(disp) == 2*n:
        sweep_count += 1
        cw = sum(1 for i in range(len(w)) if (w[(i+1)%len(w)] - w[i]) % n == 1)
        fired = set(w)
        safe_procs = [p for p in range(n) if not ({(p-1)%n, p, (p+1)%n} & fired)]

        # Show step directions
        dirs = []
        for i in range(len(w)):
            diff = (w[(i+1)%len(w)] - w[i]) % n
            dirs.append('+' if diff == 1 else '-')

        print(f"\n  Word: {list(w)}")
        print(f"  Dirs: {''.join(dirs)}")
        print(f"  disp={disp:+d}, cw={cw}, ccw={len(w)-cw}")
        print(f"  Safe procs: {safe_procs}")

        # Check: is this literally a pure sweep (all same direction)?
        if all(d == '+' for d in dirs):
            print(f"  TYPE: Pure CW sweep")
        elif all(d == '-' for d in dirs):
            print(f"  TYPE: Pure CCW sweep")
        else:
            print(f"  TYPE: Mixed-direction sweep (net winding = {disp//n})")

        # EC check
        has_ec = has_ec_incrementing(w, cycle, ms, n)
        result = check_all_combos_ec(w, ms, n)
        print(f"  Inc-EC: {has_ec}, All-combos: all_ec={result[0]}, no_ec={result[1]}/{result[2]}")

print(f"\nTotal sweeps: {sweep_count}")

# Show a few zero-winding cycles for comparison
print(f"\nZERO-WINDING CYCLES (sample):")
zw_count = 0
for w, cycle in valid:
    disp = compute_displacement(w, n)
    if disp == 0:
        zw_count += 1
        if zw_count <= 3:
            cw = sum(1 for i in range(len(w)) if (w[(i+1)%len(w)] - w[i]) % n == 1)
            dirs = []
            for i in range(len(w)):
                diff = (w[(i+1)%len(w)] - w[i]) % n
                dirs.append('+' if diff == 1 else '-')
            has_ec = has_ec_incrementing(w, cycle, ms, n)
            print(f"\n  Word: {list(w)}")
            print(f"  Dirs: {''.join(dirs)}")
            print(f"  disp=0, cw={cw}, ccw={len(w)-cw}")
            print(f"  Inc-EC: {has_ec}")

print(f"Total zero-winding: {zw_count}")


# ============================================================
# n=8 check (to see if pattern holds)
# ============================================================
print(f"\n{'='*72}")
print(f"n=8 CHECK")
print(f"{'='*72}")
sys.stdout.flush()

n = 8
threshold = 4 * 3**(n-2)

# Generate all non-consecutive >=3 binary
all_ms_n8 = []
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
            all_ms_n8.append(ms)

print(f"Sub-threshold multisets: {len(all_ms_n8)}")

# Group by gap pattern
gap_groups = {}
for ms in all_ms_n8:
    bp = [i for i, m in enumerate(ms) if m == 2]
    nb = len(bp)
    gaps = tuple(sorted([(bp[(i+1)%nb] - bp[i]) % n for i in range(nb)]))
    prod = 1
    for m in ms:
        prod *= m
    key = (nb, gaps, prod)
    if key not in gap_groups:
        gap_groups[key] = []
    gap_groups[key].append(ms)

for key in sorted(gap_groups.keys()):
    nb, gaps, prod = key
    ms = gap_groups[key][0]
    bp = [i for i, m in enumerate(ms) if m == 2]

    print(f"\n--- {nb}bin gaps={gaps} prod={prod} ms={ms} ---")
    sys.stdout.flush()

    target_fc = {p: ms[p] for p in range(n)}
    cl = sum(ms[p] for p in range(n))

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

    print(f"  CL={cl}, valid={len(valid)}")

    if not valid:
        continue

    branch_cnt = Counter()
    no_inc_ec_words = []
    for w, cycle in valid:
        disp = compute_displacement(w, n)
        cw = sum(1 for i in range(len(w)) if (w[(i+1)%len(w)] - w[i]) % n == 1)
        fired = set(w)
        safe = any(not ({(p-1)%n, p, (p+1)%n} & fired) for p in range(n))
        if safe:
            b = "B1:safe"
        elif disp == 0:
            b = "B2:zw_cw0" if cw == 0 else "B3:zw_cw>0"
        elif abs(disp) >= 2*n:
            b = "B4a:sweep"
        elif abs(disp) == n:
            b = "B4b:odd-wind"
        else:
            b = f"B4?:{disp}"
        branch_cnt[b] += 1

        if not has_ec_incrementing(w, cycle, ms, n):
            no_inc_ec_words.append((w, disp, b))

    print(f"  Branches: {dict(sorted(branch_cnt.items()))}")
    print(f"  No-inc-EC: {len(no_inc_ec_words)}")

    if no_inc_ec_words:
        for w, disp, b in no_inc_ec_words[:3]:
            result = check_all_combos_ec(w, ms, n)
            status = f"no_ec={result[1]}/{result[2]}" if result[0] is not None else f"skip({result[2]})"
            print(f"    disp={disp:+d} | {b} | {status}")
    sys.stdout.flush()


# ============================================================
# Key structural insight about the sweep words
# ============================================================
print(f"\n{'='*72}")
print("STRUCTURAL ANALYSIS OF SWEEP WORDS")
print(f"{'='*72}")

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
valid = [(w, build_cycle(ms, n, w)) for w in unique if build_cycle(ms, n, w) is not None]

sweeps = [(w, c) for w, c in valid if abs(compute_displacement(w, n)) == 2*n]
print(f"\n{len(sweeps)} sweep words at n=9:")

for w, c in sweeps:
    disp = compute_displacement(w, n)
    # Decompose into "segments" between direction changes
    dirs = [(w[(i+1)%len(w)] - w[i]) % n for i in range(len(w))]
    dir_signs = [1 if d == 1 else -1 for d in dirs]

    # Count consecutive same-direction runs
    runs = []
    cur_dir = dir_signs[0]
    cur_len = 1
    for i in range(1, len(dir_signs)):
        if dir_signs[i] == cur_dir:
            cur_len += 1
        else:
            runs.append(('+' if cur_dir == 1 else '-', cur_len))
            cur_dir = dir_signs[i]
            cur_len = 1
    runs.append(('+' if cur_dir == 1 else '-', cur_len))

    print(f"  disp={disp:+d} runs={runs}")

print("\nDone.")
