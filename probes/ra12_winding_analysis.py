#!/usr/bin/env python3
"""RA12: Winding number analysis for no-EC good cycles at n=9.

For each sub-threshold multiset with >=3 non-consecutive binary at n=9,
enumerate good cycles, check for entry conflict, and classify by:
- totalDisplacement (sum of mover steps as +1/-1 on the ring)
- winding number = totalDisplacement / n
- safe processor (proc where neither it nor neighbors ever fire as mover)
- which sorry branch they fall into

Proof branches (ZeroWindingAssembly.lean):
  1. Safe processor -> done
  2. Zero winding, cw=0 -> done
  3. Zero winding, cw>0 -> palindromic EC (sorrys 1, 4a-c)
  4. Non-zero winding -> sweep (|disp| >= 2n) or odd-winding (|disp| = n)
     - sorry 5: non-zero winding dispatch
     - sorry 6: sweep branch
     - sorry 7: odd-winding branch
"""

from collections import Counter
from itertools import product as iproduct
import sys


def get_binary_positions(ms):
    return [i for i, m in enumerate(ms) if m == 2]


def are_consecutive(positions, n):
    """Check if any two binary positions are adjacent on the ring."""
    for i in range(len(positions)):
        for j in range(i+1, len(positions)):
            if abs(positions[i] - positions[j]) % n in (1, n-1):
                return True
    return False


def enumerate_mover_words(ms, n, max_length):
    """Enumerate all valid mover words (good cycles)."""
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
    """Return canonical rotation of word."""
    best = word
    for i in range(len(word)):
        rot = word[i:] + word[:i]
        if rot < best:
            best = rot
    return best


def compute_total_displacement(word, n):
    """Total displacement = sum of signed steps around the ring.
    Each step word[i] -> word[i+1] contributes +1 (CW) or -1 (CCW).
    Wrap: word[-1] -> word[0] also counted."""
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
            # Non-adjacent step — shouldn't happen for valid mover words
            raise ValueError(f"Non-adjacent step: {cur} -> {nxt}")
    return total


def has_entry_conflict_at_any_proc(word, cycle, ms, n):
    """Check if cycle has entry conflict at ANY processor."""
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
    """A safe processor is one where neither it nor its neighbors ever fire as mover."""
    fired = set(word)
    for p in range(n):
        neighbors = {(p-1) % n, p, (p+1) % n}
        if not (neighbors & fired):
            return True, p
    return False, None


def count_cw_steps(word, n):
    """Count clockwise steps in the mover word."""
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
    """Enumerate all state sequences of length k for a proc with m states,
    starting and ending at 0."""
    seqs = []
    def dfs(seq, remaining):
        if remaining == 0:
            if seq[-1] == 0:
                seqs.append(list(seq))
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


def check_all_state_combos_ec(word, ms, n):
    """Check if EVERY state-sequence combo has entry conflict.
    Returns (all_have_ec, num_no_ec_combos, total_combos)."""
    ell = len(word)
    fc = Counter(word)

    # For each proc, enumerate valid state sequences
    proc_seqs = {}
    for p in range(n):
        k = fc[p]
        proc_seqs[p] = enumerate_state_sequences(ms[p], k)

    # Build the configs from state sequences
    # For each combo, construct full cycle and check EC
    no_ec_count = 0
    total = 1
    for p in range(n):
        total *= len(proc_seqs[p])

    if total > 500000:
        # Too many combos, skip exhaustive check
        return None, None, total

    # Map: for each proc, the steps where it fires
    proc_steps = {p: [] for p in range(n)}
    for s in range(ell):
        proc_steps[word[s]].append(s)

    # Iterate over all combos
    combo_count = 0
    no_ec_examples = []

    def iterate_combos(p_idx, assignment):
        nonlocal combo_count, no_ec_count
        if p_idx == n:
            combo_count += 1
            # Build cycle from assignment
            cycle = [list(range(n)) for _ in range(ell)]  # placeholder
            # Actually build config sequence
            configs = [[0]*n for _ in range(ell + 1)]
            for s in range(ell):
                for q in range(n):
                    configs[s+1][q] = configs[s][q]
                p = word[s]
                # Find which firing this is for proc p
                idx = proc_steps[p].index(s) if s in proc_steps[p] else -1
                firing_num = sum(1 for prev_s in proc_steps[p] if prev_s < s)
                new_val = assignment[p][firing_num + 1]
                configs[s+1][p] = new_val

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
                    no_ec_examples.append(dict(assignment))
            return

        for seq in proc_seqs[p_idx]:
            assignment[p_idx] = seq
            iterate_combos(p_idx + 1, assignment)

    assignment = {}
    iterate_combos(0, assignment)

    return no_ec_count == 0, no_ec_count, combo_count, no_ec_examples


def classify_cycle(word, ms, n):
    """Classify a cycle into proof branches."""
    ell = len(word)
    disp = compute_total_displacement(word, n)
    cw = count_cw_steps(word, n)
    ccw = ell - cw
    safe, safe_p = has_safe_processor(word, n)

    winding = disp // n if disp % n == 0 else None

    if safe:
        branch = "Branch 1: safe processor"
    elif disp == 0:
        if cw == 0:
            branch = "Branch 2: zero winding, cw=0"
        else:
            branch = "Branch 3: zero winding, cw>0 (sorrys 1, 4a-c)"
    elif abs(disp) >= 2 * n:
        branch = "Branch 4a: sweep (sorry 6)"
    elif abs(disp) == n:
        branch = "Branch 4b: odd-winding (sorry 7)"
    else:
        branch = f"Branch 4?: non-zero winding disp={disp} (unexpected)"

    return {
        'disp': disp,
        'winding': winding,
        'cw': cw,
        'ccw': ccw,
        'safe': safe,
        'safe_proc': safe_p,
        'branch': branch,
    }


# ============================================================
# MAIN
# ============================================================

print("=" * 72)
print("RA12: WINDING ANALYSIS FOR NO-EC GOOD CYCLES AT n=9")
print("=" * 72)

n = 9

# Generate candidate multisets with >=3 non-consecutive binary, product < 4*3^7 = 8748
# We focus on specific interesting ones mentioned in the question
test_multisets = [
    [2,3,3,2,3,3,2,3,3],  # all-odd-gap (gaps of 1 ternary)
    [2,3,2,3,2,3,3,3,3],  # 3 binary at 0,2,4
    [2,3,3,3,2,3,3,3,2],  # gaps of 2
    [2,3,3,3,3,2,3,2,3],  # mixed gaps
]

# Also generate all rotations to find distinct multisets
from itertools import combinations

def generate_sub_threshold_multisets(n):
    """Generate multisets with >=3 binary, non-consecutive, product < 4*3^(n-2)."""
    threshold = 4 * (3 ** (n - 2))
    results = []
    # Choose positions for binary (value 2), rest ternary (value 3)
    for num_bin in range(3, n+1):
        for positions in combinations(range(n), num_bin):
            # Check non-consecutive
            pos_set = set(positions)
            consec = False
            for p in positions:
                if (p+1) % n in pos_set:
                    consec = True
                    break
            if consec:
                continue

            ms = [3] * n
            for p in positions:
                ms[p] = 2
            prod = 1
            for m in ms:
                prod *= m
            if prod < threshold:
                results.append(ms)
    return results

all_multisets = generate_sub_threshold_multisets(n)
print(f"\nTotal non-consecutive-binary sub-threshold multisets at n=9: {len(all_multisets)}")

# Show products
products = set()
for ms in all_multisets:
    p = 1
    for m in ms:
        p *= m
    products.add(p)
print(f"Products represented: {sorted(products)}")

# For n=9, max_length for enumeration
# CL for bounce = 24 (binary fire 2x, ternary fire 3x)
# But we should also check CL up to ~27 to catch other cycle types
max_len = 27

# First: detailed analysis of the all-odd-gap family
print("\n" + "=" * 72)
print("DETAILED: All-odd-gap ms=[2,3,3,2,3,3,2,3,3]")
print("=" * 72)

ms_aog = [2,3,3,2,3,3,2,3,3]
prod_aog = 1
for m in ms_aog:
    prod_aog *= m
print(f"Product: {prod_aog}, threshold: {4 * 3**7} = {4 * 3**7}")
bin_pos = get_binary_positions(ms_aog)
print(f"Binary positions: {bin_pos}")
print(f"Non-consecutive: {not are_consecutive(bin_pos, n)}")

print(f"\nEnumerating mover words (max_len={max_len})...")
words = enumerate_mover_words(ms_aog, n, max_len)
print(f"Raw words: {len(words)}")

# Deduplicate by canonical rotation
seen = set()
unique_words = []
for w in words:
    canon = canonicalize_word(w)
    if canon not in seen:
        seen.add(canon)
        unique_words.append(w)

print(f"Unique words (up to rotation): {len(unique_words)}")

# Filter valid cycles with wrap-adjacency
valid_words = []
for w in unique_words:
    if is_wrap_adjacent(w, n):
        cycle = build_cycle(ms_aog, n, w)
        if cycle is not None:
            valid_words.append(w)

print(f"Valid wrap-adjacent cycles: {len(valid_words)}")

# Classify each valid cycle
branch_counts = Counter()
disp_counts = Counter()
no_ec_by_branch = Counter()

print(f"\nClassifying cycles...")
for w in valid_words:
    info = classify_cycle(w, ms_aog, n)
    branch_counts[info['branch']] += 1
    disp_counts[info['disp']] += 1

print(f"\nDisplacement distribution:")
for d in sorted(disp_counts.keys()):
    print(f"  disp={d:+3d}: {disp_counts[d]} cycles")

print(f"\nBranch distribution:")
for b in sorted(branch_counts.keys()):
    print(f"  {b}: {branch_counts[b]}")

# Now check EC for all state-sequence combos on a few representative cycles
print(f"\n--- EC analysis (all state-sequence combos) ---")

# Group by displacement
by_disp = {}
for w in valid_words:
    d = compute_total_displacement(w, n)
    if d not in by_disp:
        by_disp[d] = []
    by_disp[d].append(w)

# For each displacement class, check a sample
for d in sorted(by_disp.keys()):
    sample = by_disp[d][:3]  # check up to 3 per class
    for w in sample:
        info = classify_cycle(w, ms_aog, n)
        fc = Counter(w)
        result = check_all_state_combos_ec(w, ms_aog, n)
        if result[0] is None:
            ec_status = f"TOO MANY COMBOS ({result[2]})"
        elif result[0]:
            ec_status = f"ALL have EC ({result[2]} combos)"
        else:
            ec_status = f"*** {result[1]} NO-EC out of {result[2]} combos ***"

        print(f"\n  Word (first 20): {list(w)[:20]}{'...' if len(w)>20 else ''}")
        print(f"  CL={len(w)}, fc={dict(fc)}")
        print(f"  disp={info['disp']}, cw={info['cw']}, ccw={info['ccw']}")
        print(f"  safe={info['safe']} (proc={info['safe_proc']})")
        print(f"  Branch: {info['branch']}")
        print(f"  EC: {ec_status}")


# ============================================================
# COMPREHENSIVE: All multisets
# ============================================================
print("\n" + "=" * 72)
print("COMPREHENSIVE: All non-consecutive-binary sub-threshold multisets")
print("=" * 72)

# We'll look at a representative set (checking all would be slow at n=9)
# Focus on the ones from the question + a few more
check_multisets = [
    [2,3,3,2,3,3,2,3,3],  # all-odd-gap
    [2,3,2,3,2,3,3,3,3],  # 3 binary at 0,2,4
    [2,3,3,3,2,3,3,3,2],  # gaps of 2
]

# Also find all 3-binary multisets (smaller enumeration)
three_binary = [ms for ms in all_multisets if sum(1 for m in ms if m == 2) == 3]
print(f"\n3-binary multisets: {len(three_binary)}")

# Group by gap pattern
gap_patterns = {}
for ms in three_binary:
    bp = get_binary_positions(ms)
    gaps = tuple(sorted([(bp[(i+1)%3] - bp[i]) % n for i in range(3)]))
    if gaps not in gap_patterns:
        gap_patterns[gaps] = []
    gap_patterns[gaps].append(ms)

print("Gap patterns:")
for g, mss in sorted(gap_patterns.items()):
    print(f"  gaps={g}: {len(mss)} multisets (e.g. {mss[0]})")

# For each gap pattern, check one representative
for gaps, mss in sorted(gap_patterns.items()):
    ms = mss[0]
    prod = 1
    for m in ms:
        prod *= m
    bp = get_binary_positions(ms)

    print(f"\n--- Gap pattern {gaps}, ms={ms}, prod={prod} ---")

    words = enumerate_mover_words(ms, n, max_len)

    # Deduplicate
    seen = set()
    unique = []
    for w in words:
        canon = canonicalize_word(w)
        if canon not in seen:
            seen.add(canon)
            unique.append(w)

    valid = [w for w in unique if is_wrap_adjacent(w, n) and build_cycle(ms, n, w) is not None]
    print(f"  Valid cycles: {len(valid)}")

    if len(valid) == 0:
        continue

    # Classify all
    bc = Counter()
    dc = Counter()
    for w in valid:
        info = classify_cycle(w, ms, n)
        bc[info['branch']] += 1
        dc[info['disp']] += 1

    print(f"  Displacement: {dict(sorted(dc.items()))}")
    print(f"  Branches:")
    for b in sorted(bc.keys()):
        print(f"    {b}: {bc[b]}")

    # Check EC on non-zero-displacement cycles (if any)
    no_ec_found = []
    for w in valid:
        info = classify_cycle(w, ms, n)
        result = check_all_state_combos_ec(w, ms, n)
        if result[0] is not None and not result[0]:
            no_ec_found.append((w, info, result))

    if no_ec_found:
        print(f"  *** NO-EC CYCLES FOUND: {len(no_ec_found)} ***")
        for w, info, result in no_ec_found[:5]:
            print(f"    CL={len(w)}, disp={info['disp']}, branch={info['branch']}, "
                  f"no_ec_combos={result[1]}/{result[2]}")
    else:
        print(f"  All cycles have EC for all state combos")


# ============================================================
# SPECIFIC: CLB bounce cycle at n=9
# ============================================================
print("\n" + "=" * 72)
print("SPECIFIC: CLB bounce cycle structure")
print("=" * 72)

# The CLB construction for ms=(2,3,3,3,3,3,3,3,2) at n=9
# Bounce cycle: 0,1,2,...,8,7,6,...,1,0,1,2,...
# Actually let's construct it properly
ms_clb = [2,3,3,3,3,3,3,3,2]
bp_clb = get_binary_positions(ms_clb)
print(f"CLB ms={ms_clb}, binary at {bp_clb}")
print(f"Note: binary are CONSECUTIVE (adjacent at 0,8) - this is Case 3a, not Case 3b")

# The actual all-odd-gap bounce
# ms=[2,3,3,2,3,3,2,3,3], binary at 0,3,6
# A bounce-type cycle: goes up and down
# CL = sum of fire counts = 3*2 + 6*3 = 6+18 = 24
# Let's enumerate and find the longest/most interesting cycles

print(f"\nLooking at CL=24 cycles for ms=[2,3,3,2,3,3,2,3,3]...")
ms_focus = [2,3,3,2,3,3,2,3,3]

cl24_words = [w for w in valid_words if len(w) == 24]
print(f"CL=24 cycles: {len(cl24_words)}")

# Show a few with their properties
for w in cl24_words[:10]:
    info = classify_cycle(w, ms_focus, n)
    fc = Counter(w)
    result = check_all_state_combos_ec(w, ms_focus, n)
    ec_str = "ALL EC" if (result[0] is not None and result[0]) else f"{result[1]} no-EC/{result[2]}" if result[0] is not None else "?"

    print(f"  CL=24 disp={info['disp']:+3d} cw={info['cw']} "
          f"safe={info['safe']}({info['safe_proc']}) "
          f"EC={ec_str} branch={info['branch']}")

print("\n" + "=" * 72)
print("SUMMARY")
print("=" * 72)
