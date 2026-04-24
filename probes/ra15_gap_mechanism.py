#!/usr/bin/env python3
"""
RA15: Gap case mechanism for CL≤2n proof.

Gap case: ALL boundary ternary procs have fc_bin >= fc_ter for every
adjacent binary proc. Previous RA found 100% EC at n=7.

Questions:
1. Enumerate gap-case ZW cycles at n=5,7,9
2. Where is EC? At which proc?
3. What mechanism? Binary pigeonhole? Interior ternary gradient?
4. Universal argument?

Key insight to test: binary proc with fc >= 4 has tiny context space
(at most 18 = 2*3*3 mover contexts). With 4+ mover appearances and
many non-mover appearances, pigeonhole might force EC at the binary proc.
"""
import sys, os, time
from itertools import product as iproduct
from collections import Counter, defaultdict

sys.stdout = os.fdopen(sys.stdout.fileno(), 'w', buffering=1)


def enumerate_mover_words(ms, n, max_length):
    """Enumerate all valid mover words (DFS, incrementing transitions)."""
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


def get_contexts(word, ms, n):
    """
    For each step in the mover word, compute the full context (L, S, R)
    BEFORE the move, and whether proc is mover or non-mover.

    Returns: dict mapping proc -> list of (L, S, R, is_mover) tuples
    """
    config = [0] * n
    proc_contexts = defaultdict(list)

    for step_idx, mover in enumerate(word):
        # Record context for ALL procs
        for p in range(n):
            L = config[(p-1) % n]
            S = config[p]
            R = config[(p+1) % n]
            is_mover = (p == mover)
            proc_contexts[p].append((L, S, R, is_mover))

        # Apply move (incrementing)
        config[mover] = (config[mover] + 1) % ms[mover]

    return proc_contexts


def find_entry_conflicts(word, ms, n):
    """
    Find all procs with entry conflict: same (L, S, R) appears as both
    mover and non-mover context.
    """
    contexts = get_contexts(word, ms, n)
    ec_procs = []

    for p in range(n):
        mover_ctxs = set()
        nonmover_ctxs = set()
        for (L, S, R, is_mover) in contexts[p]:
            if is_mover:
                mover_ctxs.add((L, S, R))
            else:
                nonmover_ctxs.add((L, S, R))
        overlap = mover_ctxs & nonmover_ctxs
        if overlap:
            ec_procs.append((p, overlap))

    return ec_procs


def is_gap_case(word, ms, n):
    """
    Check if word is in the gap case: for every boundary ternary proc t
    (has at least one binary neighbor), ALL adjacent binary procs b have
    fc_b >= fc_t.
    """
    fc = Counter(word)
    binary_pos = set(i for i in range(n) if ms[i] == 2)
    ternary_pos = set(i for i in range(n) if ms[i] == 3)

    # Must have some fc >= 3 to be interesting
    if not any(fc[p] >= 3 for p in range(n)):
        return False

    # Check: is there ANY ternary with a binary neighbor that has fc_bin < fc_ter?
    for t in ternary_pos:
        if fc[t] < 3:
            continue
        L = (t - 1) % n
        R = (t + 1) % n
        for nbr in [L, R]:
            if nbr in binary_pos and fc[nbr] < fc[t]:
                return False  # gradient exists -> not gap case

    return True


def classify_ec_mechanism(word, ms, n, ec_procs):
    """
    For each EC proc, classify the mechanism.
    """
    fc = Counter(word)
    binary_pos = set(i for i in range(n) if ms[i] == 2)
    ternary_pos = set(i for i in range(n) if ms[i] == 3)

    classifications = []
    for p, overlap in ec_procs:
        if p in binary_pos:
            classifications.append(('binary_ec', p, fc[p], len(overlap)))
        elif p in ternary_pos:
            # Check if this ternary has a ternary neighbor with lower fc
            L = (p - 1) % n
            R = (p + 1) % n
            has_ter_gradient = False
            for nbr in [L, R]:
                if nbr in ternary_pos and fc[nbr] < fc[p]:
                    has_ter_gradient = True
            if has_ter_gradient:
                classifications.append(('ternary_gradient', p, fc[p], len(overlap)))
            else:
                classifications.append(('ternary_other', p, fc[p], len(overlap)))
        else:
            classifications.append(('other', p, fc[p], len(overlap)))

    return classifications


def analyze_binary_pigeonhole(word, ms, n):
    """
    For each binary proc with fc >= 4:
    Count distinct mover contexts vs non-mover contexts.
    Check if pigeonhole forces overlap.
    """
    fc = Counter(word)
    contexts = get_contexts(word, ms, n)
    binary_pos = [i for i in range(n) if ms[i] == 2]

    results = []
    for b in binary_pos:
        if fc[b] < 4:
            continue
        mover_ctxs = set()
        nonmover_ctxs = set()
        mover_count = 0
        nonmover_count = 0
        for (L, S, R, is_mover) in contexts[b]:
            if is_mover:
                mover_ctxs.add((L, S, R))
                mover_count += 1
            else:
                nonmover_ctxs.add((L, S, R))
                nonmover_count += 1

        # Context space size for binary proc b
        m_L = ms[(b-1) % n]
        m_R = ms[(b+1) % n]
        ctx_space = 2 * m_L * m_R  # (L, S, R) with S in {0,1}

        overlap = mover_ctxs & nonmover_ctxs

        results.append({
            'proc': b,
            'fc': fc[b],
            'mover_distinct': len(mover_ctxs),
            'nonmover_distinct': len(nonmover_ctxs),
            'mover_count': mover_count,
            'nonmover_count': nonmover_count,
            'ctx_space': ctx_space,
            'overlap': len(overlap),
        })

    return results


# ============================================================
# MAIN ANALYSIS
# ============================================================

print("=" * 70)
print("RA15: GAP CASE MECHANISM ANALYSIS")
print("=" * 70)

# Test layouts for n=5 and n=7
# For sub-threshold product with >=3 binary
test_cases = []

for n in [5, 7]:
    # Generate representative multisets with >=3 binary
    if n == 5:
        layouts = [
            [2, 2, 2, 3, 3],
            [2, 3, 2, 3, 2],
            [2, 2, 3, 2, 3],
        ]
    elif n == 7:
        layouts = [
            [2, 2, 2, 3, 3, 3, 3],
            [2, 3, 2, 3, 2, 3, 3],
            [2, 2, 2, 2, 3, 3, 3],
            [3, 2, 3, 2, 3, 2, 3],
        ]
    for ms in layouts:
        test_cases.append((ms, n))

for ms, n in test_cases:
    binary_pos = [i for i in range(n) if ms[i] == 2]
    ternary_pos = [i for i in range(n) if ms[i] == 3]
    product = 1
    for m in ms:
        product *= m

    # Max CL for ZW: 2n + excess
    max_cl = 2 * n + 6  # generous bound

    t0 = time.time()
    words = enumerate_mover_words(ms, n, max_cl)
    t1 = time.time()

    # Filter to fc > 2n (ZW = zigzag-winding, CL > 2n)
    zw_words = [w for w in words if len(w) > 2*n]

    # Filter to gap case
    gap_words = [w for w in zw_words if is_gap_case(w, ms, n)]

    print(f"\nms={ms}, n={n}, product={product}")
    print(f"  Total words: {len(words)} ({t1-t0:.1f}s)")
    print(f"  ZW words (CL > 2n={2*n}): {len(zw_words)}")
    print(f"  Gap case: {len(gap_words)} ({100*len(gap_words)/max(1,len(zw_words)):.1f}% of ZW)")

    if not gap_words:
        print(f"  No gap cases found.")
        continue

    # Analyze EC in gap cases
    ec_found = 0
    ec_at_binary = 0
    ec_at_ternary_gradient = 0
    ec_at_ternary_other = 0

    mechanism_counts = Counter()
    binary_fc_dist = Counter()
    ec_proc_types = Counter()

    # Detailed: binary pigeonhole analysis
    binary_ph_stats = []

    for w in gap_words:
        ec_procs = find_entry_conflicts(w, ms, n)
        if ec_procs:
            ec_found += 1
        else:
            print(f"  *** NO EC: word={w}")
            continue

        classifications = classify_ec_mechanism(w, ms, n, ec_procs)
        for mech, p, fc_val, noverlap in classifications:
            mechanism_counts[mech] += 1
            ec_proc_types[(mech, ms[p])] += 1

        # Check which proc has EC first (smallest index)
        first_ec_type = classifications[0][0] if classifications else 'none'

        # Binary pigeonhole stats
        bp = analyze_binary_pigeonhole(w, ms, n)
        for info in bp:
            binary_ph_stats.append(info)
            binary_fc_dist[info['fc']] += 1

    print(f"  EC found: {ec_found}/{len(gap_words)} ({100*ec_found/len(gap_words):.1f}%)")
    print(f"  EC mechanism counts:")
    for mech, cnt in sorted(mechanism_counts.items()):
        print(f"    {mech}: {cnt}")

    # Binary proc analysis
    if binary_ph_stats:
        print(f"\n  Binary proc pigeonhole analysis (fc >= 4):")
        print(f"    Total binary procs with fc>=4: {len(binary_ph_stats)}")
        print(f"    fc distribution: {dict(binary_fc_dist)}")

        # Aggregate stats
        overlap_count = sum(1 for s in binary_ph_stats if s['overlap'] > 0)
        print(f"    Procs with EC (mover/nonmover overlap): {overlap_count}/{len(binary_ph_stats)}")

        # Show summary of context usage
        for fc_val in sorted(binary_fc_dist.keys()):
            subset = [s for s in binary_ph_stats if s['fc'] == fc_val]
            avg_mover = sum(s['mover_distinct'] for s in subset) / len(subset)
            avg_nonmover = sum(s['nonmover_distinct'] for s in subset) / len(subset)
            avg_space = sum(s['ctx_space'] for s in subset) / len(subset)
            pct_overlap = 100 * sum(1 for s in subset if s['overlap'] > 0) / len(subset)
            print(f"    fc={fc_val}: avg mover_distinct={avg_mover:.1f}, nonmover_distinct={avg_nonmover:.1f}, ctx_space={avg_space:.0f}, overlap%={pct_overlap:.1f}")

    # Show a few examples
    if gap_words:
        print(f"\n  Example gap words (first 3):")
        for w in gap_words[:3]:
            fc = Counter(w)
            fc_str = {p: fc[p] for p in range(n)}
            ec_procs = find_entry_conflicts(w, ms, n)
            ec_info = [(p, ms[p], len(ov)) for p, ov in ec_procs]
            print(f"    word_len={len(w)}, fc={fc_str}")
            print(f"      EC procs: {ec_info}")

            # Show binary proc details
            for p, ov in ec_procs:
                if ms[p] == 2:
                    print(f"      Binary p={p}: EC overlaps = {ov}")


# ============================================================
# DEEPER ANALYSIS: Is binary EC universal in gap case?
# ============================================================
print("\n" + "=" * 70)
print("DEEPER: Is EC always at a BINARY proc in gap case?")
print("=" * 70)

for ms, n in test_cases:
    binary_pos = set(i for i in range(n) if ms[i] == 2)

    max_cl = 2 * n + 6
    words = enumerate_mover_words(ms, n, max_cl)
    gap_words = [w for w in words if len(w) > 2*n and is_gap_case(w, ms, n)]

    if not gap_words:
        continue

    always_binary_ec = 0
    no_binary_ec = 0
    both_ec = 0

    for w in gap_words:
        ec_procs = find_entry_conflicts(w, ms, n)
        ec_at_bin = any(p in binary_pos for p, _ in ec_procs)
        ec_at_ter = any(p not in binary_pos for p, _ in ec_procs)

        if ec_at_bin and ec_at_ter:
            both_ec += 1
        elif ec_at_bin:
            always_binary_ec += 1
        elif ec_at_ter:
            no_binary_ec += 1

    print(f"ms={ms}: gap={len(gap_words)}, binary_only_EC={always_binary_ec}, ternary_only_EC={no_binary_ec}, both={both_ec}")


# ============================================================
# CONTEXT SPACE ARGUMENT
# ============================================================
print("\n" + "=" * 70)
print("CONTEXT SPACE ARGUMENT FOR BINARY PROCS")
print("=" * 70)

print("""
For binary proc b with neighbors of size m_L, m_R:
  Context space: 2 * m_L * m_R values of (L, S, R)
  If both neighbors ternary: 2 * 3 * 3 = 18
  If one binary, one ternary: 2 * 2 * 3 = 12

In a cycle of length CL:
  Mover appearances at b: fc_b (each is a mover context)
  Non-mover appearances at b: CL - fc_b

For EC, need some (L,S,R) to appear as both mover and non-mover.
By pigeonhole: if fc_b + (CL - fc_b) > ctx_space,
  i.e., CL > ctx_space, then total appearances > space.
But that doesn't immediately give overlap between mover/nonmover sets.

Better argument:
  Mover contexts: fc_b values from a space of size ctx_space
  Non-mover contexts: CL - fc_b values from same space
  If |mover_distinct| + |nonmover_distinct| > ctx_space, then overlap exists.

For gap case: fc_b >= 4 (even, >= fc_ter >= 3).
Can we bound |mover_distinct| and |nonmover_distinct| tightly?
""")

# Empirical check: what fraction of context space do mover/nonmover use?
for ms, n in test_cases:
    binary_pos = [i for i in range(n) if ms[i] == 2]

    max_cl = 2 * n + 6
    words = enumerate_mover_words(ms, n, max_cl)
    gap_words = [w for w in words if len(w) > 2*n and is_gap_case(w, ms, n)]

    if not gap_words:
        continue

    print(f"\nms={ms}:")
    for w in gap_words[:5]:
        fc = Counter(w)
        cl = len(w)
        contexts = get_contexts(w, ms, n)

        for b in binary_pos:
            if fc[b] < 4:
                continue
            mover_ctxs = set()
            nonmover_ctxs = set()
            for (L, S, R, is_mover) in contexts[b]:
                if is_mover:
                    mover_ctxs.add((L, S, R))
                else:
                    nonmover_ctxs.add((L, S, R))

            m_L = ms[(b-1) % n]
            m_R = ms[(b+1) % n]
            space = 2 * m_L * m_R
            overlap = mover_ctxs & nonmover_ctxs

            print(f"  b={b}, fc={fc[b]}, CL={cl}, |M|={len(mover_ctxs)}, |NM|={len(nonmover_ctxs)}, space={space}, |M|+|NM|={len(mover_ctxs)+len(nonmover_ctxs)}, overlap={len(overlap)}")


# ============================================================
# REFINED: Check if walk structure constrains contexts
# ============================================================
print("\n" + "=" * 70)
print("WALK STRUCTURE CONSTRAINTS ON BINARY CONTEXTS")
print("=" * 70)

print("""
When binary proc b fires, it toggles: 0->1->0->...
So mover contexts alternate between S=0 and S=1.
With fc_b fires: fc_b/2 with S=0, fc_b/2 with S=1.

Non-mover contexts: b doesn't change, but neighbors do.
Between consecutive fires of b, the non-mover value of S stays fixed
(alternating 0,1,0,1... at each fire boundary).

Key: the MOVER contexts at b have both S=0 and S=1 (fc/2 each).
The NON-MOVER contexts at b also span both S=0 and S=1.

For S=0: mover contexts (L,0,R) and non-mover contexts (L,0,R).
If any (L,R) pair appears in both -> EC.

Mover: fc_b/2 contexts with S=0, from space of size m_L * m_R.
Non-mover: many contexts with S=0.

How many distinct (L,R) for mover with S=0?
  At most min(fc_b/2, m_L*m_R). With fc_b=4: 2 mover (L,R) pairs for S=0.

How many distinct (L,R) for non-mover with S=0?
  In CL - fc_b steps where b doesn't fire, roughly half have S=0.
  So ~(CL - fc_b)/2 non-mover appearances with S=0.

Union bound: |M_s0| + |NM_s0| > m_L*m_R implies overlap in S=0 slice.
""")

# Check empirically how this S-split looks
for ms, n in test_cases[:3]:  # first 3 cases
    binary_pos = [i for i in range(n) if ms[i] == 2]

    max_cl = 2 * n + 6
    words = enumerate_mover_words(ms, n, max_cl)
    gap_words = [w for w in words if len(w) > 2*n and is_gap_case(w, ms, n)]

    if not gap_words:
        continue

    print(f"\nms={ms}:")

    s0_overlap_count = 0
    s1_overlap_count = 0
    total_checks = 0

    for w in gap_words:
        fc = Counter(w)
        contexts = get_contexts(w, ms, n)

        for b in binary_pos:
            if fc[b] < 4:
                continue
            total_checks += 1

            # Split by S value
            for s_val in [0, 1]:
                mover_lr = set()
                nonmover_lr = set()
                for (L, S, R, is_mover) in contexts[b]:
                    if S == s_val:
                        if is_mover:
                            mover_lr.add((L, R))
                        else:
                            nonmover_lr.add((L, R))

                overlap_lr = mover_lr & nonmover_lr
                if overlap_lr:
                    if s_val == 0:
                        s0_overlap_count += 1
                    else:
                        s1_overlap_count += 1

    if total_checks > 0:
        print(f"  total binary(fc>=4) checks: {total_checks}")
        print(f"  S=0 overlap: {s0_overlap_count} ({100*s0_overlap_count/total_checks:.1f}%)")
        print(f"  S=1 overlap: {s1_overlap_count} ({100*s1_overlap_count/total_checks:.1f}%)")
        print(f"  Either S: {s0_overlap_count + s1_overlap_count - total_checks}")  # rough
        # Better: any overlap
        any_overlap = 0
        for w in gap_words:
            fc = Counter(w)
            contexts = get_contexts(w, ms, n)
            for b in binary_pos:
                if fc[b] < 4:
                    continue
                has = False
                for s_val in [0, 1]:
                    mover_lr = set()
                    nonmover_lr = set()
                    for (L, S, R, is_mover) in contexts[b]:
                        if S == s_val:
                            if is_mover:
                                mover_lr.add((L, R))
                            else:
                                nonmover_lr.add((L, R))
                    if mover_lr & nonmover_lr:
                        has = True
                if has:
                    any_overlap += 1
        print(f"  Any S overlap: {any_overlap}/{total_checks} ({100*any_overlap/total_checks:.1f}%)")


# ============================================================
# CYCLE LENGTH CONSTRAINT
# ============================================================
print("\n" + "=" * 70)
print("CYCLE LENGTH vs BINARY FC IN GAP CASE")
print("=" * 70)

for ms, n in test_cases:
    binary_pos = [i for i in range(n) if ms[i] == 2]
    ternary_pos = [i for i in range(n) if ms[i] == 3]

    max_cl = 2 * n + 6
    words = enumerate_mover_words(ms, n, max_cl)
    gap_words = [w for w in words if len(w) > 2*n and is_gap_case(w, ms, n)]

    if not gap_words:
        continue

    print(f"\nms={ms}, n={n}:")
    for w in gap_words[:8]:
        fc = Counter(w)
        cl = len(w)
        fc_str = " ".join(f"P{p}({'B' if ms[p]==2 else 'T'})={fc[p]}" for p in range(n))

        # Sum of fc = CL
        total_fc = sum(fc[p] for p in range(n))
        min_fc = sum(ms)  # minimum total (each proc fires exactly ms[p])
        excess = cl - min_fc

        # Count binary fc total
        bin_total = sum(fc[b] for b in binary_pos)
        ter_total = sum(fc[t] for t in ternary_pos)

        print(f"  CL={cl} (2n={2*n}, excess={cl-2*n}): {fc_str}")
        print(f"    bin_total={bin_total}, ter_total={ter_total}, min={min_fc}")


print("\n" + "=" * 70)
print("DONE")
print("=" * 70)
