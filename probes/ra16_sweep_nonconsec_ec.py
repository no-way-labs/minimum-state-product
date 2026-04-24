#!/usr/bin/env python3
"""
RA16: Universal EC investigation for sweep cycles with non-consecutive binary.

SETUP:
  - n processors on a ring, m_i in {2,3}
  - >=3 binary procs, NO 3 consecutive binary
  - Product < 4*3^(n-2) (sub-threshold)
  - Good cycle is a sweep: |displacement| >= 2n

QUESTION: Does EVERY such cycle have an entry conflict (EC)?
If so, what mechanism produces it?

EC definition: exists proc j and context triple (L,S,R) that appears
both when j is the mover AND when j is a non-mover. This forces
f_j(L,S,R) = S' != S (mover) and f_j(L,S,R) = S (non-mover) — contradiction.
"""
from itertools import combinations, product as iproduct
from collections import Counter, defaultdict
import time


def total_displacement(word, n):
    """Compute total displacement of mover word on ring of size n."""
    disp = 0
    L = len(word)
    for i in range(L):
        nxt = word[(i + 1) % L]
        cur = word[i]
        diff = (nxt - cur) % n
        if diff == 1:
            disp += 1
        elif diff == n - 1:
            disp -= 1
        else:
            return None  # non-adjacent step
    return disp


def has_3_consecutive_binary(ms):
    """Check if ms has 3 consecutive binary procs (on ring)."""
    n = len(ms)
    for i in range(n):
        if ms[i] == 2 and ms[(i+1)%n] == 2 and ms[(i+2)%n] == 2:
            return True
    return False


def enumerate_words_dfs(n, ms, max_len, max_results=50000, timeout=120):
    """Enumerate all valid mover words (cyclic, adjacent, each proc fires m_i times)."""
    target_cl = sum(ms)
    results = []
    t0 = time.time()
    ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}

    def dfs(word, fc):
        if time.time() - t0 > timeout:
            return
        if len(results) >= max_results:
            return
        if len(word) == target_cl:
            if all(fc[p] == ms[p] for p in range(n)):
                # Check cyclic adjacency
                diff = (word[0] - word[-1]) % n
                if diff in (1, n-1):
                    results.append(tuple(word))
            return
        remaining = target_cl - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n))
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            if fc[nxt] < ms[nxt]:
                fc[nxt] += 1
                word.append(nxt)
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1

    for start in range(n):
        if time.time() - t0 > timeout or len(results) >= max_results:
            break
        fc = [0]*n
        fc[start] = 1
        if fc[start] <= ms[start]:
            dfs([start], fc)

    return results


def canonicalize(word):
    """Canonical form of cyclic word (min rotation)."""
    L = len(word)
    best = word
    for i in range(L):
        rot = word[i:] + word[:i]
        if rot < best:
            best = rot
    return best


def build_configs_all_trans(word, ms, n):
    """Build good cycle configs for ALL transition combos (inc/dec at ternary).
    Returns list of (trans_dir, configs) pairs."""
    L = len(word)
    wl = list(word)
    bins = {p for p in range(n) if ms[p] == 2}
    ternary = [p for p in range(n) if ms[p] == 3]
    n_tern = len(ternary)

    results = []
    for trans_bits in range(1 << n_tern):
        trans_dir = {}
        for p in bins:
            trans_dir[p] = 1
        for idx, p in enumerate(ternary):
            trans_dir[p] = 1 if not ((trans_bits >> idx) & 1) else -1

        configs = [[0]*n]
        for t in range(L):
            c = list(configs[-1])
            p = wl[t]
            c[p] = (c[p] + trans_dir[p]) % ms[p]
            configs.append(c)

        if configs[-1] != configs[0]:
            continue
        config_set = set(tuple(c) for c in configs[:L])
        if len(config_set) != L:
            continue

        results.append((trans_dir.copy(), [tuple(c) for c in configs[:L]]))
    return results


def find_ec_at_proc(word, configs, n, j):
    """Check entry conflict at proc j. Returns set of conflicting triples."""
    L = len(word)
    mt = set()   # triples when j is mover
    nmt = set()  # triples when j is non-mover
    for t in range(L):
        c = configs[t]
        triple = (c[(j-1)%n], c[j], c[(j+1)%n])
        if word[t] == j:
            mt.add(triple)
        else:
            nmt.add(triple)
    return mt & nmt


def find_all_ec(word, configs, ms, n):
    """Find all procs with entry conflict. Returns dict proc -> overlap triples."""
    result = {}
    for j in range(n):
        overlap = find_ec_at_proc(word, configs, n, j)
        if overlap:
            result[j] = overlap
    return result


def classify_ec_proc(j, ms, n):
    """Classify proc j: binary, sandwiched ternary (between 2 binary), or other ternary."""
    if ms[j] == 2:
        return "binary"
    # ternary
    lm = ms[(j-1)%n]
    rm = ms[(j+1)%n]
    if lm == 2 and rm == 2:
        return "sandwiched-ternary"
    elif lm == 2 or rm == 2:
        return "semi-sandwiched-ternary"
    else:
        return "interior-ternary"


def analyze_ec_mechanism(word, configs, ms, n, j, overlap):
    """Analyze WHY the EC happens at proc j."""
    L = len(word)
    fc = Counter(word)

    # Gather mover and non-mover steps for proc j
    mover_steps = [t for t in range(L) if word[t] == j]
    nonmover_steps = [t for t in range(L) if word[t] != j]

    # For each conflicting triple, find the mover and non-mover steps
    details = []
    for triple in overlap:
        m_at = [t for t in mover_steps if configs[t] == tuple(
            triple[k] for k in [((j-1)%n - (j-1)%n + (j-1)%n) % 1, 0, 0])  # wrong approach
        ]
        # Simpler: just find steps
        m_steps = []
        nm_steps = []
        for t in range(L):
            c = configs[t]
            tr = (c[(j-1)%n], c[j], c[(j+1)%n])
            if tr == triple:
                if word[t] == j:
                    m_steps.append(t)
                else:
                    nm_steps.append(t)
        details.append((triple, m_steps, nm_steps))

    # Classify: what's the non-mover doing when the conflict occurs?
    # Key question: is the non-mover step a neighbor of j?
    nm_movers_at_conflict = set()
    for triple, m_steps, nm_steps in details:
        for t in nm_steps:
            nm_movers_at_conflict.add(word[t])

    # Check if conflict involves neighbor firings
    neighbors = {(j-1)%n, (j+1)%n}
    involves_neighbor = bool(nm_movers_at_conflict & neighbors)

    # Check if it's a "phase extraction" type (ternary j, binary neighbor fires
    # create same context at both mover and non-mover steps)
    is_phase_extraction = (ms[j] == 3 and involves_neighbor and
                           bool(nm_movers_at_conflict & {p for p in neighbors if ms[p] == 2}))

    return {
        'triple_details': details,
        'nm_movers': nm_movers_at_conflict,
        'involves_neighbor': involves_neighbor,
        'is_phase_extraction': is_phase_extraction,
        'proc_type': classify_ec_proc(j, ms, n),
        'fc_j': fc[j],
    }


def run_investigation(n_val, timeout_per_ms=60):
    """Run full investigation for a given n."""
    n = n_val
    threshold = 4 * (3 ** (n - 2))

    print(f"\n{'='*70}")
    print(f"n = {n}, threshold = {threshold}")
    print(f"{'='*70}")

    # Enumerate all sub-threshold multisets with >=3 binary, no 3 consecutive
    bin_counts = range(3, n+1)  # 3 to n binary procs
    all_cases = []

    for nb in bin_counts:
        nt = n - nb
        prod = (2**nb) * (3**nt)
        if prod >= threshold:
            continue
        # Need to place nb binary procs so no 3 consecutive
        for bin_combo in combinations(range(n), nb):
            bins_set = set(bin_combo)
            ms = [2 if p in bins_set else 3 for p in range(n)]
            if has_3_consecutive_binary(ms):
                continue
            # Check product
            product = 1
            for m in ms:
                product *= m
            if product >= threshold:
                continue
            # Canonicalize by rotation
            ms_rotations = []
            for r in range(n):
                ms_rotations.append(tuple(ms[(r+i)%n] for i in range(n)))
            canon_ms = min(ms_rotations)
            all_cases.append((canon_ms, bins_set, ms))

    # Deduplicate
    seen = set()
    unique_cases = []
    for canon_ms, bins_set, ms in all_cases:
        if canon_ms not in seen:
            seen.add(canon_ms)
            unique_cases.append((canon_ms, ms))

    print(f"Sub-threshold multisets with >=3 binary, no 3 consecutive: {len(unique_cases)}")
    for canon_ms, ms in unique_cases:
        nb = sum(1 for m in ms if m == 2)
        product = 1
        for m in ms:
            product *= m
        print(f"  ms={list(ms)}, #binary={nb}, product={product}")

    # For each case, enumerate sweep words and check EC
    total_sweep_cycles = 0
    total_ec_cycles = 0
    total_no_ec = 0
    no_ec_examples = []
    ec_proc_type_counts = Counter()
    ec_mechanism_counts = Counter()

    for canon_ms, ms in unique_cases:
        bins_set = {p for p in range(n) if ms[p] == 2}
        nb = len(bins_set)
        product = 1
        for m in ms:
            product *= m

        print(f"\n--- ms={list(ms)}, product={product} ---")

        # Enumerate mover words
        max_len = sum(ms)
        words = enumerate_words_dfs(n, ms, max_len, max_results=50000, timeout=timeout_per_ms)

        # Deduplicate by canonical rotation
        unique_words = {}
        for w in words:
            c = canonicalize(w)
            if c not in unique_words:
                unique_words[c] = w

        # Filter for sweeps
        sweep_words = []
        for w in unique_words.values():
            d = total_displacement(list(w), n)
            if d is not None and abs(d) >= 2*n:
                sweep_words.append(w)

        print(f"  Total unique words: {len(unique_words)}, sweep words: {len(sweep_words)}")

        if not sweep_words:
            print(f"  No sweep words found")
            continue

        # For each sweep word, try all transition combos
        for w in sweep_words:
            valid_cycles = build_configs_all_trans(w, ms, n)
            if not valid_cycles:
                continue

            for trans_dir, configs in valid_cycles:
                total_sweep_cycles += 1
                ec_map = find_all_ec(w, configs, ms, n)

                if ec_map:
                    total_ec_cycles += 1
                    # Classify which proc types have EC
                    for j in ec_map:
                        ptype = classify_ec_proc(j, ms, n)
                        ec_proc_type_counts[ptype] += 1

                    # Analyze the FIRST EC found for mechanism classification
                    first_j = min(ec_map.keys())
                    analysis = analyze_ec_mechanism(w, configs, ms, n, first_j, ec_map[first_j])
                    if analysis['is_phase_extraction']:
                        ec_mechanism_counts['phase-extraction'] += 1
                    elif analysis['involves_neighbor']:
                        ec_mechanism_counts['neighbor-context'] += 1
                    else:
                        ec_mechanism_counts['far-context'] += 1
                else:
                    total_no_ec += 1
                    no_ec_examples.append({
                        'ms': list(ms),
                        'word': list(w),
                        'trans_dir': trans_dir,
                        'configs': configs[:6],  # first 6 configs for display
                    })

        print(f"  Sweep cycles checked: {sum(1 for w2 in sweep_words for _ in build_configs_all_trans(w2, ms, n))}")

    print(f"\n{'='*70}")
    print(f"SUMMARY for n={n}")
    print(f"{'='*70}")
    print(f"Total sweep cycles (all multisets, all trans combos): {total_sweep_cycles}")
    print(f"  With EC: {total_ec_cycles} ({100*total_ec_cycles/max(1,total_sweep_cycles):.1f}%)")
    print(f"  Without EC: {total_no_ec}")
    if total_sweep_cycles > 0 and total_no_ec == 0:
        print(f"  *** UNIVERSAL EC: Every sweep cycle has entry conflict ***")

    print(f"\nEC proc type breakdown (which proc types provide EC):")
    for ptype, cnt in ec_proc_type_counts.most_common():
        print(f"  {ptype}: {cnt}")

    print(f"\nEC mechanism breakdown:")
    for mech, cnt in ec_mechanism_counts.most_common():
        print(f"  {mech}: {cnt}")

    if no_ec_examples:
        print(f"\nNO-EC EXAMPLES (first 3):")
        for ex in no_ec_examples[:3]:
            print(f"  ms={ex['ms']}")
            print(f"  word={ex['word']}")
            print(f"  trans={ex['trans_dir']}")

    return total_sweep_cycles, total_ec_cycles, total_no_ec, no_ec_examples


def deep_ec_analysis(n_val, timeout_per_ms=60):
    """Deeper analysis: for each EC, classify exact mechanism precisely."""
    n = n_val
    threshold = 4 * (3 ** (n - 2))

    print(f"\n{'='*70}")
    print(f"DEEP EC ANALYSIS: n = {n}")
    print(f"{'='*70}")

    # Same setup as above but with detailed per-proc analysis
    bin_counts = range(3, n+1)
    all_cases = []
    seen = set()

    for nb in bin_counts:
        nt = n - nb
        prod = (2**nb) * (3**nt)
        if prod >= threshold:
            continue
        for bin_combo in combinations(range(n), nb):
            bins_set = set(bin_combo)
            ms = [2 if p in bins_set else 3 for p in range(n)]
            if has_3_consecutive_binary(ms):
                continue
            product = 1
            for m in ms:
                product *= m
            if product >= threshold:
                continue
            ms_rotations = []
            for r in range(n):
                ms_rotations.append(tuple(ms[(r+i)%n] for i in range(n)))
            canon_ms = min(ms_rotations)
            if canon_ms not in seen:
                seen.add(canon_ms)
                all_cases.append((canon_ms, ms))

    # For each sweep cycle, do detailed per-proc EC analysis
    # Focus: which PROC has EC, what does the conflicting triple look like
    mechanism_details = defaultdict(int)

    for canon_ms, ms in all_cases:
        max_len = sum(ms)
        words = enumerate_words_dfs(n, ms, max_len, max_results=50000, timeout=timeout_per_ms)
        unique_words = {}
        for w in words:
            c = canonicalize(w)
            if c not in unique_words:
                unique_words[c] = w

        sweep_words = [w for w in unique_words.values()
                       if total_displacement(list(w), n) is not None
                       and abs(total_displacement(list(w), n)) >= 2*n]

        for w in sweep_words:
            for trans_dir, configs in build_configs_all_trans(w, ms, n):
                L = len(w)
                fc = Counter(w)

                # Check EC at each proc
                for j in range(n):
                    overlap = find_ec_at_proc(w, configs, n, j)
                    if not overlap:
                        continue

                    ptype = classify_ec_proc(j, ms, n)
                    # Detailed mechanism:
                    # For each overlapping triple, find which steps
                    for triple in overlap:
                        m_steps = []
                        nm_steps = []
                        for t in range(L):
                            c = configs[t]
                            tr = (c[(j-1)%n], c[j], c[(j+1)%n])
                            if tr == triple:
                                if w[t] == j:
                                    m_steps.append(t)
                                else:
                                    nm_steps.append(t)

                        # What fires at non-mover step?
                        nm_firers = set(w[t] for t in nm_steps)
                        neighbors = {(j-1)%n, (j+1)%n}
                        binary_neighbors = {p for p in neighbors if ms[p] == 2}
                        ternary_neighbors = {p for p in neighbors if ms[p] == 3}

                        if nm_firers & binary_neighbors:
                            mechanism_details[f'{ptype}:binary-neighbor-fires'] += 1
                        elif nm_firers & ternary_neighbors:
                            mechanism_details[f'{ptype}:ternary-neighbor-fires'] += 1
                        elif nm_firers - neighbors:
                            mechanism_details[f'{ptype}:far-proc-fires'] += 1
                        break  # one triple per proc suffices
                    break  # one proc per cycle suffices for classification

    print(f"\nDetailed mechanism breakdown:")
    for mech, cnt in sorted(mechanism_details.items(), key=lambda x: -x[1]):
        print(f"  {mech}: {cnt}")


def investigate_isolated_binary(n_val, timeout_per_ms=60):
    """Check the isolated binary parity argument."""
    n = n_val
    threshold = 4 * (3 ** (n - 2))

    print(f"\n{'='*70}")
    print(f"ISOLATED BINARY PARITY ANALYSIS: n = {n}")
    print(f"{'='*70}")

    seen = set()
    all_cases = []
    for nb in range(3, n+1):
        nt = n - nb
        prod = (2**nb) * (3**nt)
        if prod >= threshold:
            continue
        for bin_combo in combinations(range(n), nb):
            bins_set = set(bin_combo)
            ms = [2 if p in bins_set else 3 for p in range(n)]
            if has_3_consecutive_binary(ms):
                continue
            product = 1
            for m in ms:
                product *= m
            if product >= threshold:
                continue
            ms_rotations = [tuple(ms[(r+i)%n] for i in range(n)) for r in range(n)]
            canon_ms = min(ms_rotations)
            if canon_ms not in seen:
                seen.add(canon_ms)
                all_cases.append((canon_ms, ms))

    for canon_ms, ms in all_cases:
        max_len = sum(ms)
        words = enumerate_words_dfs(n, ms, max_len, max_results=50000, timeout=timeout_per_ms)
        unique_words = {}
        for w in words:
            c = canonicalize(w)
            if c not in unique_words:
                unique_words[c] = w

        sweep_words = [w for w in unique_words.values()
                       if total_displacement(list(w), n) is not None
                       and abs(total_displacement(list(w), n)) >= 2*n]

        if not sweep_words:
            continue

        print(f"\nms={list(ms)}")

        for w in sweep_words[:5]:  # first 5 sweep words
            for trans_dir, configs in build_configs_all_trans(w, ms, n):
                L = len(w)
                bins_set = {p for p in range(n) if ms[p] == 2}

                # For each binary proc, check firing isolation
                for b in sorted(bins_set):
                    b_steps = [t for t in range(L) if w[t] == b]
                    fc_b = len(b_steps)
                    if fc_b != 2:
                        continue  # binary fires exactly 2 times in sweep

                    # Check isolation: no consecutive fires
                    isolated = True
                    for i in range(len(b_steps)):
                        nxt = b_steps[(i+1) % len(b_steps)]
                        gap = (nxt - b_steps[i]) % L
                        if gap == 1:
                            isolated = False
                            break

                    if not isolated:
                        continue

                    # At binary proc b: values are 0 and 1
                    # With fc=2, isolated: b fires at step s1 (0->1) and step s2 (1->0)
                    # Between fires: value is constant (1 or 0)
                    # Check: does the context (L,S,R) at mover steps overlap with non-mover?
                    overlap = find_ec_at_proc(w, configs, n, b)
                    ec_at_b = bool(overlap)

                    # Also check EC at b's ternary neighbors
                    b_neighbors = [(b-1)%n, (b+1)%n]
                    tern_neighbors = [p for p in b_neighbors if ms[p] == 3]
                    ec_at_tn = {}
                    for tn in tern_neighbors:
                        ov = find_ec_at_proc(w, configs, n, tn)
                        if ov:
                            ec_at_tn[tn] = ov

                    if ec_at_b or ec_at_tn:
                        print(f"  word={list(w)[:20]}..., binary={b}, fc={fc_b}, "
                              f"isolated={isolated}, EC@binary={ec_at_b}, "
                              f"EC@ternary_nbrs={list(ec_at_tn.keys())}")
                break  # one trans combo for this word


if __name__ == '__main__':
    # Run for n=5, 7 first (faster), then n=9
    for n_val in [5, 7]:
        total, ec, no_ec, examples = run_investigation(n_val, timeout_per_ms=30)

    print("\n" + "="*70)
    print("DEEP MECHANISM ANALYSIS")
    print("="*70)
    for n_val in [5, 7]:
        deep_ec_analysis(n_val, timeout_per_ms=30)

    # n=9 with longer timeout
    print("\n" + "#"*70)
    print("# N=9 INVESTIGATION")
    print("#"*70)
    total, ec, no_ec, examples = run_investigation(9, timeout_per_ms=90)
    if no_ec == 0:
        deep_ec_analysis(9, timeout_per_ms=90)
