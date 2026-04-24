#!/usr/bin/env python3
"""
RA12: Hamming-1 Uniqueness Investigation

For good cycles of self-stabilizing token rings:
  If g_j and g_k are Hamming distance 1, must j = k±1 (mod CL)?

Tests:
  Part 1: General good cycles (Sol3 n=5,7; Dijkstra Sol1 n=5)
  Part 2: Sweep cycles at n=9, ms=(2,3,3,2,3,3,2,3,3) sub-threshold
  Part 3: Analysis of WHY it holds (or counterexamples)
  Part 4: Pre-image uniqueness (stronger property)
  Part 5: Transition injectivity analysis
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict
from verifier import verify_system, privileged_set, apply_move


def hamming_distance(a, b):
    return sum(1 for x, y in zip(a, b) if x != y)


def hamming_diff_positions(a, b):
    return [i for i in range(len(a)) if a[i] != b[i]]


# ── System builders ──

def build_sol3(n):
    ms = [3] * n
    def f_bottom(L, S, R):
        if (S + 1) % 3 == R: return (S - 1) % 3
        return S
    def f_top(L, S, R):
        if L == R and (L + 1) % 3 != S: return (L + 1) % 3
        return S
    def f_middle(L, S, R):
        if (S + 1) % 3 == L: return L
        if (S + 1) % 3 == R: return R
        return S
    fs = [f_bottom] + [f_middle] * (n - 2) + [f_top]
    return ms, fs


def build_cup2(n):
    """CUP-2 system: ms = (2, 3, ..., 3, 2)"""
    ms = [2] + [3] * (n - 2) + [2]

    T_bot = {
        (0,0,0):1, (0,0,1):1, (0,0,2):0,
        (0,1,0):1, (0,1,1):1, (0,1,2):1,
        (1,0,0):0, (1,0,1):1, (1,0,2):0,
        (1,1,0):0, (1,1,1):1, (1,1,2):0,
    }
    T_low = {
        (0,0,0):0, (0,0,1):0, (0,0,2):0,
        (0,1,0):0, (0,1,1):1, (0,1,2):0,
        (0,2,0):0, (0,2,1):2, (0,2,2):0,
        (1,0,0):1, (1,0,1):1, (1,0,2):1,
        (1,1,0):1, (1,1,1):1, (1,1,2):2,
        (1,2,0):0, (1,2,1):1, (1,2,2):2,
    }
    T_mid = {
        (0,0,0):0, (0,0,1):0, (0,0,2):0,
        (0,1,0):0, (0,1,1):1, (0,1,2):0,
        (0,2,0):0, (0,2,1):2, (0,2,2):0,
        (1,0,0):1, (1,0,1):1, (1,0,2):1,
        (1,1,0):1, (1,1,1):1, (1,1,2):2,
        (1,2,0):0, (1,2,1):1, (1,2,2):2,
        (2,0,0):0, (2,0,1):0, (2,0,2):2,
        (2,1,0):1, (2,1,1):0, (2,1,2):2,
        (2,2,0):0, (2,2,1):2, (2,2,2):2,
    }
    T_high = {
        (0,0,0):0, (0,0,1):0,
        (0,1,0):0, (0,1,1):0,
        (0,2,0):0, (0,2,1):0,
        (1,0,0):1, (1,0,1):1,
        (1,1,0):1, (1,1,1):2,
        (1,2,0):0, (1,2,1):2,
        (2,0,0):0, (2,0,1):2,
        (2,1,0):0, (2,1,1):2,
        (2,2,0):2, (2,2,1):2,
    }
    T_top = {
        (0,0,0):0, (0,0,1):0,
        (0,1,0):0, (0,1,1):0,
        (1,0,0):0, (1,0,1):1,
        (1,1,0):1, (1,1,1):1,
        (2,0,0):1, (2,0,1):1,
        (2,1,0):1, (2,1,1):1,
    }

    def get_table(pos):
        if pos == 0: return T_bot
        if pos == 1: return T_low
        if pos == n - 2: return T_high
        if pos == n - 1: return T_top
        return T_mid

    fs = []
    for p in range(n):
        tbl = get_table(p)
        def make_f(t):
            return lambda L, S, R: t[(L, S, R)]
        fs.append(make_f(tbl))

    return ms, fs


def build_m5_witness():
    """M_5 = 96 witness: ms = (2,2,2,3,4)"""
    # From clb_witness or similar — let me build from the verifier
    # Actually, let me use the known construction
    ms = [2, 2, 2, 3, 4]
    # We need to verify and extract cycle — let me search
    return None, None  # placeholder


def extract_cycle(ms, fs):
    """Extract good cycle from a verified system."""
    result = verify_system(ms, fs)
    if not result['valid']:
        return None, None, None
    cycle = result['cycle']
    # Extract movers
    n = len(ms)
    movers = []
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        for p in range(n):
            if c[p] != c_next[p]:
                movers.append(p)
                break
    return cycle, movers, fs


def check_h1_uniqueness(cycle, label=""):
    """Check H-1 uniqueness for a good cycle."""
    CL = len(cycle)
    h1_pairs = []  # (j, k, pos) where j < k and Hamming dist = 1

    for j in range(CL):
        for k in range(j + 1, CL):
            hd = hamming_distance(cycle[j], cycle[k])
            if hd == 1:
                pos = hamming_diff_positions(cycle[j], cycle[k])[0]
                # Check if adjacent
                adj = (k == j + 1) or (j == 0 and k == CL - 1)
                h1_pairs.append((j, k, pos, adj))

    non_adj = [(j, k, p, a) for j, k, p, a in h1_pairs if not a]

    print(f"\n{'='*60}")
    print(f"{label}: cycle length = {CL}")
    print(f"  Total H-1 pairs: {len(h1_pairs)}")
    print(f"  Adjacent H-1 pairs: {len(h1_pairs) - len(non_adj)}")
    print(f"  NON-ADJACENT H-1 pairs: {len(non_adj)}")

    if non_adj:
        print(f"  *** H-1 UNIQUENESS FAILS ***")
        for j, k, p, _ in non_adj[:10]:
            gap = min(k - j, CL - k + j)
            print(f"    g[{j}] vs g[{k}] differ at pos {p}, gap={gap}")
            print(f"      g[{j}] = {cycle[j]}")
            print(f"      g[{k}] = {cycle[k]}")
        return False
    else:
        print(f"  H-1 uniqueness HOLDS")
        return True


def check_preimage_uniqueness(cycle, movers, fs, ms, label=""):
    """Check transition pre-image uniqueness.
    For each good config g_k and each position p:
    how many values v satisfy f_p(L, v, R) = g_k[p]
    where L = g_k[left(p)], R = g_k[right(p)]?
    """
    n = len(ms)
    CL = len(cycle)
    max_preimage = 0
    violations = []

    for k in range(CL):
        gk = cycle[k]
        for p in range(n):
            L = gk[(p - 1) % n]
            R = gk[(p + 1) % n]
            target = gk[p]
            # Count pre-images
            preimages = []
            for v in range(ms[p]):
                if fs[p](L, v, R) == target:
                    preimages.append(v)
            if len(preimages) > 1:
                max_preimage = max(max_preimage, len(preimages))
                violations.append((k, p, target, preimages, L, R))

    print(f"\n{'='*60}")
    print(f"{label} — Pre-image uniqueness check")
    print(f"  Violations (|pre-image| > 1): {len(violations)}")
    if violations:
        print(f"  Max pre-image size: {max_preimage}")
        for k, p, target, pre, L, R in violations[:10]:
            print(f"    g[{k}] pos {p}: f_p({L}, ?, {R}) = {target} has pre-images {pre}")
            # Check if mover at k-1 is p
            prev_mover = movers[(k - 1) % CL]
            print(f"      moverAt({(k-1)%CL}) = {prev_mover}, {'MATCH' if prev_mover == p else 'no match'}")
    else:
        print(f"  ALL pre-images unique → forcedSucc_nonGood follows trivially!")

    return len(violations) == 0


def check_h1_preimage(cycle, movers, fs, ms, label=""):
    """Combined check: for Hamming-1 non-good configs mapping to g_k,
    is the result always a good config?

    For each g_k, for each position p:
      For each v != g_k[p] with f_p(g_k[left], v, g_k[right]) = g_k[p]:
        c = g_k with position p changed to v
        Is c good? If so, which g_j is it?
    """
    n = len(ms)
    CL = len(cycle)
    good_set = set(cycle)
    cycle_index = {c: i for i, c in enumerate(cycle)}

    problematic = []  # Cases where a non-good H-1 config maps to g_k

    for k in range(CL):
        gk = cycle[k]
        for p in range(n):
            L = gk[(p - 1) % n]
            R = gk[(p + 1) % n]
            target = gk[p]

            for v in range(ms[p]):
                if v == gk[p]:
                    continue  # same config
                if fs[p](L, v, R) != target:
                    continue  # doesn't map to gk[p] — this c won't have move(c,p) = g_k

                # Actually wait — for move(sys, c, p) = g_k, we need:
                # c agrees with g_k at all positions except p, AND
                # f_p(c[left], c[p], c[right]) = g_k[p]
                # Since c agrees with g_k at left and right of p:
                # f_p(g_k[left], v, g_k[right]) = g_k[p] ✓

                # But also: p must be privileged in c, meaning f_p(L, v, R) != v
                # We know f_p(L, v, R) = target = g_k[p] != v (since v != gk[p])
                # So yes, p is privileged in c. ✓

                # Build c
                c = list(gk)
                c[p] = v
                c = tuple(c)

                if c in good_set:
                    j = cycle_index[c]
                    gap = min(abs(j - k), CL - abs(j - k))
                    if gap > 1:
                        problematic.append((k, p, v, j, gap, c))
                else:
                    problematic.append((k, p, v, None, None, c))

    print(f"\n{'='*60}")
    print(f"{label} — H-1 pre-image analysis")

    non_good_mapped = [(k, p, v, j, g, c) for k, p, v, j, g, c in problematic if j is None]
    distant_good = [(k, p, v, j, g, c) for k, p, v, j, g, c in problematic if j is not None]

    print(f"  Non-good H-1 configs mapping into good cycle: {len(non_good_mapped)}")
    print(f"  Distant (gap>1) good H-1 configs: {len(distant_good)}")

    if non_good_mapped:
        print(f"\n  *** CRITICAL: Non-good configs at H-1 distance map into cycle! ***")
        for k, p, v, _, _, c in non_good_mapped[:10]:
            priv = privileged_set(c, fs, ms)
            print(f"    c={c} (H-1 from g[{k}] at pos {p}, v={v})")
            print(f"      privileged procs: {priv} (count={len(priv)})")
            print(f"      g[{k}]={cycle[k]}")
    else:
        print(f"  GOOD: Every H-1 config that maps into cycle is itself good!")
        print(f"    → forcedSucc_nonGood holds for this system!")

    if distant_good:
        print(f"\n  Distant good H-1 pairs:")
        for k, p, v, j, g, c in distant_good[:10]:
            print(f"    g[{j}] is H-1 from g[{k}] at pos {p}, gap={g}")

    return len(non_good_mapped) == 0


# ── Part 1: General good cycles ──

print("=" * 70)
print("PART 1: H-1 Uniqueness for General Good Cycles")
print("=" * 70)

# Sol3 n=5
ms5, fs5 = build_sol3(5)
cycle5, movers5, _ = extract_cycle(ms5, fs5)
if cycle5:
    h1_ok_5 = check_h1_uniqueness(cycle5, "Sol3 n=5")
    check_preimage_uniqueness(cycle5, movers5, fs5, ms5, "Sol3 n=5")
    check_h1_preimage(cycle5, movers5, fs5, ms5, "Sol3 n=5")

# Sol3 n=7
ms7, fs7 = build_sol3(7)
cycle7, movers7, _ = extract_cycle(ms7, fs7)
if cycle7:
    h1_ok_7 = check_h1_uniqueness(cycle7, "Sol3 n=7")
    check_preimage_uniqueness(cycle7, movers7, fs7, ms7, "Sol3 n=7")
    check_h1_preimage(cycle7, movers7, fs7, ms7, "Sol3 n=7")

# CUP-2 n=5
ms_cup5, fs_cup5 = build_cup2(5)
cycle_cup5, movers_cup5, _ = extract_cycle(ms_cup5, fs_cup5)
if cycle_cup5:
    check_h1_uniqueness(cycle_cup5, "CUP-2 n=5")
    check_preimage_uniqueness(cycle_cup5, movers_cup5, fs_cup5, ms_cup5, "CUP-2 n=5")
    check_h1_preimage(cycle_cup5, movers_cup5, fs_cup5, ms_cup5, "CUP-2 n=5")

# CUP-2 n=7
ms_cup7, fs_cup7 = build_cup2(7)
cycle_cup7, movers_cup7, _ = extract_cycle(ms_cup7, fs_cup7)
if cycle_cup7:
    check_h1_uniqueness(cycle_cup7, "CUP-2 n=7")
    check_preimage_uniqueness(cycle_cup7, movers_cup7, fs_cup7, ms_cup7, "CUP-2 n=7")
    check_h1_preimage(cycle_cup7, movers_cup7, fs_cup7, ms_cup7, "CUP-2 n=7")

# Dijkstra Sol1 n=5 K=5
def build_sol1(n, K):
    ms = [K] * n
    def f_distinguished(L, S, R):
        if L == S: return (S + 1) % K
        return S
    def f_other(L, S, R):
        if L != S: return L
        return S
    fs = [f_distinguished] + [f_other] * (n - 1)
    return ms, fs

ms_d1, fs_d1 = build_sol1(5, 5)
cycle_d1, movers_d1, _ = extract_cycle(ms_d1, fs_d1)
if cycle_d1:
    check_h1_uniqueness(cycle_d1, "Dijkstra Sol1 n=5 K=5")
    check_preimage_uniqueness(cycle_d1, movers_d1, fs_d1, ms_d1, "Dijkstra Sol1 n=5 K=5")
    check_h1_preimage(cycle_d1, movers_d1, fs_d1, ms_d1, "Dijkstra Sol1 n=5 K=5")


# ── Part 2: Sweep / bounce cycles at n=9 ──

print("\n" + "=" * 70)
print("PART 2: Bounce cycle at n=9 (CLB witness)")
print("=" * 70)

def build_clb_n9():
    """Build CLB witness ms=(2,3,3,3,3,3,3,3,2)"""
    n = 9
    ms = [2, 3, 3, 3, 3, 3, 3, 3, 2]

    # Bounce cycle
    up_down = list(range(n)) + list(range(n - 2, 0, -1))
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    full = up_down * 3
    movers = []
    for step, mover in enumerate(full):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            movers = full[:step + 1]
            break
        if nc in visited:
            break
        visited.add(nc)
        cycle.append(nc)

    return cycle, movers, ms

cycle_n9, movers_n9, ms_n9 = build_clb_n9()
print(f"CLB n=9 bounce cycle: length = {len(cycle_n9)}")
check_h1_uniqueness(cycle_n9, "CLB n=9 bounce")


# ── Part 2b: CUP-2 at n=9 ──

ms_cup9, fs_cup9 = build_cup2(9)
cycle_cup9, movers_cup9, _ = extract_cycle(ms_cup9, fs_cup9)
if cycle_cup9:
    check_h1_uniqueness(cycle_cup9, "CUP-2 n=9")
    check_preimage_uniqueness(cycle_cup9, movers_cup9, fs_cup9, ms_cup9, "CUP-2 n=9")
    check_h1_preimage(cycle_cup9, movers_cup9, fs_cup9, ms_cup9, "CUP-2 n=9")


# ── Part 3: Detailed analysis ──

print("\n" + "=" * 70)
print("PART 3: WHY does H-1 uniqueness hold/fail?")
print("=" * 70)

def analyze_h1_structure(cycle, movers, ms, label=""):
    """Analyze the structure of H-1 pairs."""
    CL = len(cycle)
    n = len(ms)

    # For each adjacent pair, check if they're H-1
    adj_h1 = 0
    adj_not_h1 = 0
    for k in range(CL):
        k_next = (k + 1) % CL
        hd = hamming_distance(cycle[k], cycle[k_next])
        if hd == 1:
            adj_h1 += 1
        else:
            adj_not_h1 += 1

    print(f"\n{label}: Adjacent pair analysis")
    print(f"  Adjacent and H-1: {adj_h1}/{CL}")
    print(f"  Adjacent but H-d>1: {adj_not_h1}/{CL}")

    if adj_not_h1 > 0:
        print(f"  NOTE: Not all adjacent pairs are H-1!")
        print(f"  (This means some transitions change multiple positions... no, that's impossible)")
        print(f"  (Each transition changes exactly 1 position — the mover. So adjacent = H-1 always.)")

    # For each position p, count how many times it appears as the H-1 diff position
    # between any pair (not just adjacent)
    pos_counts = defaultdict(int)
    for j in range(CL):
        for k in range(j + 1, CL):
            if hamming_distance(cycle[j], cycle[k]) == 1:
                p = hamming_diff_positions(cycle[j], cycle[k])[0]
                pos_counts[p] += 1

    print(f"\n  H-1 pairs by diff position:")
    for p in sorted(pos_counts):
        mover_count = sum(1 for m in movers if m == p)
        print(f"    pos {p} (m_p={ms[p]}): {pos_counts[p]} H-1 pairs, fires {mover_count} times in cycle")

analyze_h1_structure(cycle5, movers5, ms5, "Sol3 n=5")
if cycle_cup5:
    analyze_h1_structure(cycle_cup5, movers_cup5, ms_cup5, "CUP-2 n=5")


# ── Part 4: The key question for forcedSucc_nonGood ──

print("\n" + "=" * 70)
print("PART 4: forcedSucc_nonGood — does it hold?")
print("=" * 70)

print("""
The question: if move(sys, c, p) = g_k and c is non-good,
does this lead to a contradiction?

c agrees with g_k everywhere except at position p.
c[p] != g_k[p], and f_p(g_k[left], c[p], g_k[right]) = g_k[p].

For this to be a contradiction, we need: no such non-good c exists.
Equivalently: every v with f_p(L, v, R) = g_k[p] and v != g_k[p]
must give a c that IS good.

Checked above via check_h1_preimage.
""")


# ── Part 5: Injectivity analysis ──

print("=" * 70)
print("PART 5: Transition injectivity analysis")
print("=" * 70)

def analyze_injectivity(fs, ms, label=""):
    """For each processor p and each (L, R) context,
    check if f_p(L, ·, R) is injective."""
    n = len(ms)
    non_injective = 0
    total = 0

    for p in range(n):
        m_L = ms[(p - 1) % n]
        m_R = ms[(p + 1) % n]
        for L in range(m_L):
            for R in range(m_R):
                total += 1
                outputs = {}
                for S in range(ms[p]):
                    out = fs[p](L, S, R)
                    if out in outputs:
                        non_injective += 1
                        break
                    outputs[out] = S

    print(f"\n{label}: Injectivity of f_p(L, ·, R)")
    print(f"  Total (p, L, R) contexts: {total}")
    print(f"  Non-injective: {non_injective}")
    print(f"  All injective: {non_injective == 0}")

analyze_injectivity(fs5, ms5, "Sol3 n=5")
if fs_cup5:
    analyze_injectivity(fs_cup5, ms_cup5, "CUP-2 n=5")
if fs_cup7:
    analyze_injectivity(fs_cup7, ms_cup7, "CUP-2 n=7")


# ── Summary ──

print("\n" + "=" * 70)
print("SUMMARY")
print("=" * 70)
