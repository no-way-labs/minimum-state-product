#!/usr/bin/env python3
"""CIC Exploration 2: Deep analysis of why multisets fail.

Key questions:
1. For multisets where no bounce cycle exists: does ANY good cycle exist?
2. For (2,2,2,2,2,4,4,4,4) where bounce cycles have forced SCCs:
   what's the structure of the forced SCCs?
3. Can we use the DFS cycle search tool to find non-bounce cycles?
4. Does the shadow cycle extend to mixed systems?
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict
import time


def build_bounce_cycle(ms, n, base_pattern=None, max_reps=5):
    if base_pattern is None:
        base_pattern = list(range(n - 1, -1, -1)) + list(range(1, n))
    for reps in range(1, max_reps):
        config = [0] * n
        cycle = [tuple(config)]
        visited = {tuple(config)}
        full = base_pattern * reps
        for step, mover in enumerate(full):
            config = list(cycle[-1])
            config[mover] = (config[mover] + 1) % ms[mover]
            nc = tuple(config)
            if nc == cycle[0]:
                return cycle, full[:step + 1]
            if nc in visited:
                break
            visited.add(nc)
            cycle.append(nc)
    return None, None


def max_consecutive_binary(ms, n):
    if all(v == 2 for v in ms):
        return n
    start = None
    for i in range(n):
        if ms[i] != 2:
            start = i
            break
    max_run = 0
    current_run = 0
    for j in range(n):
        idx = (start + j) % n
        if ms[idx] == 2:
            current_run += 1
            max_run = max(max_run, current_run)
        else:
            current_run = 0
    return max_run


# ================================================================
# Part 1: Analyze (2,2,2,2,2,4,4,4,4) — the one with forced SCCs
# ================================================================
print("=" * 70)
print("Part 1: Deep analysis of ms=(2,2,2,2,2,4,4,4,4)")
print("=" * 70)

n = 9
ms_base = (2, 2, 2, 2, 2, 4, 4, 4, 4)

# Try specific orientations where binary and quaternary are well-separated
orientations = [
    (2, 4, 2, 4, 2, 4, 2, 4, 2),  # alternating (5 binary, 4 quat)
    (2, 2, 2, 4, 4, 2, 2, 4, 4),  # grouped
    (4, 2, 2, 2, 4, 4, 2, 2, 4),  # binary triple + quat
    (4, 2, 4, 2, 4, 2, 4, 2, 2),
    (2, 4, 4, 2, 4, 4, 2, 2, 2),  # binary triple at end
    (4, 4, 2, 2, 2, 4, 4, 2, 2),
    (2, 2, 4, 4, 4, 4, 2, 2, 2),  # max binary run = 3
]

bounce_patterns = [
    ("down-up", list(range(n - 1, -1, -1)) + list(range(1, n))),
    ("up-down", list(range(n)) + list(range(n - 2, 0, -1))),
    ("fwd-sweep", list(range(n))),
    ("rev-sweep", list(range(n - 1, -1, -1))),
]

for ms in orientations:
    if sorted(ms) != sorted(ms_base):
        continue
    mc = max_consecutive_binary(ms, n)
    if mc > 3:
        continue
    print(f"\n  ms={ms}  max_consec={mc}")
    for pname, base in bounce_patterns:
        cycle, movers_seq = build_bounce_cycle(ms, n, base)
        if cycle is None:
            print(f"    {pname}: no cycle")
            continue
        print(f"    {pname}: cycle len={len(cycle)}, "
              f"movers={movers_seq[:20]}...")

        # Analyze forced transitions
        good_set = set(cycle)
        all_configs = list(cartesian(*(range(m) for m in ms)))
        non_good = [c for c in all_configs if c not in good_set]
        non_good_set = set(non_good)

        det = {}
        for idx in range(len(cycle)):
            c = cycle[idx]
            c_next = cycle[(idx + 1) % len(cycle)]
            mv = movers_seq[idx]
            for p in range(n):
                L = c[(p - 1) % n]
                S = c[p]
                R = c[(p + 1) % n]
                key = (p, L, S, R)
                if p == mv:
                    det[key] = c_next[p]
                else:
                    det[key] = S

        # Count mover entries per processor
        mover_entries = defaultdict(set)
        for idx in range(len(cycle)):
            c = cycle[idx]
            mv = movers_seq[idx]
            L = c[(mv - 1) % n]
            S = c[mv]
            R = c[(mv + 1) % n]
            mover_entries[mv].add((L, S, R))

        total_contexts = {}
        for p in range(n):
            m_L = ms[(p - 1) % n]
            m_S = ms[p]
            m_R = ms[(p + 1) % n]
            total_contexts[p] = m_L * m_S * m_R

        print(f"      Mover entries per processor:")
        for p in range(n):
            print(f"        P{p} (m={ms[p]}): "
                  f"{len(mover_entries[p])}/{total_contexts[p]} "
                  f"contexts used as mover "
                  f"({100*len(mover_entries[p])/total_contexts[p]:.0f}%)")

        # Build forced adjacency
        forced_adj = defaultdict(list)
        forced_priv_count = 0
        for c in non_good:
            priv_list = []
            for p in range(n):
                L = c[(p - 1) % n]
                S = c[p]
                R = c[(p + 1) % n]
                key = (p, L, S, R)
                if key in det and det[key] != S:
                    priv_list.append(p)
                    new_c = list(c)
                    new_c[p] = det[key]
                    nc = tuple(new_c)
                    if nc in non_good_set:
                        forced_adj[c].append(nc)
            if priv_list:
                forced_priv_count += 1

        print(f"      Non-good with forced privilege: "
              f"{forced_priv_count}/{len(non_good)} "
              f"({100*forced_priv_count/len(non_good):.0f}%)")

        # Find forced SCCs
        idx_counter = [0]
        stack = []
        on_stack = set()
        index_map = {}
        lowlink = {}
        sccs = []

        def strongconnect(v):
            work = [(v, 0)]
            index_map[v] = lowlink[v] = idx_counter[0]
            idx_counter[0] += 1
            stack.append(v)
            on_stack.add(v)
            while work:
                node, si = work[-1]
                succs = forced_adj.get(node, [])
                if si < len(succs):
                    work[-1] = (node, si + 1)
                    w = succs[si]
                    if w not in index_map:
                        index_map[w] = lowlink[w] = idx_counter[0]
                        idx_counter[0] += 1
                        stack.append(w)
                        on_stack.add(w)
                        work.append((w, 0))
                    elif w in on_stack:
                        lowlink[node] = min(
                            lowlink[node], index_map[w])
                else:
                    if lowlink[node] == index_map[node]:
                        scc = []
                        while True:
                            w = stack.pop()
                            on_stack.discard(w)
                            scc.append(w)
                            if w == node:
                                break
                        if (len(scc) > 1
                                or (scc[0] in forced_adj
                                    and scc[0] in forced_adj[scc[0]])):
                            sccs.append(scc)
                    work.pop()
                    if work:
                        lowlink[work[-1][0]] = min(
                            lowlink[work[-1][0]], lowlink[node])

        for v in forced_adj:
            if v not in index_map:
                strongconnect(v)

        if sccs:
            print(f"      FORCED SCCs: {len(sccs)}")
            for i, scc in enumerate(sccs[:3]):
                print(f"        SCC {i}: size={len(scc)}")
                if len(scc) <= 5:
                    for c in scc:
                        print(f"          {c}")
        else:
            print(f"      No forced SCCs")

# ================================================================
# Part 2: Try DFS good cycle search for a few orientations
# ================================================================
print(f"\n{'=' * 70}")
print("Part 2: DFS cycle search for selected orientations")
print("=" * 70)

try:
    from p2_good_cycle_search import search_good_cycle
    HAS_SEARCH = True
except ImportError:
    HAS_SEARCH = False
    print("  p2_good_cycle_search not available")

# Test a few key multisets with DFS
test_cases = [
    # ms, label
    ((5, 2, 5, 2, 5, 2, 2, 2, 2), "5-5-5 alternating"),
    ((4, 2, 4, 2, 4, 2, 4, 2, 2), "4-4-4-4 alternating"),
    ((2, 4, 4, 4, 4, 2, 2, 2, 2), "binary-triple + 4-quad"),
    ((3, 2, 3, 2, 4, 2, 5, 2, 2), "mixed ascending"),
]

if HAS_SEARCH:
    for ms, label in test_cases:
        n = len(ms)
        mc = max_consecutive_binary(ms, n)
        if mc > 3:
            print(f"\n  {label}: ms={ms} SKIP (consec={mc})")
            continue
        prod_val = 1
        for m in ms:
            prod_val *= m
        print(f"\n  {label}: ms={ms} product={prod_val}")
        t0 = time.time()
        result = search_good_cycle(ms, time_limit=10.0)
        t1 = time.time()
        if result.cycle is not None:
            print(f"    FOUND cycle of length {len(result.cycle)} "
                  f"[{t1-t0:.1f}s]")
            print(f"    movers: {result.movers[:20]}...")
        else:
            print(f"    No cycle found [{t1-t0:.1f}s]")
            print(f"    Stats: {result.stats}")

# ================================================================
# Part 3: Check if ALL multisets with ≥3 binary fail cycle search
# ================================================================
print(f"\n{'=' * 70}")
print("Part 3: Adjacent-mover constraint analysis")
print("=" * 70)

# For a walk on Z_n with steps {-1, 0, +1} that visits all positions,
# analyze what contexts are forced at binary processors.
# Key: binary processor p with binary neighbors has only 8 contexts.
# In a walk of length L, p is visited as mover ~L/n times.
# Minimum L for fairness = n. In a bounce: L = 2(n-1).
# So p is visited ~2 times per sweep through.

print("""
ADJACENT-MOVER LEMMA ANALYSIS:
- All good cycles have adjacent movers (proved above)
- Mover sequence is a walk on Z_n with steps {-1, 0, +1}
- Must visit all processors (fairness)
- Binary processor p in a triple (b,b,b) has only 8 contexts
- In a minimum-length cycle (L = 2n-2 for bounce):
  each processor is mover ~2 times -> uses 2 mover contexts
  appears as non-mover ~2n-4 times -> uses many non-mover contexts
- Key constraint: mover contexts ∩ non-mover contexts = ∅

COUNTING ARGUMENT for binary triple (positions i, i+1, i+2):
- P_{i+1} has m_L × 2 × m_R contexts
- If m_L = m_R = 2: only 8 contexts total
- Each mover pass uses 1 context (state 0→1 or 1→0)
- In a bounce, P_{i+1} is mover moving RIGHT and moving LEFT
- Right pass: context depends on what P_i just did
- Left pass: context depends on what P_{i+2} just did
- These mover contexts must all be DISTINCT from non-mover contexts

This is the BINARY CONTEXT BOTTLENECK:
With only 8 contexts and multiple passes in different directions,
the mover/non-mover separation becomes impossible for long enough cycles.
""")

# Verify: for binary triple, how many mover contexts can we have?
# In a bounce (0,1,...,n-1,n-2,...,1), each position is visited twice.
# For interior binary in triple, the context at each visit:
# Visit 1 (going right): (prev_left, current, prev_right)
# Visit 2 (going left): (new_left, current, new_right)

# The mover changes state: 0→1 or 1→0. So each visit uses a context
# with a specific self-state. Two visits can use (L,0,R)→1 and (L',1,R')→0

# For this to be compatible with non-mover appearances, NO non-mover
# config should have the same (L,S,R) as a mover config at position p.

# In a bounce cycle where all 3 positions are binary:
# Total configs involving this triple: 2^3 = 8 contexts for middle pos
# If we use 2+ as mover -> 6 or fewer as non-mover
# But non-mover appears at EVERY step except when p is mover
# In a cycle of length L, p is non-mover L-2 times -> sees many contexts

print(f"\n{'=' * 70}")
print("Part 4: Forced SCC analysis for ALL 57 multisets")
print("=" * 70)

# Check: for ALL 57 candidate multisets (not just the 12 surviving ones),
# do bounce cycles produce forced SCCs?

from cic_enumerate import enumerate_multisets, can_place_with_consecutive_le3

candidates = enumerate_multisets(n, 4 * 3**7)
valid_candidates = [
    (ms, p, k) for ms, p, k in candidates
    if can_place_with_consecutive_le3(ms, n)
]
valid_candidates.sort(key=lambda x: x[1])

print(f"Testing {len(valid_candidates)} multisets...")

bounce_pats = [
    list(range(n - 1, -1, -1)) + list(range(1, n)),
    list(range(n)) + list(range(n - 2, 0, -1)),
]

results_by_failure = defaultdict(list)

for ms_sorted, product, k_binary in valid_candidates:
    # Try a few orientations
    from cic_kill_survivors import multiset_perms
    seen = set()
    tested = 0
    has_cycle = False
    has_scc = False
    has_overlap = False

    for perm in multiset_perms(list(ms_sorted)):
        if tested > 50:
            break
        variants = []
        for r in range(n):
            rot = tuple(perm[(i + r) % n] for i in range(n))
            variants.append(rot)
            ref = tuple(perm[(r - i) % n] for i in range(n))
            variants.append(ref)
        canonical = min(variants)
        if canonical in seen:
            continue
        seen.add(canonical)
        ms_perm = canonical

        mc = max_consecutive_binary(ms_perm, n)
        if mc > 3:
            continue

        for base in bounce_pats:
            cycle, mseq = build_bounce_cycle(ms_perm, n, base)
            if cycle is None:
                continue
            has_cycle = True
            tested += 1

            # Check overlap
            mover_t = defaultdict(set)
            nonmover_t = defaultdict(set)
            for idx in range(len(cycle)):
                c = cycle[idx]
                mv = mseq[idx]
                for p in range(n):
                    tr = (c[(p - 1) % n], c[p], c[(p + 1) % n])
                    if p == mv:
                        mover_t[p].add(tr)
                    else:
                        nonmover_t[p].add(tr)
            overlap = any(
                mover_t[p] & nonmover_t[p] for p in range(n))
            if overlap:
                has_overlap = True
                continue

            # Check forced SCCs (simplified)
            good_set = set(cycle)
            all_configs = list(cartesian(*(range(m) for m in ms_perm)))
            non_good_set = set(c for c in all_configs if c not in good_set)

            det = {}
            for idx in range(len(cycle)):
                c = cycle[idx]
                c_next = cycle[(idx + 1) % len(cycle)]
                mv = mseq[idx]
                for p in range(n):
                    L = c[(p - 1) % n]
                    S = c[p]
                    R = c[(p + 1) % n]
                    key = (p, L, S, R)
                    if p == mv:
                        det[key] = c_next[p]
                    else:
                        det[key] = S

            forced_adj = defaultdict(list)
            for c in non_good_set:
                for p in range(n):
                    L = c[(p - 1) % n]
                    S = c[p]
                    R = c[(p + 1) % n]
                    key = (p, L, S, R)
                    if key in det and det[key] != S:
                        new_c = list(c)
                        new_c[p] = det[key]
                        nc = tuple(new_c)
                        if nc in non_good_set:
                            forced_adj[c].append(nc)

            # Quick SCC check: look for a 2-cycle
            has_2cycle = False
            for c in forced_adj:
                for nc in forced_adj[c]:
                    if c in forced_adj.get(nc, []):
                        has_2cycle = True
                        break
                if has_2cycle:
                    break

            if has_2cycle:
                has_scc = True

    if not has_cycle:
        reason = "no_bounce_cycle"
    elif has_overlap and not has_scc:
        reason = "overlap_only"
    elif has_scc:
        reason = "forced_scc"
    else:
        reason = "no_scc_found"
    results_by_failure[reason].append((ms_sorted, product, k_binary))

print()
for reason, items in sorted(results_by_failure.items()):
    print(f"  {reason}: {len(items)} multisets")
    for ms, prod, k in items[:5]:
        print(f"    ms={ms} product={prod} k={k}")
    if len(items) > 5:
        print(f"    ... and {len(items)-5} more")
