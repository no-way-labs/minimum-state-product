#!/usr/bin/env python3
"""
COPY-PAIR REACHABILITY ANALYSIS
================================
Question: After TP-preserving steps (which all copy a neighbor), does every
interior position eventually get a "copy-pair" (c[k]=c[k-1] or c[k]=c[k+1])?

For n=9, ms=(2,3,3,3,3,3,3,3,2), total configs = 4*3^7 = 8748.

Analysis:
1. Which bad configs have at least one interior copy-pair?
2. For those without: does BFS on TP-preserving steps reach one?
3. For configs reachable from CΦ boundary-changing steps: do they all have copy-pairs?
"""

import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_final_verify import build_system, T_bot, T_low, T_mid, T_high, T_top
from itertools import product as cartesian
from collections import defaultdict, deque

N = 9

# ================================================================
# CUP-2 system
# ================================================================

ms, fs = build_system(N)
assert ms == [2, 3, 3, 3, 3, 3, 3, 3, 2]

all_configs = list(cartesian(*(range(m) for m in ms)))
print(f"Total configs: {len(all_configs)}")
assert len(all_configs) == 8748

# ================================================================
# Utility functions
# ================================================================

def fc(c):
    return sum(1 for j in range(N) if c[j] != c[(j + 1) % N])

def is_privileged(c, j):
    L = c[(j - 1) % N]
    S = c[j]
    R = c[(j + 1) % N]
    return fs[j](L, S, R) != S

def fire(c, j):
    L = c[(j - 1) % N]
    S = c[j]
    R = c[(j + 1) % N]
    out = fs[j](L, S, R)
    lst = list(c)
    lst[j] = out
    return tuple(lst)

def num_privileged(c):
    return sum(1 for j in range(N) if is_privileged(c, j))

def exp2_count(c):
    return sum(1 for j in range(2, N - 2) if c[j] == 2 and c[(j + 1) % N] in (0, 1))

def int_21(c):
    return sum(1 for j in range(2, N - 2) if c[j] == 2 and c[(j + 1) % N] == 1)

def exp2_weight(c):
    return sum(j for j in range(2, N - 2) if c[j] == 2 and c[(j + 1) % N] in (0, 1))

def tp_triple(c):
    return (exp2_count(c), int_21(c), exp2_weight(c))

def has_interior_copy_pair(c, lo=3, hi=None):
    """Check if any interior position k in [lo, hi] has c[k]=c[k-1] or c[k]=c[k+1].
    Default range: k in {3,...,n-4} = {3,4,5} for n=9."""
    if hi is None:
        hi = N - 4  # = 5 for n=9
    for k in range(lo, hi + 1):
        if c[k] == c[k - 1] or c[k] == c[k + 1]:
            return True
    return False

def has_any_copy_pair(c):
    """Check if ANY position k in {1,...,n-2} has c[k]=c[k-1] or c[k]=c[k+1]."""
    for k in range(1, N - 1):
        if c[k] == c[k - 1] or c[k] == c[k + 1]:
            return True
    return False

def copy_pair_positions(c):
    """Return set of positions with a copy-pair."""
    result = []
    for k in range(1, N - 1):
        if c[k] == c[k - 1] or c[k] == c[k + 1]:
            result.append(k)
    return result

# ================================================================
# Find good configs (cycle)
# ================================================================
print("\n--- Finding good cycle ---")

# Use the verifier approach: find all configs with exactly 1 privileged processor
# Actually let's just build the full system and verify
from verifier import verify_system
result = verify_system(ms, fs)
assert result['valid'], "System is not valid!"
good_set = result['good_configs']
print(f"Good configs: {len(good_set)}")
print(f"Bad configs: {len(all_configs) - len(good_set)}")

bad_configs = [c for c in all_configs if c not in good_set]
bad_set = set(bad_configs)

# ================================================================
# PART 1: Copy-pair prevalence among bad configs
# ================================================================
print("\n" + "=" * 70)
print("PART 1: COPY-PAIR PREVALENCE IN BAD CONFIGS")
print("=" * 70)

# Check interior copy-pairs (positions 3..5 for n=9)
interior_cp = [c for c in bad_configs if has_interior_copy_pair(c)]
no_interior_cp = [c for c in bad_configs if not has_interior_copy_pair(c)]
print(f"\nInterior copy-pair (positions 3..{N-4}):")
print(f"  With copy-pair: {len(interior_cp)} / {len(bad_configs)} "
      f"({100*len(interior_cp)/len(bad_configs):.1f}%)")
print(f"  Without copy-pair: {len(no_interior_cp)} / {len(bad_configs)} "
      f"({100*len(no_interior_cp)/len(bad_configs):.1f}%)")

# Also check wider range (positions 1..n-2)
any_cp = [c for c in bad_configs if has_any_copy_pair(c)]
no_any_cp = [c for c in bad_configs if not has_any_copy_pair(c)]
print(f"\nAny copy-pair (positions 1..{N-2}):")
print(f"  With copy-pair: {len(any_cp)} / {len(bad_configs)} "
      f"({100*len(any_cp)/len(bad_configs):.1f}%)")
print(f"  Without copy-pair: {len(no_any_cp)} / {len(bad_configs)} "
      f"({100*len(no_any_cp)/len(bad_configs):.1f}%)")

# Show some examples of no-copy-pair configs
if no_interior_cp:
    print(f"\nSample configs with NO interior copy-pair (showing first 10):")
    for c in no_interior_cp[:10]:
        cps = copy_pair_positions(c)
        fc_val = fc(c)
        print(f"  {list(c)}  fc={fc_val}  copy-pairs at: {cps}")

if no_any_cp:
    print(f"\nConfigs with NO copy-pair anywhere (first 10):")
    for c in no_any_cp[:10]:
        fc_val = fc(c)
        print(f"  {list(c)}  fc={fc_val}")

# ================================================================
# PART 2: Build TP-preserving graph on bad configs
# ================================================================
print("\n" + "=" * 70)
print("PART 2: TP-PRESERVING TRANSITIONS")
print("=" * 70)

tp_adj = defaultdict(list)   # c -> list of (succ, pos, dfc)
tp_edge_count = 0

for c in bad_configs:
    e2c, i21c, ewc = tp_triple(c)
    fc_c = fc(c)
    for j in range(N):
        if is_privileged(c, j):
            succ = fire(c, j)
            if succ in bad_set:
                e2s, i21s, ews = tp_triple(succ)
                if e2s == e2c and i21s == i21c and ews == ewc:
                    dfc = fc(succ) - fc_c
                    tp_adj[c].append((succ, j, dfc))
                    tp_edge_count += 1

print(f"TP-preserving edges (bad→bad): {tp_edge_count}")

# ================================================================
# Verify: ALL TP-preserving TMid steps copy a neighbor
# ================================================================
print("\n--- Verifying TMid copy-neighbor property ---")
tmid_priv_entries = []
for L, S, R in cartesian(range(3), range(3), range(3)):
    out = T_mid[(L, S, R)]
    if out != S:
        copies_L = (out == L)
        copies_R = (out == R)
        tmid_priv_entries.append((L, S, R, out, copies_L, copies_R))

all_copy = all(cL or cR for _, _, _, _, cL, cR in tmid_priv_entries)
print(f"TMid privileged entries: {len(tmid_priv_entries)}")
print(f"ALL copy a neighbor: {all_copy}")
for L, S, R, out, cL, cR in tmid_priv_entries:
    tag = []
    if cL: tag.append("copies_L")
    if cR: tag.append("copies_R")
    print(f"  ({L},{S},{R})→{out}  {', '.join(tag)}")

# Also check TLow and THigh
print("\nTLow privileged entries:")
for L in range(2):
    for S in range(3):
        for R in range(3):
            out = T_low[(L, S, R)]
            if out != S:
                cL = (out == L); cR = (out == R)
                tag = []
                if cL: tag.append("copies_L")
                if cR: tag.append("copies_R")
                if not cL and not cR: tag.append("ANOMALOUS")
                print(f"  ({L},{S},{R})→{out}  {', '.join(tag)}")

print("\nTHigh privileged entries:")
for L in range(3):
    for S in range(3):
        for R in range(2):
            out = T_high[(L, S, R)]
            if out != S:
                cL = (out == L); cR = (out == R)
                tag = []
                if cL: tag.append("copies_L")
                if cR: tag.append("copies_R")
                if not cL and not cR: tag.append("ANOMALOUS")
                print(f"  ({L},{S},{R})→{out}  {', '.join(tag)}")

# ================================================================
# PART 3: TP-reachability from no-copy-pair configs
# ================================================================
print("\n" + "=" * 70)
print("PART 3: TP-REACHABILITY FROM NO-COPY-PAIR CONFIGS")
print("=" * 70)

if no_interior_cp:
    # For each no-interior-copy-pair config, BFS on TP edges
    max_dist_to_cp = 0
    never_reach_cp = 0
    dist_histogram = defaultdict(int)

    for c_start in no_interior_cp:
        # BFS
        visited = {c_start: 0}
        queue = deque([c_start])
        found_cp = False
        min_dist_cp = None

        while queue:
            c = queue.popleft()
            d = visited[c]
            if d > 0 and has_interior_copy_pair(c):
                if min_dist_cp is None or d < min_dist_cp:
                    min_dist_cp = d
                    found_cp = True
                continue  # Don't expand beyond first copy-pair
            for succ, pos, dfc in tp_adj.get(c, []):
                if succ not in visited:
                    visited[succ] = d + 1
                    queue.append(succ)

        if found_cp:
            dist_histogram[min_dist_cp] += 1
            max_dist_to_cp = max(max_dist_to_cp, min_dist_cp)
        else:
            never_reach_cp += 1

    print(f"\nNo-interior-copy-pair configs: {len(no_interior_cp)}")
    print(f"  Reach copy-pair via TP: {len(no_interior_cp) - never_reach_cp}")
    print(f"  NEVER reach copy-pair via TP: {never_reach_cp}")
    if dist_histogram:
        print(f"  Max TP distance to copy-pair: {max_dist_to_cp}")
        print(f"  Distance histogram:")
        for d in sorted(dist_histogram):
            print(f"    d={d}: {dist_histogram[d]}")

# ================================================================
# PART 4: After ANY single TP step, does copy-pair appear?
# ================================================================
print("\n" + "=" * 70)
print("PART 4: COPY-PAIR AFTER SINGLE TP STEP")
print("=" * 70)

# For each TP edge (c -> succ) where position j (interior, TMid) fires:
# Does succ have c[j]=c[j-1] or c[j]=c[j+1]? (Yes, by copy property.)
# But we want to know: does the WHOLE config have an interior copy-pair?

tp_steps_total = 0
tp_steps_create_cp = 0
tp_steps_at_interior = 0  # position j in {2,...,n-3}

for c in bad_configs:
    for succ, pos, dfc in tp_adj.get(c, []):
        tp_steps_total += 1
        # Is position 'pos' interior (uses TMid)?
        if 2 <= pos <= N - 3:
            tp_steps_at_interior += 1
            # After firing at pos, succ[pos] = L or R of c
            # So succ[pos] = c[pos-1] or succ[pos] = c[pos+1]
            # Since only pos changed: succ[pos-1] = c[pos-1], succ[pos+1] = c[pos+1]
            # So succ[pos] = succ[pos-1] or succ[pos] = succ[pos+1]
            # This IS a copy-pair at position pos.
            # But is pos in {3,...,n-4}?
            if 3 <= pos <= N - 4:
                tp_steps_create_cp += 1

print(f"Total TP edges: {tp_steps_total}")
print(f"TP edges at interior TMid positions (2..{N-3}): {tp_steps_at_interior}")
print(f"TP edges at deep interior ({3}..{N-4}): {tp_steps_create_cp}")

# Verify: every TMid fire creates a copy-pair at that position
print("\nVerifying: every TMid fire at pos creates copy-pair at pos...")
violations = 0
for c in bad_configs:
    for succ, pos, dfc in tp_adj.get(c, []):
        if 2 <= pos <= N - 3:
            # succ[pos] should equal succ[pos-1] or succ[pos+1]
            if succ[pos] != succ[pos - 1] and succ[pos] != succ[pos + 1]:
                violations += 1
                print(f"  VIOLATION: {list(c)} fire@{pos} -> {list(succ)}")
print(f"Violations: {violations}")

# ================================================================
# PART 5: Φ_full and constant-Φ analysis
# ================================================================
print("\n" + "=" * 70)
print("PART 5: CONSTANT-Φ BOUNDARY-CHANGING STEPS AND COPY-PAIRS")
print("=" * 70)

# Build Φ_full (max reachable fc over TP paths)
fc_cache = {c: fc(c) for c in bad_configs}
tp_fwd = defaultdict(list)
for c in bad_configs:
    for succ, pos, dfc in tp_adj.get(c, []):
        tp_fwd[c].append(succ)

# g[c] = max fc gain reachable from c via TP edges
g = {c: 0 for c in bad_configs}
for _ in range(2 * N + 10):
    changed = False
    for c in bad_configs:
        for s in tp_fwd.get(c, []):
            dfc = fc_cache[s] - fc_cache[c]
            new_g = dfc + g[s]
            if new_g > g[c]:
                g[c] = new_g
                changed = True
    if not changed:
        break

phi = {c: fc_cache[c] + g[c] for c in bad_configs}

# Find constant-Φ edges with 6-tuple change (boundary-changing)
const_phi_boundary = []  # edges where phi stays same but 6-tuple changes
for c in bad_configs:
    for succ, pos, dfc in tp_adj.get(c, []):
        if phi.get(succ, -999) == phi.get(c, -999):
            s6c = (c[0], c[1], c[2], c[N-3], c[N-2], c[N-1])
            s6s = (succ[0], succ[1], succ[2], succ[N-3], succ[N-2], succ[N-1])
            if s6c != s6s:
                const_phi_boundary.append((c, succ, pos))

print(f"Constant-Φ boundary-changing TP edges: {len(const_phi_boundary)}")

# Check: do the SOURCE configs of these edges have copy-pairs?
src_with_cp = sum(1 for c, s, p in const_phi_boundary if has_interior_copy_pair(c))
src_without_cp = len(const_phi_boundary) - src_with_cp
print(f"  Source has interior copy-pair: {src_with_cp}")
print(f"  Source lacks interior copy-pair: {src_without_cp}")

# Check: do the TARGET configs have copy-pairs?
tgt_with_cp = sum(1 for c, s, p in const_phi_boundary if has_interior_copy_pair(s))
tgt_without_cp = len(const_phi_boundary) - tgt_with_cp
print(f"  Target has interior copy-pair: {tgt_with_cp}")
print(f"  Target lacks interior copy-pair: {tgt_without_cp}")

# Check with wider range
src_with_any_cp = sum(1 for c, s, p in const_phi_boundary if has_any_copy_pair(c))
tgt_with_any_cp = sum(1 for c, s, p in const_phi_boundary if has_any_copy_pair(s))
print(f"\n  Source has ANY copy-pair (pos 1..{N-2}): {src_with_any_cp}/{len(const_phi_boundary)}")
print(f"  Target has ANY copy-pair (pos 1..{N-2}): {tgt_with_any_cp}/{len(const_phi_boundary)}")

# ================================================================
# PART 6: Which positions fire in constant-Φ boundary-changing steps?
# ================================================================
print("\n" + "=" * 70)
print("PART 6: POSITION ANALYSIS OF CONSTANT-Φ BOUNDARY STEPS")
print("=" * 70)

pos_hist = defaultdict(int)
for c, s, p in const_phi_boundary:
    pos_hist[p] += 1
print("Firing position distribution:")
for p in sorted(pos_hist):
    print(f"  pos={p}: {pos_hist[p]} edges")

# For boundary-changing steps: show examples without copy-pair
if src_without_cp > 0:
    print(f"\nExamples: CΦ boundary-changing with NO interior copy-pair at source:")
    count = 0
    for c, s, p in const_phi_boundary:
        if not has_interior_copy_pair(c):
            if count < 15:
                cps_c = copy_pair_positions(c)
                cps_s = copy_pair_positions(s)
                print(f"  {list(c)} fire@{p} -> {list(s)}")
                print(f"    src copy-pairs: {cps_c}, tgt copy-pairs: {cps_s}")
                print(f"    fc: {fc_cache[c]}→{fc_cache.get(s, fc(s))}, phi: {phi[c]}")
            count += 1
    if count > 15:
        print(f"  ... and {count - 15} more")

# ================================================================
# PART 7: Full TP-reachable set from CΦ boundary-changing configs
# ================================================================
print("\n" + "=" * 70)
print("PART 7: TP-REACHABLE FROM CΦ BOUNDARY-CHANGING TARGETS")
print("=" * 70)

# Collect all unique target configs of boundary-changing constant-Φ steps
cphi_targets = set(s for c, s, p in const_phi_boundary)
print(f"Unique CΦ boundary-changing targets: {len(cphi_targets)}")

# BFS from these targets on TP edges (within same Φ level)
cphi_reachable = set(cphi_targets)
queue = deque(cphi_targets)
while queue:
    c = queue.popleft()
    for s in tp_fwd.get(c, []):
        if phi.get(s, -999) == phi.get(c, -999) and s not in cphi_reachable:
            cphi_reachable.add(s)
            queue.append(s)

print(f"TP-reachable from CΦ boundary targets (same Φ): {len(cphi_reachable)}")

cphi_with_cp = sum(1 for c in cphi_reachable if has_interior_copy_pair(c))
cphi_without_cp = len(cphi_reachable) - cphi_with_cp
print(f"  With interior copy-pair: {cphi_with_cp}")
print(f"  Without interior copy-pair: {cphi_without_cp}")

if cphi_without_cp > 0:
    print(f"\nCΦ-reachable configs WITHOUT interior copy-pair:")
    count = 0
    for c in cphi_reachable:
        if not has_interior_copy_pair(c):
            if count < 20:
                cps = copy_pair_positions(c)
                print(f"  {list(c)}  fc={fc_cache.get(c, fc(c))} phi={phi.get(c,'?')} cp={cps}")
            count += 1
    if count > 20:
        print(f"  ... and {count - 20} more")

# ================================================================
# PART 8: Summary
# ================================================================
print("\n" + "=" * 70)
print("SUMMARY")
print("=" * 70)

print(f"n={N}, total configs={len(all_configs)}, bad configs={len(bad_configs)}")
print(f"Interior copy-pair (pos 3..{N-4}): {len(interior_cp)}/{len(bad_configs)} "
      f"({100*len(interior_cp)/len(bad_configs):.1f}%)")
print(f"Any copy-pair (pos 1..{N-2}): {len(any_cp)}/{len(bad_configs)} "
      f"({100*len(any_cp)/len(bad_configs):.1f}%)")
print(f"TMid copy-neighbor: ALL = {all_copy}")
print(f"CΦ boundary-changing edges: {len(const_phi_boundary)}")
print(f"CΦ targets without interior copy-pair: {tgt_without_cp}")
print(f"CΦ-reachable without interior copy-pair: {cphi_without_cp}")
