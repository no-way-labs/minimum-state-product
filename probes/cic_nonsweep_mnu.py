#!/usr/bin/env python3
"""CIC Exploration 4 (revised): MNU for non-sweep good cycles.

The original cic_general_mnu.py found 0 cycles because all sub-threshold
systems are invalid (vacuously true). This revised version tests MNU on
KNOWN VALID systems with non-sweep good cycles:

1. CLB system: ms=(2,3,...,3,2), bounce cycle (not a sweep)
2. M_5=96 witness: ms=(2,2,2,3,4), extract its good cycle type
3. Dijkstra Sol 3 at n=5: ms=(3,3,3,3,3), known sweep

Key question: Does MNU hold for ALL good cycles, or only sweeps?
If MNU fails for bounce cycles, the non-sweep gap is real.
"""

from itertools import product as iproduct
import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from verifier import verify_system


def check_mnu(cycle, n):
    """Check Mover Neighborhood Uniqueness for a good cycle."""
    movers = []
    for idx in range(len(cycle)):
        c = cycle[idx]; c_next = cycle[(idx + 1) % len(cycle)]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return None  # not a valid single-mover cycle
        movers.append(diffs[0])

    violations = []
    for step in range(len(cycle)):
        p = movers[step]
        gc = cycle[step]
        gc_next = cycle[(step + 1) % len(cycle)]
        L = gc[(p - 1) % n]
        S_prime = gc_next[p]
        R = gc[(p + 1) % n]
        # Count configs in C where proc p sees (L, S_prime, R)
        matches = [j for j, gj in enumerate(cycle)
                   if gj[(p - 1) % n] == L and gj[p] == S_prime and gj[(p + 1) % n] == R]
        if len(matches) != 1:
            violations.append((step, p, L, S_prime, R, len(matches), matches))

    return violations


def check_universal_escape(cycle, det, ms, n, max_configs=50000):
    """Check that no forced move at a non-good config enters C."""
    good_set = set(cycle)
    product_val = 1
    for m in ms:
        product_val *= m
    if product_val > max_configs:
        return None, 0  # too large

    failures = []
    total = 0
    for c in iproduct(*[range(m) for m in ms]):
        if c in good_set:
            continue
        for i in range(n):
            L, S, R = c[(i - 1) % n], c[i], c[(i + 1) % n]
            key = (i, L, S, R)
            if key in det and det[key] != S:
                total += 1
                new_c = list(c)
                new_c[i] = det[key]
                if tuple(new_c) in good_set:
                    failures.append((c, i, tuple(new_c)))
    return failures, total


def extract_cycle_and_det(cycle, movers, n):
    """Extract determined entries from a good cycle."""
    det = {}
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        mv = movers[idx]
        for p in range(n):
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            key = (p, L, S, R)
            if p == mv:
                det[key] = c_next[p]
            else:
                det[key] = S
    return det


def build_clb_system(n):
    """Build the CLB bounce cycle system for ms=(2,3,...,3,2)."""
    ms = tuple([2] + [3] * (n - 2) + [2])
    up_down = list(range(n)) + list(range(n - 2, 0, -1))
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    full = up_down * (n + 5)
    movers = None
    for step, mover in enumerate(full):
        if step >= len(full):
            break
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            movers = full[:step + 1]
            break
        if nc in visited:
            return None, None, None, None
        visited.add(nc)
        cycle.append(nc)
    if movers is None:
        return None, None, None, None
    return ms, cycle, movers, n


def classify_cycle(movers, n):
    """Classify cycle type: sweep, bounce, or other."""
    sweep = list(range(n)) * (len(movers) // n) if len(movers) % n == 0 else None
    if sweep and movers == sweep:
        return "uniform_sweep"

    # Check if it's a bounce: 0,1,...,n-1,n-2,...,1 repeated
    bounce_unit = list(range(n)) + list(range(n - 2, 0, -1))
    if len(movers) % len(bounce_unit) == 0:
        reps = len(movers) // len(bounce_unit)
        if movers == bounce_unit * reps:
            return f"bounce_x{reps}"

    # Check for partial bounce
    for prefix_len in range(len(bounce_unit), len(movers) + 1):
        if movers == (bounce_unit * ((prefix_len // len(bounce_unit)) + 1))[:len(movers)]:
            return f"bounce_partial_{len(movers)}"

    return f"other_L{len(movers)}"


# ============================================================
# Test 1: CLB bounce cycle (non-sweep, known valid)
# ============================================================
print("=" * 70)
print("TEST 1: CLB BOUNCE CYCLE — MNU CHECK")
print("=" * 70)

for n in [5, 6, 7, 8, 9]:
    ms, cycle, movers, _ = build_clb_system(n)
    if cycle is None:
        print(f"\n  n={n}: bounce cycle construction failed")
        continue

    product_val = 1
    for m in ms:
        product_val *= m

    cycle_type = classify_cycle(movers, n)
    det = extract_cycle_and_det(cycle, movers, n)

    # Count determined and free entries
    total_entries = sum(ms[(p - 1) % n] * ms[p] * ms[(p + 1) % n] for p in range(n))
    det_count = len(det)
    free_count = total_entries - det_count

    print(f"\n  n={n}, ms={list(ms)}, product={product_val}")
    print(f"  Cycle: length={len(cycle)}, type={cycle_type}")
    print(f"  Movers: {movers}")
    print(f"  Entries: {det_count} determined, {free_count} free (of {total_entries})")

    # Check MNU
    violations = check_mnu(cycle, n)
    if violations is None:
        print(f"  MNU: INVALID CYCLE (multi-mover step)")
    elif len(violations) == 0:
        print(f"  MNU: OK (0 violations)")
    else:
        print(f"  MNU: FAIL ({len(violations)} violations)")
        for v in violations[:5]:
            step, p, L, S_prime, R, num_matches, matches = v
            print(f"    Step {step}: P{p} post-move (L={L},S'={S_prime},R={R})"
                  f" appears in {num_matches} cycle configs: {matches}")

    # Check Universal Escape
    if product_val <= 50000:
        esc_fails, total = check_universal_escape(cycle, det, ms, n)
        if esc_fails is None:
            print(f"  Escape: skipped (product too large)")
        elif len(esc_fails) == 0:
            print(f"  Escape: OK ({total} forced moves, 0 enter C)")
        else:
            print(f"  Escape: FAIL ({len(esc_fails)}/{total} moves enter C)")
            for f in esc_fails[:3]:
                c, i, nc = f
                print(f"    {c} → P{i} → {nc} (in C)")


# ============================================================
# Test 2: M_5 = 96 witness — what cycle type?
# ============================================================
print(f"\n{'=' * 70}")
print("TEST 2: M_5 = 96 WITNESS — CYCLE TYPE AND MNU")
print("=" * 70)

# The M_5=96 system uses ms=(2,2,2,3,4), product=96
# Let's build it using the verifier to find a valid system
n = 5
ms_96 = (2, 2, 2, 3, 4)

# Build via good-targeting approach (same as CLB but for this ms)
# Try bounce cycle first
for attempt_ms in [(2, 2, 2, 3, 4), (2, 2, 3, 2, 4), (2, 3, 2, 2, 4),
                   (4, 2, 2, 2, 3), (3, 2, 2, 2, 4), (4, 3, 2, 2, 2),
                   (2, 4, 2, 3, 2), (2, 2, 4, 3, 2)]:
    product_val = 1
    for m in attempt_ms:
        product_val *= m

    # Try uniform sweep cycle
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    sweep_movers = list(range(n)) * 4
    valid_sweep = True
    for step, mover in enumerate(sweep_movers):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % attempt_ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            sweep_movers = sweep_movers[:step + 1]
            break
        if nc in visited:
            valid_sweep = False
            break
        visited.add(nc)
        cycle.append(nc)
    else:
        valid_sweep = False

    if valid_sweep and len(cycle) >= 2 * n:
        det = extract_cycle_and_det(cycle, sweep_movers, n)
        ok, _ = check_consistency_simple(cycle, n) if False else (True, None)

        cycle_type = classify_cycle(sweep_movers, n)
        print(f"\n  ms={list(attempt_ms)}, product={product_val}")
        print(f"  Sweep cycle: length={len(cycle)}, type={cycle_type}")

        violations = check_mnu(cycle, n)
        if violations is not None:
            print(f"  MNU: {'OK' if len(violations) == 0 else f'FAIL ({len(violations)} violations)'}")

    # Try bounce cycle
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    bounce_unit = list(range(n)) + list(range(n - 2, 0, -1))
    bounce_movers = bounce_unit * 5
    valid_bounce = True
    for step, mover in enumerate(bounce_movers):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % attempt_ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            bounce_movers = bounce_movers[:step + 1]
            break
        if nc in visited:
            valid_bounce = False
            break
        visited.add(nc)
        cycle.append(nc)
    else:
        valid_bounce = False

    if valid_bounce and len(cycle) >= 2 * n:
        det = extract_cycle_and_det(cycle, bounce_movers, n)
        cycle_type = classify_cycle(bounce_movers, n)
        print(f"  Bounce cycle: length={len(cycle)}, type={cycle_type}")

        violations = check_mnu(cycle, n)
        if violations is not None:
            print(f"  MNU: {'OK' if len(violations) == 0 else f'FAIL ({len(violations)} violations)'}")


# ============================================================
# Test 3: Dijkstra Sol 3 — known sweep, baseline
# ============================================================
print(f"\n{'=' * 70}")
print("TEST 3: DIJKSTRA SOL 3 — BASELINE MNU CHECK")
print("=" * 70)

for n in [5, 6, 7]:
    ms = tuple([3] * n)
    product_val = 3 ** n

    # Sol 3 sweep cycle: configs are g_j[i] = j+i mod 3 for waterfall
    # Actually, build via uniform sweep
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    sweep = list(range(n)) * 10
    movers = None
    for step, mover in enumerate(sweep):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % 3
        nc = tuple(config)
        if nc == cycle[0]:
            movers = sweep[:step + 1]
            break
        if nc in visited:
            break
        visited.add(nc)
        cycle.append(nc)

    if movers is not None:
        cycle_type = classify_cycle(movers, n)
        det = extract_cycle_and_det(cycle, movers, n)

        print(f"\n  n={n}, ms={list(ms)}, product={product_val}")
        print(f"  Cycle: length={len(cycle)}, type={cycle_type}")

        violations = check_mnu(cycle, n)
        if violations is not None:
            print(f"  MNU: {'OK' if len(violations) == 0 else f'FAIL ({len(violations)} violations)'}")
            if violations:
                for v in violations[:5]:
                    step, p, L, S_prime, R, num_matches, matches = v
                    print(f"    Step {step}: P{p} (L={L},S'={S_prime},R={R})"
                          f" → {num_matches} matches at {matches}")

        if product_val <= 50000:
            esc_fails, total = check_universal_escape(cycle, det, ms, n)
            if esc_fails is not None:
                print(f"  Escape: {'OK' if len(esc_fails) == 0 else f'FAIL ({len(esc_fails)}/{total})'}")


# ============================================================
# Test 4: CLB full system — check MNU for completed system
# ============================================================
print(f"\n{'=' * 70}")
print("TEST 4: CLB FULL SYSTEM — MNU + ESCAPE + FORCED SCCs")
print("=" * 70)

for n in [5, 6, 7]:
    ms, cycle, movers, _ = build_clb_system(n)
    if cycle is None:
        continue

    product_val = 1
    for m in ms:
        product_val *= m

    det = extract_cycle_and_det(cycle, movers, n)
    good_set = set(cycle)

    # Now complete the system using good-targeting
    from collections import defaultdict
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    # Find free entries
    free_entries = []
    for p in range(n):
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    if key not in det:
                        free_entries.append(key)

    # Good-targeting completion
    comp = dict(det)
    for key in free_entries:
        p, L, S, R = key
        best_out = S  # identity
        best_good = 0
        best_ng = float('inf')
        for out in range(ms[p]):
            good_count = 0
            ng_count = 0
            for c in non_good:
                if c[(p - 1) % n] == L and c[p] == S and c[(p + 1) % n] == R:
                    new_c = list(c)
                    new_c[p] = out
                    nc = tuple(new_c)
                    if nc in good_set:
                        good_count += 1
                    elif nc in non_good_set:
                        ng_count += 1
            if out != S:
                if good_count > best_good or (good_count == best_good and ng_count < best_ng):
                    best_out = out
                    best_good = good_count
                    best_ng = ng_count
        comp[key] = best_out

    # Build transition tables
    tables = {}
    for p in range(n):
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        table = {}
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    table[(L, S, R)] = comp.get((p, L, S, R), S)
        tables[p] = table

    # Build fs list (list of callables, one per processor)
    fs = []
    for p in range(n):
        t = tables[p]
        fs.append(lambda L, S, R, _t=t: _t.get((L, S, R), S))

    # Verify
    result = verify_system(ms, fs)
    status = "VALID" if all([result['liveness'], result['mutual_exclusion'],
                             result['closure'], result['convergence']]) else "INVALID"

    print(f"\n  n={n}, ms={list(ms)}, product={product_val}")
    print(f"  System: {status}")
    print(f"  Good configs: {result.get('num_good', '?')}")

    # Extract the actual good cycle from the verified system
    if result.get('good_cycle'):
        actual_cycle = result['good_cycle']
        actual_movers = []
        for idx in range(len(actual_cycle)):
            c = actual_cycle[idx]
            c_next = actual_cycle[(idx + 1) % len(actual_cycle)]
            diffs = [j for j in range(n) if c[j] != c_next[j]]
            if len(diffs) == 1:
                actual_movers.append(diffs[0])
            else:
                actual_movers.append(-1)

        actual_type = classify_cycle(actual_movers, n) if -1 not in actual_movers else "unknown"
        print(f"  Verified cycle: length={len(actual_cycle)}, type={actual_type}")
        print(f"  Movers: {actual_movers}")

        violations = check_mnu(actual_cycle, n)
        if violations is not None:
            print(f"  MNU: {'OK' if len(violations) == 0 else f'FAIL ({len(violations)} violations)'}")
            if violations:
                for v in violations[:10]:
                    step, p, L, S_prime, R, num_matches, matches = v
                    print(f"    Step {step}: P{p} (L={L},S'={S_prime},R={R})"
                          f" → {num_matches} matches at {matches}")
    else:
        # Use the bounce cycle
        print(f"  Using bounce cycle: length={len(cycle)}")
        violations = check_mnu(cycle, n)
        if violations is not None:
            print(f"  MNU: {'OK' if len(violations) == 0 else f'FAIL ({len(violations)} violations)'}")

    # Check forced SCCs with complete system
    full_det = comp
    esc_fails, total = check_universal_escape(cycle, full_det, ms, n)
    if esc_fails is not None:
        print(f"  Escape (full system): {'OK' if len(esc_fails) == 0 else f'FAIL ({len(esc_fails)}/{total})'}")


# ============================================================
# Test 5: CRITICAL — Is the bounce cycle for CLB really non-sweep?
# ============================================================
print(f"\n{'=' * 70}")
print("TEST 5: BOUNCE vs SWEEP — STRUCTURAL COMPARISON")
print("=" * 70)

for n in [5, 7, 9]:
    ms, cycle, movers, _ = build_clb_system(n)
    if cycle is None:
        continue

    sweep = list(range(n)) * 2
    is_sweep = (movers == sweep)

    bounce_unit = list(range(n)) + list(range(n - 2, 0, -1))
    cycle_type = classify_cycle(movers, n)

    # Count firings per processor
    from collections import Counter
    firing_counts = Counter(movers)

    print(f"\n  n={n}, cycle length={len(cycle)}")
    print(f"  Is uniform sweep: {is_sweep}")
    print(f"  Type: {cycle_type}")
    print(f"  Firings per proc: {dict(sorted(firing_counts.items()))}")

    # Check waterfall structure
    # In a waterfall: g_j[i] = v_i if i < j <= n+i (mod schedule), else 0
    # For bounce cycle, the structure is different
    print(f"  First 5 configs: {cycle[:5]}")
    if len(cycle) > 10:
        print(f"  Mid configs:     {cycle[len(cycle)//2:len(cycle)//2+3]}")
    print(f"  Last 3 configs:  {cycle[-3:]}")

print(f"\n{'=' * 70}")
print("SUMMARY")
print("=" * 70)
print("""
Key findings:
- CLB bounce cycles are NON-sweep (movers go 0→n-1→1, not 0→n-1→0→n-1)
- If MNU holds for bounce cycles: MNU is NOT sweep-specific
- If MNU fails for bounce cycles: the shadow approach needs modification
  for non-sweep cycles (may need direct forced-SCC argument instead)
""")
