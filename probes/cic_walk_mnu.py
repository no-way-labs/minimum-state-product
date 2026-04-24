#!/usr/bin/env python3
"""CIC Exploration 5: MNU for general adjacent-mover walks.

Goal: prove that MNU holds for ALL good cycles, not just sweeps/bounces.

Key insight from Exploration 4: MNU = "monotone wavefront uniqueness".
Each processor sees a unique post-move (L, S', R) at each of its firings.

For this to fail, processor p would need to fire at two different steps
k1 and k2 with the SAME post-move (L, S', R). This requires:
1. Same L = c_{k1}[p-1] = c_{k2}[p-1]  (left neighbor same)
2. Same R = c_{k1}[p+1] = c_{k2}[p+1]  (right neighbor same)
3. Same S' = f_p(L, S1, R) = f_p(L, S2, R)  (same output, possibly S1 ≠ S2)

Between k1 and k2, the adjacent-mover lemma says the walk passes through
p's neighbors. So at least one of L or R must change. Unless the walk
goes away from p and RETURNS with the same neighbor states.

This script investigates:
1. Can L and R both return to their original values between two p-firings?
2. If yes, can f_p still map different inputs to the same output (creating MNU fail)?
3. What structural constraints prevent this?
"""

from itertools import product as iproduct
import sys
import os
sys.path.insert(0, os.path.dirname(__file__))


def enumerate_all_good_cycles(ms, n, max_cycles=100, max_time=30.0):
    """Enumerate ALL good cycles for a system by building complete transition functions.

    Strategy: for small state spaces, enumerate all possible deterministic
    single-mover transition functions and find which ones create good cycles.
    """
    import time
    from collections import defaultdict
    t0 = time.time()

    product_val = 1
    for m in ms:
        product_val *= m

    if product_val > 500:
        return []  # too large for exhaustive enum

    all_configs = list(iproduct(*[range(m) for m in ms]))
    cycles = []

    # Strategy: build good cycles directly via consistent walks
    # Start from each config, try all possible moves, track consistency
    for start_idx in range(min(len(all_configs), 50)):
        if time.time() - t0 > max_time:
            break

        start = all_configs[start_idx]
        # DFS with consistency tracking
        stack = [(start, [start], {}, [])]  # (config, path, det, movers)
        nodes = 0

        while stack and nodes < 200000:
            if time.time() - t0 > max_time:
                break
            nodes += 1

            config, path, det, movers = stack.pop()

            for p in range(n):
                for new_val in range(ms[p]):
                    if new_val == config[p]:
                        continue

                    # Check adjacent-mover
                    if movers:
                        last = movers[-1]
                        diff = min(abs(p - last), n - abs(p - last))
                        if diff > 1:
                            continue

                    # Check consistency
                    new_det = dict(det)
                    consistent = True

                    # Mover entry
                    L = config[(p - 1) % n]
                    S = config[p]
                    R = config[(p + 1) % n]
                    key_m = (p, L, S, R)
                    if key_m in new_det:
                        if new_det[key_m] != new_val:
                            consistent = False
                    else:
                        new_det[key_m] = new_val

                    # Non-mover entries (identity)
                    if consistent:
                        for i in range(n):
                            if i == p:
                                continue
                            Li = config[(i - 1) % n]
                            Si = config[i]
                            Ri = config[(i + 1) % n]
                            key_i = (i, Li, Si, Ri)
                            if key_i in new_det:
                                if new_det[key_i] != Si:
                                    consistent = False
                                    break
                            else:
                                new_det[key_i] = Si

                    if not consistent:
                        continue

                    new_config = list(config)
                    new_config[p] = new_val
                    new_config = tuple(new_config)

                    if new_config == start and len(path) >= 2 * n:
                        # Check mutual exclusion: each config in path
                        # has exactly 1 privileged processor
                        me_ok = True
                        for idx in range(len(path)):
                            c = path[idx]
                            priv = []
                            for i in range(n):
                                Li = c[(i - 1) % n]
                                Si = c[i]
                                Ri = c[(i + 1) % n]
                                ki = (i, Li, Si, Ri)
                                if ki in new_det and new_det[ki] != Si:
                                    priv.append(i)
                            if len(priv) != 1:
                                me_ok = False
                                break
                        if me_ok:
                            cycle = list(path)
                            new_movers = movers + [p]
                            # Deduplicate
                            cycle_tup = tuple(cycle)
                            if cycle_tup not in [tuple(c) for c, _, _ in cycles]:
                                cycles.append((cycle, new_movers, new_det))
                                if len(cycles) >= max_cycles:
                                    return cycles
                        continue

                    if new_config not in set(path) and len(path) < 4 * n:
                        stack.append((
                            new_config,
                            path + [new_config],
                            new_det,
                            movers + [p]
                        ))

    return cycles


def check_mnu(cycle, movers, n):
    """Check MNU for a cycle. Returns list of violations."""
    violations = []
    for step in range(len(cycle)):
        p = movers[step]
        gc_next = cycle[(step + 1) % len(cycle)]
        L = cycle[step][(p - 1) % n]
        S_prime = gc_next[p]
        R = cycle[step][(p + 1) % n]
        matches = sum(1 for gj in cycle
                      if gj[(p - 1) % n] == L
                      and gj[p] == S_prime
                      and gj[(p + 1) % n] == R)
        if matches != 1:
            violations.append((step, p, L, S_prime, R, matches))
    return violations


def classify_mover_pattern(movers, n):
    """Classify mover pattern type."""
    sweep = list(range(n))
    if len(movers) % n == 0:
        reps = len(movers) // n
        if movers == sweep * reps:
            return "sweep"

    bounce = list(range(n)) + list(range(n - 2, 0, -1))
    for r in range(1, 6):
        prefix = (bounce * r)[:len(movers)]
        if movers == prefix:
            return "bounce"

    # Check for self-loops
    has_self_loop = any(movers[i] == movers[i + 1]
                        for i in range(len(movers) - 1))
    # Check for direction changes
    dirs = []
    for i in range(len(movers) - 1):
        d = (movers[i + 1] - movers[i]) % n
        if d == 1:
            dirs.append('+')
        elif d == n - 1:
            dirs.append('-')
        elif d == 0:
            dirs.append('0')
    dir_str = ''.join(dirs)

    if has_self_loop:
        return f"walk_selfloop_L{len(movers)}"
    return f"walk_L{len(movers)}"


# ============================================================
# Test 1: Exhaustive search for non-sweep/non-bounce cycles
# ============================================================
print("=" * 70)
print("EXHAUSTIVE GOOD CYCLE SEARCH (small n)")
print("=" * 70)

# Use systems where valid good cycles exist
# n=3, ms=(3,3,3): product=27, Dijkstra Sol 3
# n=4, ms=(3,3,3,3): product=81
# n=3, ms=(2,3,2): product=12

test_systems = [
    (3, (2, 3, 2)),   # product 12
    (3, (3, 3, 3)),   # product 27
    (3, (2, 4, 3)),   # product 24
    (3, (2, 5, 2)),   # product 20
    (4, (2, 3, 3, 2)),  # product 36
    (4, (3, 3, 3, 3)),  # product 81
    (4, (2, 3, 2, 3)),  # product 36
    (4, (2, 4, 2, 3)),  # product 48
    (5, (2, 3, 3, 3, 2)),  # product 108 (CLB)
    (5, (3, 3, 3, 3, 3)),  # product 243 (Sol 3)
]

all_results = []

for n, ms in test_systems:
    product_val = 1
    for m in ms:
        product_val *= m

    print(f"\nn={n}, ms={list(ms)}, product={product_val}")

    cycles = enumerate_all_good_cycles(ms, n, max_cycles=50, max_time=15.0)
    print(f"  Found {len(cycles)} good cycles")

    sweep_count = 0
    bounce_count = 0
    other_count = 0
    mnu_ok = 0
    mnu_fail = 0

    for cycle, movers, det in cycles:
        ctype = classify_mover_pattern(movers, n)
        violations = check_mnu(cycle, movers, n)

        if 'sweep' in ctype:
            sweep_count += 1
        elif 'bounce' in ctype:
            bounce_count += 1
        else:
            other_count += 1

        if len(violations) == 0:
            mnu_ok += 1
        else:
            mnu_fail += 1
            if mnu_fail <= 3:
                print(f"    MNU FAIL: type={ctype}, L={len(cycle)}, "
                      f"movers={movers}")
                for v in violations[:3]:
                    step, p, L, S_prime, R, cnt = v
                    print(f"      Step {step}: P{p} (L={L},S'={S_prime},"
                          f"R={R}) → {cnt} matches")

        if 'walk' in ctype or other_count <= 3:
            if len(violations) == 0:
                print(f"    {ctype}: L={len(cycle)}, movers={movers}, "
                      f"MNU OK")

    print(f"  Types: {sweep_count} sweep, {bounce_count} bounce, "
          f"{other_count} other")
    print(f"  MNU: {mnu_ok} OK, {mnu_fail} FAIL")
    all_results.append((n, ms, len(cycles), sweep_count, bounce_count,
                         other_count, mnu_ok, mnu_fail))


# ============================================================
# Test 2: Theoretical analysis — when can MNU fail?
# ============================================================
print(f"\n{'=' * 70}")
print("THEORETICAL MNU FAILURE ANALYSIS")
print("=" * 70)

print("""
For MNU to fail at processor p (two firings with same post-move triple):
1. p fires at steps k1 and k2
2. Same (L, S', R) at both steps
3. L = c_{k1}[p-1] = c_{k2}[p-1]
4. R = c_{k1}[p+1] = c_{k2}[p+1]
5. S' = f_p(L, S1, R) = f_p(L, S2, R)  with S1 ≠ S2

Condition 3+4: Between k1 and k2, L and R must both return to original.
  → p-1 must fire an even number of times (for binary) or return to same state
  → p+1 must fire an even number of times (for binary) or return to same state

Condition 5: f_p maps different inputs to same output for same (L,R).
  → For binary p: f_p(L,0,R) = f_p(L,1,R). Both map to same output.
    One is identity (no privilege), one is privilege. But same output means
    f_p(L,0,R) = f_p(L,1,R) = v. Then for state v: no privilege.
    For state 1-v: privilege, fires to v.
    This means p fires ONCE from 1-v to v and never again (no more privilege
    at this (L,R)). So p can't fire twice with same (L,R) as binary!
  → For ternary p: f_p(L,0,R)=f_p(L,1,R)=v is possible.
    But both states 0 and 1 would need to be visited at p with same (L,R).
    The walk must reach state 0 at (L,R) and state 1 at (L,R) at position p.
""")

# Check: for binary p, can it fire twice with same (L,R)?
print("Binary processor MNU impossibility:")
print("  If p is binary and fires at k1 with (L, 0, R) → 1,")
print("  then f_p(L, 0, R) = 1 (privilege).")
print("  After firing, p has state 1. For p to fire again with same (L,R),")
print("  need f_p(L, 1, R) ≠ 1, i.e., f_p(L, 1, R) = 0.")
print("  This is the FORBIDDEN binary 2-cycle!")
print("  → Binary p can NEVER create an MNU violation.")
print()
print("  Conversely, if p fires at k1 with (L, 1, R) → 0,")
print("  for a second firing with same (L,R): need f_p(L, 0, R) ≠ 0,")
print("  i.e., f_p(L, 0, R) = 1. Again the forbidden binary 2-cycle!")
print()
print("THEOREM: For binary processor p, MNU ALWAYS holds.")
print("  (No good cycle can create an MNU violation at a binary proc.)")

# For ternary: check if MNU violations can occur
print("\nTernary processor MNU analysis:")
print("  For ternary p with f_p(L, S1, R) = f_p(L, S2, R) = v:")
print("  Need S1 ≠ S2, both map to same v under same (L,R).")
print("  This means at least 2 of the 3 states {0,1,2} map to v.")
print("  Example: f_p(L, 0, R) = 1, f_p(L, 1, R) = 1. Allowed.")
print("  But then state 1 has no privilege at (L,R): identity.")
print("  States 0 and 2 might both have privilege → maps to 1 and 1.")
print("  Both fire at different steps but produce same post-move (L,1,R).")
print()

# Can this actually happen in a valid good cycle?
# The walk must visit p at state 0 with (L,R) AND at state 2 with (L,R).
# Between these visits, L and R must return to same values.
print("For this to happen in a valid good cycle:")
print("  1. Walk visits p at state 0 with nbhd (L, 0, R)")
print("  2. p fires: state → f_p(L,0,R) = v")
print("  3. Walk continues, eventually returns to p at state S2 ≠ 0")
print("     with SAME nbhd (L, S2, R)")
print("  4. p fires: state → f_p(L,S2,R) = v (same output!)")
print("  5. MNU violated: config at step 2 has (L,v,R) at p,")
print("     AND config at step 4 also has (L,v,R) at p.")
print()
print("BUT: step 2 and step 4 produce DIFFERENT configs (since")
print("  other processors differ between the two firings).")
print("  So (L,v,R) appears at p in TWO different cycle configs.")
print("  This is the MNU violation.")
print()
print("QUESTION: Does this actually happen for any valid system?")
print("  Testing exhaustively at small n...")

# Count MNU violations at ternary procs specifically
print(f"\n{'=' * 70}")
print("MNU VIOLATIONS BY PROCESSOR TYPE")
print("=" * 70)

for n, ms, total, sw, bn, ot, ok, fail in all_results:
    if fail > 0:
        print(f"\nn={n}, ms={list(ms)}: {fail} cycles with MNU violations")
        cycles = enumerate_all_good_cycles(ms, n, max_cycles=50,
                                           max_time=15.0)
        for cycle, movers, det in cycles:
            violations = check_mnu(cycle, movers, n)
            if violations:
                for v in violations:
                    step, p, L, S_prime, R, cnt = v
                    proc_type = "binary" if ms[p] == 2 else (
                        "ternary" if ms[p] == 3 else f"m={ms[p]}")
                    print(f"  Violation at P{p} ({proc_type}): "
                          f"step {step}, (L={L},S'={S_prime},R={R})"
                          f" → {cnt} matches")

print(f"\n{'=' * 70}")
print("SUMMARY")
print("=" * 70)
for n, ms, total, sw, bn, ot, ok, fail in all_results:
    prod = 1
    for m in ms:
        prod *= m
    print(f"  n={n} ms={list(ms):20s} prod={prod:5d}  "
          f"cycles={total:3d}  "
          f"sw={sw} bn={bn} ot={ot}  MNU: {ok} OK {fail} FAIL")
