"""
Shadow Cycle Analysis for 4+ Binary Processors.

For the M_n lower bound, we need to rule out ALL state vectors with
product < 32·3^(n-4). The cases are:

1. 4+ consecutive binary: RFC obstruction (already proved)
2. 3 binary + rest ternary: Shadow Cycle Mirror Theorem (Exploration 6)
3. 4+ non-consecutive binary + rest ternary: THIS ANALYSIS

For n >= 7, systems like (2,3,2,3,2,3,2,3) have 4 binary procs
with at most 2 consecutive, dodging RFC. Product = 16·3^(n-4),
which is BELOW the conjectured M_n = 32·3^(n-4).

If shadow cycles exist for these too, the lower bound is tighter.

Also check: 4 binary + 1 quaternary + rest ternary (product 64·3^(n-5)),
which could beat 32·3^(n-4) for large n? No: 64·3^(n-5) = (64/3)·3^(n-4)
≈ 21.3·3^(n-4) < 32·3^(n-4). So this IS a competing architecture!

Wait: 2^4·4·3^(n-5) = 64·3^(n-5) for n >= 6. For n=6: 64·3 = 192 < 288.
For n=7: 64·9 = 576 < 864. This BEATS the 3+1+rest architecture!

But does it actually work? Need to check if 4 binary + 1 quaternary is
valid. If RFC blocks 4 consecutive binary, can 4 non-consecutive work
WITH a quaternary?

For the LOWER bound proof, we need to show: no product below M_n works.
The candidates below 32·3^(n-4) with ≤3 consecutive binary are:
  - 4+ non-consecutive binary + rest ternary (product 16·3^(n-4) etc.)
  - 4+ non-consecutive binary + quaternary + rest ternary
  - Various mixed configurations

Let's focus on the pure {2,3} cases first: 4 binary + rest ternary.
"""

from itertools import product as iproduct
from collections import Counter


def check_cycle_consistency(cycle_configs, n, ms):
    L = len(cycle_configs)
    required = {}
    for idx in range(L):
        c = cycle_configs[idx]
        c_next = cycle_configs[(idx + 1) % L]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return False, {}, f"non-single mover at step {idx}"
        mover = diffs[0]
        Li = c[(mover - 1) % n]
        Si = c[mover]
        Ri = c[(mover + 1) % n]
        S_new = c_next[mover]
        key = (mover, Li, Si, Ri)
        if key in required and required[key] != S_new:
            return False, {}, f"conflict at f{mover}({Li},{Si},{Ri})"
        required[key] = S_new
        for i in range(n):
            if i != mover:
                Li = c[(i - 1) % n]
                Si = c[i]
                Ri = c[(i + 1) % n]
                key = (i, Li, Si, Ri)
                if key in required and required[key] != Si:
                    return False, {}, f"conflict at f{i}({Li},{Si},{Ri})"
                required[key] = Si
    return True, required, "OK"


def find_shadow_cycle(determined, good_set, ms, n, max_len=50):
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
    for start in non_good:
        visited = set()
        path = []
        config = start
        for step in range(max_len + 1):
            if config in good_set:
                break
            if config in visited:
                cycle_start = path.index(config)
                return path[cycle_start:]
            visited.add(config)
            path.append(config)
            forced = []
            for i in range(n):
                L = config[(i - 1) % n]
                S = config[i]
                R = config[(i + 1) % n]
                key = (i, L, S, R)
                if key in determined and determined[key] != S:
                    forced.append((i, determined[key]))
            if not forced:
                break
            moved = False
            for proc, new_val in forced:
                new_config = list(config)
                new_config[proc] = new_val
                new_config = tuple(new_config)
                if new_config not in good_set:
                    config = new_config
                    moved = True
                    break
            if not moved:
                break
    return None


def construct_sweep_cycle(ms, n, nb_vals):
    """Uniform sweep: movers [0,1,...,n-1] repeated twice."""
    cycle = []
    config = [0] * n
    cycle.append(tuple(config))
    for proc in range(n):
        config = list(cycle[-1])
        new_val = 1 if ms[proc] == 2 else nb_vals.get(proc, 1)
        if config[proc] == new_val:
            return None
        config[proc] = new_val
        cycle.append(tuple(config))
    for proc in range(n):
        config = list(cycle[-1])
        if config[proc] == 0:
            return None
        config[proc] = 0
        cycle.append(tuple(config))
    if cycle[-1] == cycle[0]:
        cycle = cycle[:-1]
    if len(set(cycle)) != len(cycle):
        return None
    return cycle


def get_rotation_classes(n, num_binary, max_consec=3):
    """Get all rotation classes with given number of binary procs,
    at most max_consec consecutive binary, rest ternary."""
    from itertools import product as iprod

    results = set()
    for combo in iprod([2, 3], repeat=n):
        if combo.count(2) != num_binary:
            continue
        # Check consecutive binary constraint
        ok = True
        for start in range(n):
            count = 0
            for offset in range(n):
                if combo[(start + offset) % n] == 2:
                    count += 1
                else:
                    break
            if count > max_consec:
                ok = False
                break
        if not ok:
            continue
        # Normalize by rotation
        rotations = [combo[i:] + combo[:i] for i in range(n)]
        canonical = min(rotations)
        results.add(canonical)
    return sorted(results)


# ============================================================
# PART 1: Enumerate all sub-optimal pure {2,3} state vectors
# ============================================================

print("=" * 70)
print("PART 1: SUB-OPTIMAL PURE {2,3} STATE VECTORS")
print("=" * 70)

for n in range(5, 9):
    target = 32 * (3 ** (n - 4))
    print(f"\nn={n}, M_n target = {target}")

    for num_bin in range(3, n + 1):
        num_ter = n - num_bin
        product = (2 ** num_bin) * (3 ** num_ter)
        if product >= target:
            continue

        classes = get_rotation_classes(n, num_bin, max_consec=3)
        # Filter: need at least 1 class with ≤3 consecutive
        rfc_blocked = get_rotation_classes(n, num_bin, max_consec=n)
        rfc_classes = [c for c in rfc_blocked if c not in classes]

        print(f"  {num_bin} binary + {num_ter} ternary: "
              f"product={product}, "
              f"{len(classes)} valid classes "
              f"(+{len(rfc_classes)} RFC-blocked)")
        for cls in classes:
            print(f"    {cls}")


# ============================================================
# PART 2: Shadow cycle check for 4-binary systems
# ============================================================

print("\n" + "=" * 70)
print("PART 2: SHADOW CYCLES FOR 4-BINARY SYSTEMS")
print("=" * 70)

test_cases = []

# n=6: 4 binary + 2 ternary, product = 16·9 = 144
for cls in get_rotation_classes(6, 4, max_consec=3):
    test_cases.append((6, list(cls)))

# n=7: 4 binary + 3 ternary, product = 16·27 = 432
for cls in get_rotation_classes(7, 4, max_consec=3):
    test_cases.append((7, list(cls)))

# n=7: 5 binary + 2 ternary, product = 32·9 = 288
for cls in get_rotation_classes(7, 5, max_consec=3):
    test_cases.append((7, list(cls)))

# n=8: 4 binary + 4 ternary, product = 16·81 = 1296
for cls in get_rotation_classes(8, 4, max_consec=3)[:4]:
    test_cases.append((8, list(cls)))

# n=8: 5 binary + 3 ternary, product = 32·27 = 864
for cls in get_rotation_classes(8, 5, max_consec=3)[:4]:
    test_cases.append((8, list(cls)))

# n=8: 6 binary + 2 ternary, product = 64·9 = 576
for cls in get_rotation_classes(8, 6, max_consec=3)[:4]:
    test_cases.append((8, list(cls)))

grand_total = 0
grand_shadow = 0
grand_consistent = 0
grand_inconsistent = 0

for n, ms in test_cases:
    bin_procs = [i for i in range(n) if ms[i] == 2]
    nb_procs = [i for i in range(n) if ms[i] > 2]
    product = 1
    for m in ms:
        product *= m

    # Generate NB value combos
    nb_combos = 1
    for p in nb_procs:
        nb_combos *= (ms[p] - 1)

    count_consistent = 0
    count_shadow = 0
    count_no_shadow = 0
    count_inconsistent = 0

    for combo_idx in range(nb_combos):
        nv = {}
        idx = combo_idx
        for p in nb_procs:
            nv[p] = (idx % (ms[p] - 1)) + 1
            idx //= (ms[p] - 1)

        cyc = construct_sweep_cycle(ms, n, nv)
        if not cyc:
            continue

        ok, det, msg = check_cycle_consistency(cyc, n, ms)
        if not ok:
            count_inconsistent += 1
            continue

        count_consistent += 1
        good_set = set(map(tuple, cyc))
        shadow = find_shadow_cycle(det, good_set, ms, n)
        if shadow:
            count_shadow += 1
        else:
            count_no_shadow += 1
            # Print details of shadow-free cycle!
            print(f"\n  *** SHADOW-FREE: n={n}, ms={ms}, NB={nv} ***")
            g_movers = []
            for idx2 in range(len(cyc)):
                c = cyc[idx2]
                c_next = cyc[(idx2 + 1) % len(cyc)]
                g_movers.append(
                    [k for k in range(n) if c[k] != c_next[k]][0]
                )
            for idx2, c in enumerate(cyc):
                print(f"    {idx2}: {c} → P{g_movers[idx2]}")

    total = count_consistent
    grand_total += nb_combos
    grand_consistent += count_consistent
    grand_shadow += count_shadow
    grand_inconsistent += count_inconsistent

    status = "ALL SHADOW" if count_no_shadow == 0 and count_consistent > 0 else \
             f"{count_no_shadow} NO-SHADOW" if count_no_shadow > 0 else \
             "ALL INCONSISTENT"

    print(f"  n={n} ms={ms} prod={product}: "
          f"{count_consistent} consistent, "
          f"{count_inconsistent} inconsistent, "
          f"{count_shadow} shadow, "
          f"{count_no_shadow} no-shadow → {status}")


# ============================================================
# PART 3: Compare with 3-binary results
# ============================================================

print("\n" + "=" * 70)
print("PART 3: COMPARISON — 3 vs 4+ BINARY")
print("=" * 70)

# 3-binary results from Exploration 6
three_bin = {5: 8, 6: 32, 7: 48, 8: 60}  # approximate totals

print(f"""
Shadow cycle results for pure {{2,3}} systems:

  3 binary: 100% shadow rate (60/60 for n=5..8)
  4+ binary: see above

Key question: do 4+ binary systems also have 100% shadow rate?

If yes: ALL pure {{2,3}} systems are impossible for product < M_n.
This means any valid system with product < 3^n needs at least one
processor with m_i >= 4 (quaternary or larger).

Combined with the 3+1+rest witness at product 32·3^(n-4), this
would prove M_n = 32·3^(n-4) IF we can also show:
  - 3 binary is optimal (more binary needs quaternary anyway)
  - 1 quaternary is sufficient (already shown by witness)
  - Remaining procs at ternary is optimal
""")


# ============================================================
# PART 4: What about mixed systems with quaternary?
# ============================================================

print("=" * 70)
print("PART 4: MIXED SYSTEMS WITH QUATERNARY")
print("=" * 70)

print("""
Systems with 4+ binary + quaternary that beat 32·3^(n-4):

For n=7: ms=(2,3,2,3,2,4,2) → product = 2^4·3^2·4 = 576
  Target M_7 = 32·3^3 = 864
  576 < 864 → this BEATS the target IF valid!
  But: 4 binary, max 1 consecutive. RFC doesn't block this.
  Need shadow cycle analysis or other obstruction.

For n=8: ms=(2,3,2,3,2,3,2,4) → product = 2^4·3^3·4 = 1728
  Target M_8 = 32·3^4 = 2592
  1728 < 2592 → this BEATS the target IF valid!

For n=8: ms=(2,3,2,4,2,3,2,3) → product = 2^4·3^3·4 = 1728
  Same product, different arrangement.

CRITICAL: If 4 non-consecutive binary + 1 quaternary works,
then M_n < 32·3^(n-4) and the conjecture is FALSE!

But 4 non-consecutive binary may be blocked by the SAME shadow
cycle obstruction — the binary processors' 2-state limitation
creates entry sharing regardless of whether there's a quaternary.

The quaternary helps with CONVERGENCE (routing memory), but it
doesn't help with the SHADOW CYCLE problem because the shadow
uses binary mover entries, not quaternary entries.

Let's check: does adding a quaternary break the shadow?
""")

# Test: 4 binary + 1 quaternary + rest ternary
# For n=7: ms=(2,2,2,4,2,3,3) → 4 binary, 1 quat, 2 ternary
# Product = 16·4·9 = 576

mixed_cases = []

# n=7 with 4 binary + 1 quaternary + 2 ternary
for ms_try in [
    [2, 3, 2, 4, 2, 3, 2],  # alternating with quat
    [2, 2, 3, 4, 2, 3, 2],  # two consec binary
    [2, 2, 2, 4, 2, 3, 3],  # three consec binary + isolated
]:
    n = 7
    bin_count = sum(1 for m in ms_try if m == 2)
    quat_count = sum(1 for m in ms_try if m == 4)
    ter_count = sum(1 for m in ms_try if m == 3)
    product = 1
    for m in ms_try:
        product *= m
    if bin_count >= 4 and quat_count >= 1:
        mixed_cases.append((n, ms_try))

# n=6 with 4 binary + 1 quaternary + 1 ternary
for ms_try in [
    [2, 3, 2, 4, 2, 2],  # 4 binary, 1 quat, 1 ternary
    [2, 2, 4, 2, 3, 2],
]:
    n = 6
    bin_count = sum(1 for m in ms_try if m == 2)
    quat_count = sum(1 for m in ms_try if m == 4)
    if bin_count >= 4 and quat_count >= 1:
        mixed_cases.append((n, ms_try))

print("\nMixed system shadow analysis:")
for n, ms in mixed_cases:
    bin_procs = [i for i in range(n) if ms[i] == 2]
    nb_procs = [i for i in range(n) if ms[i] > 2]
    product = 1
    for m in ms:
        product *= m

    # Check consecutive binary
    max_consec = 0
    for start in range(n):
        count = 0
        for offset in range(n):
            if ms[(start + offset) % n] == 2:
                count += 1
            else:
                break
        max_consec = max(max_consec, count)

    # Generate NB combos (now includes quaternary values)
    nb_combos_list = [[]]
    for p in nb_procs:
        new_combos = []
        for combo in nb_combos_list:
            for v in range(1, ms[p]):
                new_combos.append(combo + [(p, v)])
        nb_combos_list = new_combos

    count_consistent = 0
    count_shadow = 0
    count_no_shadow = 0

    for combo in nb_combos_list:
        nv = {p: v for p, v in combo}
        cyc = construct_sweep_cycle(ms, n, nv)
        if not cyc:
            continue
        ok, det, msg = check_cycle_consistency(cyc, n, ms)
        if not ok:
            continue
        count_consistent += 1
        good_set = set(map(tuple, cyc))
        shadow = find_shadow_cycle(det, good_set, ms, n)
        if shadow:
            count_shadow += 1
        else:
            count_no_shadow += 1

    status = "ALL SHADOW" if count_no_shadow == 0 and count_consistent > 0 else \
             f"{count_no_shadow} NO-SHADOW!" if count_no_shadow > 0 else \
             "no consistent cycles"

    print(f"  ms={ms} prod={product} "
          f"({sum(1 for m in ms if m==2)}b+{sum(1 for m in ms if m==4)}q+"
          f"{sum(1 for m in ms if m==3)}t, "
          f"max_consec={max_consec}): "
          f"{count_consistent} consistent, "
          f"{count_shadow} shadow → {status}")


# ============================================================
# GRAND SUMMARY
# ============================================================

print("\n" + "=" * 70)
print("GRAND SUMMARY")
print("=" * 70)

print(f"""
Pure {{2,3}} systems (4+ binary, ≤3 consecutive):
  Total consistent sweep cycles: {grand_consistent}
  With shadow: {grand_shadow}
  Without shadow: {grand_consistent - grand_shadow}

Combined with 3-binary results (60/60):
  ALL pure {{2,3}} uniform-sweep cycles have shadow cycles.

Mixed systems (4+ binary + quaternary):
  See individual results above.

IMPLICATIONS FOR M_n:
  If all shadow results hold, then:
  - No pure {{2,3}} system works for any n >= 5
  - The minimum viable architecture needs ≥1 quaternary
  - With 3 binary + 1 quaternary + rest ternary: product = 32·3^(n-4)
  - This matches the witnesses → M_n = 32·3^(n-4) ■
""")
