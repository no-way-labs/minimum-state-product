"""
Local-type classification for the Escape Lemma.

Goal: Show that whether a non-good config escapes depends only on a
bounded local neighborhood around the binary block, giving a finite
n-independent classification.

Key insight from analysis:
  - Binary forced moves ALWAYS escape (flipping b at c lands in C only if c in C)
  - So escape can only fail if ALL forced privs are non-binary
  - We classify configs by local type and check this never happens

Local type = (b0, b1, b2, s3, s_{n-1}, binary_priv_mask)
where b0,b1,b2 are binary states, s3 is proc 3's state, s_{n-1} is proc n-1's state,
and binary_priv_mask indicates which binary procs are forced-privileged.
"""

from itertools import product as iproduct


def build_uniform_sweep(n, ms, nb_vals):
    """Build uniform sweep cycle with given NB values."""
    config = [0] * n
    cycle = [tuple(config)]
    for proc in range(n):
        config = list(cycle[-1])
        config[proc] = 1 if ms[proc] == 2 else nb_vals[proc]
        cycle.append(tuple(config))
    for proc in range(n):
        config = list(cycle[-1])
        config[proc] = 0
        cycle.append(tuple(config))
    if cycle[-1] == cycle[0]:
        cycle = cycle[:-1]
    return cycle


def get_determined(cycle, n):
    """Get all determined entries from cycle."""
    det = {}
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return None
        mover = diffs[0]
        # Mover entry
        L, S, R = c[(mover-1)%n], c[mover], c[(mover+1)%n]
        det[(mover, L, S, R)] = c_next[mover]
        # Non-mover entries
        for i in range(n):
            if i != mover:
                L, S, R = c[(i-1)%n], c[i], c[(i+1)%n]
                det[(i, L, S, R)] = S
    return det


def get_forced_privileged(c, det, n):
    """Return list of (proc, new_val) for forced-privileged procs."""
    priv = []
    for i in range(n):
        L, S, R = c[(i-1)%n], c[i], c[(i+1)%n]
        key = (i, L, S, R)
        if key in det and det[key] != S:
            priv.append((i, det[key]))
    return priv


# =================================================================
# PART 1: Prove binary forced moves always escape
# =================================================================
print("=" * 70)
print("PART 1: BINARY FORCED MOVES ALWAYS ESCAPE")
print("=" * 70)
print()

for n in [5, 6, 7, 8]:
    if n == 5:
        ms_list = [(2,2,2,3,3), (2,2,3,2,3)]
    elif n == 6:
        ms_list = [(2,2,2,3,3,3), (2,3,2,3,2,3)]
    elif n == 7:
        ms_list = [(2,2,2,3,3,3,3), (2,3,2,3,2,3,3)]
    else:
        ms_list = [(2,2,2,3,3,3,3,3)]

    for ms in ms_list:
        ms = list(ms)
        bin_procs = [i for i in range(n) if ms[i] == 2]
        nb_procs = [i for i in range(n) if ms[i] > 2]
        nb_combos = list(iproduct(*[range(1, ms[p]) for p in nb_procs]))

        total_binary_forced = 0
        binary_forced_enters_C = 0

        for combo in nb_combos:
            nb_vals = {p: combo[i] for i, p in enumerate(nb_procs)}
            for p in bin_procs:
                nb_vals[p] = 1
            cycle = build_uniform_sweep(n, ms, nb_vals)
            det = get_determined(cycle, n)
            if det is None:
                continue
            good_set = set(cycle)

            for c in iproduct(*[range(m) for m in ms]):
                if c in good_set:
                    continue
                priv = get_forced_privileged(c, det, n)
                for proc, new_val in priv:
                    if ms[proc] == 2:  # binary proc
                        total_binary_forced += 1
                        new_c = list(c)
                        new_c[proc] = new_val
                        if tuple(new_c) in good_set:
                            binary_forced_enters_C += 1
                            print(f"  COUNTEREXAMPLE! n={n} ms={ms} c={c} proc={proc}")

        print(f"  n={n} ms={ms}: {total_binary_forced} binary forced moves, "
              f"{binary_forced_enters_C} enter C")

print()


# =================================================================
# PART 2: Classify local types of configs with ONLY non-binary privs
# =================================================================
print("=" * 70)
print("PART 2: CONFIGS WITH ONLY NON-BINARY FORCED PRIVILEGE")
print("=" * 70)
print()
print("These are the ONLY configs where escape could potentially fail.")
print("We show they don't exist (every forced-priv config has a binary priv).")
print()

for n in [5, 6, 7, 8]:
    if n == 5:
        ms_list = [(2,2,2,3,3), (2,2,3,2,3)]
    elif n == 6:
        ms_list = [(2,2,2,3,3,3), (2,3,2,3,2,3)]
    elif n == 7:
        ms_list = [(2,2,2,3,3,3,3), (2,3,2,3,2,3,3)]
    else:
        ms_list = [(2,2,2,3,3,3,3,3)]

    for ms in ms_list:
        ms = list(ms)
        bin_procs = [i for i in range(n) if ms[i] == 2]
        nb_procs = [i for i in range(n) if ms[i] > 2]
        nb_combos = list(iproduct(*[range(1, ms[p]) for p in nb_procs]))

        total_forced_configs = 0
        only_nb_priv = 0
        only_nb_examples = []

        for combo in nb_combos:
            nb_vals = {p: combo[i] for i, p in enumerate(nb_procs)}
            for p in bin_procs:
                nb_vals[p] = 1
            cycle = build_uniform_sweep(n, ms, nb_vals)
            det = get_determined(cycle, n)
            if det is None:
                continue
            good_set = set(cycle)

            for c in iproduct(*[range(m) for m in ms]):
                if c in good_set:
                    continue
                priv = get_forced_privileged(c, det, n)
                if not priv:
                    continue
                total_forced_configs += 1
                has_binary = any(ms[p] == 2 for p, _ in priv)
                if not has_binary:
                    only_nb_priv += 1
                    if len(only_nb_examples) < 3:
                        only_nb_examples.append((c, priv, combo))

        print(f"  n={n} ms={ms}: {total_forced_configs} forced configs, "
              f"{only_nb_priv} with ONLY non-binary privs")
        for ex in only_nb_examples:
            print(f"    Example: c={ex[0]}, privs={ex[1]}, nb_vals={ex[2]}")

print()


# =================================================================
# PART 3: For configs with only NB privs, check escape anyway
# =================================================================
print("=" * 70)
print("PART 3: ESCAPE CHECK FOR NON-BINARY-ONLY PRIV CONFIGS")
print("=" * 70)
print()

for n in [5, 6, 7, 8]:
    if n == 5:
        ms_list = [(2,2,2,3,3), (2,2,3,2,3)]
    elif n == 6:
        ms_list = [(2,2,2,3,3,3), (2,3,2,3,2,3)]
    elif n == 7:
        ms_list = [(2,2,2,3,3,3,3), (2,3,2,3,2,3,3)]
    else:
        ms_list = [(2,2,2,3,3,3,3,3)]

    for ms in ms_list:
        ms = list(ms)
        bin_procs = [i for i in range(n) if ms[i] == 2]
        nb_procs = [i for i in range(n) if ms[i] > 2]
        nb_combos = list(iproduct(*[range(1, ms[p]) for p in nb_procs]))

        nb_only_total = 0
        nb_only_escape = 0
        nb_only_no_escape = 0

        for combo in nb_combos:
            nb_vals = {p: combo[i] for i, p in enumerate(nb_procs)}
            for p in bin_procs:
                nb_vals[p] = 1
            cycle = build_uniform_sweep(n, ms, nb_vals)
            det = get_determined(cycle, n)
            if det is None:
                continue
            good_set = set(cycle)

            for c in iproduct(*[range(m) for m in ms]):
                if c in good_set:
                    continue
                priv = get_forced_privileged(c, det, n)
                if not priv:
                    continue
                has_binary = any(ms[p] == 2 for p, _ in priv)
                if has_binary:
                    continue  # already handled by Part 1

                nb_only_total += 1
                has_escape = False
                for proc, new_val in priv:
                    new_c = list(c)
                    new_c[proc] = new_val
                    if tuple(new_c) not in good_set:
                        has_escape = True
                        break
                if has_escape:
                    nb_only_escape += 1
                else:
                    nb_only_no_escape += 1
                    print(f"  NO ESCAPE! n={n} ms={ms} c={c} privs={priv}")

        if nb_only_total > 0:
            print(f"  n={n} ms={ms}: {nb_only_total} NB-only configs, "
                  f"{nb_only_escape} escape, {nb_only_no_escape} no escape")
        else:
            print(f"  n={n} ms={ms}: 0 NB-only configs (all have binary priv)")

print()


# =================================================================
# PART 4: Local type classification — what determines escape?
# =================================================================
print("=" * 70)
print("PART 4: LOCAL TYPE CLASSIFICATION")
print("=" * 70)
print()
print("For each forced-priv config, record local type:")
print("  (b0, b1, b2, s3, s_{n-1}, which_binary_priv)")
print("Check if type set is the same across n values.")
print()

type_sets = {}
for n in [5, 6, 7, 8]:
    if n == 5:
        ms_list = [(2,2,2,3,3)]
    elif n == 6:
        ms_list = [(2,2,2,3,3,3)]
    elif n == 7:
        ms_list = [(2,2,2,3,3,3,3)]
    else:
        ms_list = [(2,2,2,3,3,3,3,3)]

    for ms in ms_list:
        ms = list(ms)
        bin_procs = [i for i in range(n) if ms[i] == 2]
        nb_procs = [i for i in range(n) if ms[i] > 2]

        # Use v_i = 1 for all NB procs (canonical case)
        nb_vals = {p: 1 for p in range(n)}
        cycle = build_uniform_sweep(n, ms, nb_vals)
        det = get_determined(cycle, n)
        if det is None:
            continue
        good_set = set(cycle)

        types = set()
        for c in iproduct(*[range(m) for m in ms]):
            if c in good_set:
                continue
            priv = get_forced_privileged(c, det, n)
            if not priv:
                continue

            # Local type: binary states + boundary NB states + which procs are priv
            b0, b1, b2 = c[0], c[1], c[2]
            s3 = c[3]          # first NB proc
            sn1 = c[n-1]       # last NB proc (neighbor of proc 0)

            # Which binary procs are privileged
            bin_priv = tuple(1 if any(p == bp for p, _ in priv) else 0
                             for bp in bin_procs)

            # Interior pattern: are interior NB procs (4..n-2) all 0, all 1, or mixed?
            if n > 5:
                interior = tuple(c[i] for i in range(4, n-1))
                int_all_0 = all(v == 0 for v in interior)
                int_all_v = all(v == 1 for v in interior)  # v_i = 1 for canonical
                if int_all_0:
                    int_class = "all0"
                elif int_all_v:
                    int_allv = "allv"
                    int_class = "allv"
                else:
                    int_class = "mixed"
            else:
                int_class = "n/a"

            local_type = (b0, b1, b2, s3, sn1, bin_priv, int_class)
            types.add(local_type)

        type_sets[n] = types
        print(f"  n={n} ms={ms}: {len(types)} distinct local types")

# Show the types for n=5 (smallest)
print()
print("  Types at n=5:")
for t in sorted(type_sets.get(5, [])):
    print(f"    {t}")

# Check which types appear at n=5 but not n=6, etc.
if 5 in type_sets and 6 in type_sets:
    # Compare on (b0,b1,b2,s3,sn1,bin_priv) ignoring interior
    def strip_interior(types):
        return {t[:6] for t in types}

    t5 = strip_interior(type_sets[5])
    t6 = strip_interior(type_sets[6])
    t7 = strip_interior(type_sets.get(7, set()))
    t8 = strip_interior(type_sets.get(8, set()))

    print()
    print(f"  Boundary types (ignoring interior): n=5:{len(t5)}, n=6:{len(t6)}, "
          f"n=7:{len(t7)}, n=8:{len(t8)}")
    print(f"  n=5 ⊆ n=6: {t5 <= t6}")
    print(f"  n=6 ⊆ n=7: {t6 <= t7}")
    print(f"  n=7 ⊆ n=8: {t7 <= t8}")
    print(f"  n=5 = n=6: {t5 == t6}")
    common = t5 & t6 & t7 & t8
    print(f"  Common across all n: {len(common)} types")
    print(f"  Types in ALL n: {sorted(common)}")

print()
print("=" * 70)
print("SUMMARY")
print("=" * 70)
