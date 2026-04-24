"""
Analytic proof of Shadow Cycle Closure for all n.

Goal: Derive closed-form shadow configs s_0,...,s_{2n-1} and prove
s_{2n} = s_0, all s_i distinct, each step uses a mover entry from C.

Step 1: Extract shadow configs for n=5..10 and find the pattern.
Step 2: Verify the closed-form formula.
Step 3: Prove closure analytically.
"""

from itertools import product as iproduct


def build_uniform_sweep(n, ms, nb_vals):
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
    det = {}
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return None
        mover = diffs[0]
        L, S, R = c[(mover-1)%n], c[mover], c[(mover+1)%n]
        det[(mover, L, S, R)] = c_next[mover]
        for i in range(n):
            if i != mover:
                L, S, R = c[(i-1)%n], c[i], c[(i+1)%n]
                det[(i, L, S, R)] = S
    return det


def find_shadow_cycle(cycle, det, n, ms):
    """Find shadow cycle by following forced moves outside C."""
    good_set = set(cycle)
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]

    for start in non_good:
        visited = {}
        path = []
        c = start
        valid = True
        for step in range(4 * n + 10):
            if c in good_set:
                valid = False
                break
            if c in visited:
                shadow = path[visited[c]:]
                return shadow
            visited[c] = len(path)
            path.append(c)

            # Find forced-privileged procs
            priv = []
            for i in range(n):
                L, S, R = c[(i-1)%n], c[i], c[(i+1)%n]
                key = (i, L, S, R)
                if key in det and det[key] != S:
                    priv.append((i, det[key]))

            if not priv:
                valid = False
                break

            # Pick first forced move outside C
            moved = False
            for proc, new_val in priv:
                new_c = list(c)
                new_c[proc] = new_val
                new_c = tuple(new_c)
                if new_c not in good_set:
                    c = new_c
                    moved = True
                    break
            if not moved:
                valid = False
                break

        if not valid:
            continue

    return None


def sigma(k, n):
    """Shadow permutation."""
    if k == 0:
        return n - 4
    elif k == 1:
        return n - 1
    elif k == 2:
        return 0
    elif 3 <= k <= n - 3:
        return k - 2
    elif k == n - 2:
        return n - 2
    elif k == n - 1:
        return n - 3
    return None


# =================================================================
# PART 1: Extract shadow configs and identify pattern
# =================================================================
print("=" * 70)
print("PART 1: SHADOW CONFIG EXTRACTION")
print("=" * 70)
print()

for n in [5, 6, 7, 8, 9, 10]:
    ms = [2, 2, 2] + [3] * (n - 3)
    v = 1  # canonical NB value
    nb_vals = {p: v for p in range(n)}
    for p in range(3):
        nb_vals[p] = 1

    cycle = build_uniform_sweep(n, ms, nb_vals)
    det = get_determined(cycle, n)
    good_set = set(cycle)

    # Find shadow
    shadow = find_shadow_cycle(cycle, det, n, ms)
    if not shadow:
        print(f"  n={n}: NO SHADOW FOUND")
        continue

    # Get shadow movers
    shadow_movers = []
    for idx in range(len(shadow)):
        sc = shadow[idx]
        sc_next = shadow[(idx + 1) % len(shadow)]
        diffs = [k for k in range(n) if sc[k] != sc_next[k]]
        if len(diffs) == 1:
            shadow_movers.append(diffs[0])
        else:
            shadow_movers.append(-1)

    # Good cycle movers
    good_movers = []
    for idx in range(len(cycle)):
        gc = cycle[idx]
        gc_next = cycle[(idx + 1) % len(cycle)]
        good_movers.append([k for k in range(n) if gc[k] != gc_next[k]][0])

    print(f"  n={n}, shadow length={len(shadow)}:")
    print(f"    Good movers:   {good_movers}")
    print(f"    Shadow movers: {shadow_movers}")
    print(f"    σ(good):       {[sigma(m, n) for m in good_movers]}")
    print()

    # Print shadow configs with comparison to good configs
    print(f"    Step | Good config{' ' * (n-3)} | Shadow config{' ' * (n-3)} | G.mover | S.mover | σ(G.m)")
    print(f"    {'—' * (50 + 2*n)}")
    for idx in range(len(cycle)):
        gc = cycle[idx]
        if idx < len(shadow):
            sc = shadow[idx]
            sm = shadow_movers[idx] if idx < len(shadow_movers) else '?'
        else:
            sc = '?'
            sm = '?'
        gm = good_movers[idx]
        sg = sigma(gm, n)
        print(f"    {idx:4d} | {gc} | {sc} | {gm:7d} | {sm!s:7s} | {sg}")
    print()


# =================================================================
# PART 2: Analyze shadow config structure
# =================================================================
print("=" * 70)
print("PART 2: SHADOW CONFIG STRUCTURE ANALYSIS")
print("=" * 70)
print()

for n in [5, 6, 7, 8]:
    ms = [2, 2, 2] + [3] * (n - 3)
    nb_vals = {p: 1 for p in range(n)}
    for p in range(3):
        nb_vals[p] = 1

    cycle = build_uniform_sweep(n, ms, nb_vals)
    det = get_determined(cycle, n)
    shadow = find_shadow_cycle(cycle, det, n, ms)
    if not shadow:
        continue

    print(f"  n={n}:")
    print(f"    Good cycle configs:")
    for idx, gc in enumerate(cycle):
        print(f"      g_{idx:2d} = {gc}")
    print(f"    Shadow cycle configs:")
    for idx, sc in enumerate(shadow):
        print(f"      s_{idx:2d} = {sc}")

    # For each shadow config, express as: which positions differ from
    # the "all zeros" or "all ones" state
    print(f"    Shadow config analysis (position-by-position):")
    print(f"      Step | ", end="")
    for p in range(n):
        print(f"  P{p}", end="")
    print()
    for idx, sc in enumerate(shadow):
        gc = cycle[idx]
        print(f"      {idx:4d} | ", end="")
        for p in range(n):
            if sc[p] == gc[p]:
                print(f"  = ", end="")
            else:
                print(f" {sc[p]}≠{gc[p]}", end="")
        print()
    print()


# =================================================================
# PART 3: Derive shadow config formula
# =================================================================
print("=" * 70)
print("PART 3: SHADOW CONFIG FORMULA DERIVATION")
print("=" * 70)
print()

print("For each shadow config s_k, express s_k[i] in terms of good cycle.")
print("Using v=1 for all NB procs.")
print()

for n in [6, 7, 8]:
    ms = [2, 2, 2] + [3] * (n - 3)
    nb_vals = {p: 1 for p in range(n)}
    for p in range(3):
        nb_vals[p] = 1

    cycle = build_uniform_sweep(n, ms, nb_vals)
    det = get_determined(cycle, n)
    shadow = find_shadow_cycle(cycle, det, n, ms)
    if not shadow:
        continue

    print(f"  n={n}:")

    # For each position i, track shadow state vs good state
    for i in range(n):
        g_states = [cycle[k][i] for k in range(len(cycle))]
        s_states = [shadow[k][i] for k in range(len(shadow))]
        print(f"    P{i}: good={g_states}")
        print(f"    P{i}: shad={s_states}")

        # Try to find a shift: s_k[i] = g_{k+d}[i'] for some fixed d, i'
        for i2 in range(n):
            for d in range(len(cycle)):
                match = True
                for k in range(len(shadow)):
                    if s_states[k] != cycle[(k + d) % len(cycle)][i2]:
                        match = False
                        break
                if match:
                    print(f"         → s_k[{i}] = g_{{k+{d}}}[{i2}]")
                    break
            else:
                continue
            break
        else:
            # Try complement
            for i2 in range(n):
                for d in range(len(cycle)):
                    match = True
                    for k in range(len(shadow)):
                        expected = 1 - cycle[(k + d) % len(cycle)][i2] if ms[i2] == 2 else cycle[(k + d) % len(cycle)][i2]
                        if s_states[k] != expected:
                            match = False
                            break
                    if match:
                        print(f"         → s_k[{i}] = 1-g_{{k+{d}}}[{i2}] (complement)")
                        break
                else:
                    continue
                break
            else:
                print(f"         → NO SIMPLE FORMULA FOUND")
    print()


# =================================================================
# PART 4: Shadow as a shifted/permuted good cycle
# =================================================================
print("=" * 70)
print("PART 4: SHADOW = TRANSFORMED GOOD CYCLE?")
print("=" * 70)
print()

print("Check if shadow is a spatial permutation + time shift of good cycle.")
print("i.e., s_k[i] = g_{k+d}[π(i)] for some permutation π and shift d.")
print()

for n in [5, 6, 7, 8, 9, 10]:
    ms = [2, 2, 2] + [3] * (n - 3)
    nb_vals = {p: 1 for p in range(n)}
    for p in range(3):
        nb_vals[p] = 1

    cycle = build_uniform_sweep(n, ms, nb_vals)
    det = get_determined(cycle, n)
    shadow = find_shadow_cycle(cycle, det, n, ms)
    if not shadow:
        print(f"  n={n}: no shadow")
        continue

    L = len(cycle)
    found = False

    # Try all spatial permutations (too many for large n, so try ring rotations + reflections)
    # Actually, just try to find π position by position
    # For each position i in shadow, find which good-cycle position j and shift d
    # gives s_k[i] = g_{k+d}[j] for all k

    # For position i=0 (binary):
    # s_k[0] values
    s0 = [shadow[k][0] for k in range(L)]

    # Try each j, d
    matches_0 = []
    for j in range(n):
        for d in range(L):
            if all(shadow[k][0] == cycle[(k + d) % L][j] for k in range(L)):
                matches_0.append((j, d))

    # Also try complement for binary
    for j in range(n):
        for d in range(L):
            if all(shadow[k][0] == (1 - cycle[(k + d) % L][j]) for k in range(L)):
                matches_0.append((j, d, 'comp'))

    if not matches_0:
        print(f"  n={n}: P0 has no match")
        continue

    # For each candidate (j0, d), check if it extends to all positions
    for candidate in matches_0:
        if len(candidate) == 3:
            j0, d, comp = candidate
            # Shadow with complement on binary - complex, skip for now
            continue
        j0, d = candidate

        # Find π(i) for each i using this d
        pi = {}
        all_match = True
        for i in range(n):
            found_pi = False
            for j in range(n):
                if all(shadow[k][i] == cycle[(k + d) % L][j] for k in range(L)):
                    pi[i] = j
                    found_pi = True
                    break
            if not found_pi:
                all_match = False
                break

        if all_match and len(set(pi.values())) == n:  # π is a bijection
            print(f"  n={n}: shadow = permuted good cycle!")
            print(f"    Time shift d = {d}")
            print(f"    Spatial permutation π: {pi}")
            print(f"    π as list: [{', '.join(str(pi[i]) for i in range(n))}]")
            found = True
            break

    if not found:
        # Try with binary complement
        for d in range(L):
            pi = {}
            all_match = True
            for i in range(n):
                found_pi = False
                for j in range(n):
                    if ms[j] == 2:
                        # Try complement
                        if all(shadow[k][i] == (1 - cycle[(k + d) % L][j]) for k in range(L)):
                            pi[i] = (j, 'comp')
                            found_pi = True
                            break
                    if all(shadow[k][i] == cycle[(k + d) % L][j] for k in range(L)):
                        pi[i] = (j, 'same')
                        found_pi = True
                        break
                if not found_pi:
                    all_match = False
                    break

            if all_match:
                print(f"  n={n}: shadow = permuted+complemented good cycle!")
                print(f"    Time shift d = {d}")
                print(f"    Map: {pi}")
                found = True
                break

    if not found:
        print(f"  n={n}: no simple transformation found")

print()


# =================================================================
# PART 5: Direct formula attempt — express s_k position by position
# =================================================================
print("=" * 70)
print("PART 5: PER-POSITION SHADOW FORMULA")
print("=" * 70)
print()

for n in [5, 6, 7, 8]:
    ms = [2, 2, 2] + [3] * (n - 3)
    nb_vals = {p: 1 for p in range(n)}
    for p in range(3):
        nb_vals[p] = 1

    cycle = build_uniform_sweep(n, ms, nb_vals)
    det = get_determined(cycle, n)
    shadow = find_shadow_cycle(cycle, det, n, ms)
    if not shadow:
        continue

    L = len(cycle)
    print(f"  n={n} (L={L}):")

    for i in range(n):
        s_vals = [shadow[k][i] for k in range(L)]

        # Try: s_k[i] = g_{k+d}[j] (plain shift + position remap)
        found_formula = False
        for j in range(n):
            for d in range(L):
                if all(s_vals[k] == cycle[(k + d) % L][j] for k in range(L)):
                    print(f"    s_k[{i}] = g_{{k+{d}}}[{j}]", end="")
                    if d == 0:
                        print(f"  (= g_k[{j}])", end="")
                    print()
                    found_formula = True
                    break
            if found_formula:
                break

        if not found_formula:
            # Try complement for binary
            if ms[i] == 2:
                for j in range(n):
                    for d in range(L):
                        if all(s_vals[k] == (1 - cycle[(k + d) % L][j]) for k in range(L)):
                            print(f"    s_k[{i}] = 1 - g_{{k+{d}}}[{j}]")
                            found_formula = True
                            break
                    if found_formula:
                        break

        if not found_formula:
            print(f"    s_k[{i}] = {s_vals}  (NO FORMULA)")
    print()

print()
print("=" * 70)
print("SUMMARY")
print("=" * 70)
