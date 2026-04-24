#!/usr/bin/env python3
"""
RA14: Palindromic Entry Conflict — Existential Data Characterization

Investigates the 4 sorrys in CaseObstructionsCore.lean:
  Sorry 1: configs.length = 2n (from ZW + fair + distinct)
  Sorry 4a: configVal (left b) equal at mover/non-mover steps
  Sorry 4b: configVal b equal at the two steps
  Sorry 4c: configVal (right b) equal at the two steps

For each zero-winding good cycle, extracts:
  - Palindromic structure (mover word, CW/CCW split)
  - Interior binary processors
  - Matching step pairs (k1, k2)
  - Exact firing history between k1 and k2 for {left(b), b, right(b)}
  - What data the Lean existential needs to carry
"""

from itertools import product as iproduct
from collections import defaultdict


def enumerate_fc2_walks(n):
    """Enumerate all fc=2 mover words of length 2n on Z_n (closed walks)."""
    walks = []
    def dfs(path, fc):
        pos = path[-1]
        step = len(path)
        if step == 2 * n:
            nxt = path[0]
            if abs(pos - nxt) == 1 or abs(pos - nxt) == n - 1:
                if all(f == 2 for f in fc):
                    walks.append(tuple(path))
            return
        for d in [1, -1]:
            nxt = (pos + d) % n
            if fc[nxt] < 2:
                fc[nxt] += 1
                path.append(nxt)
                dfs(path, fc)
                path.pop()
                fc[nxt] -= 1
    fc = [0] * n
    fc[0] = 1
    dfs([0], fc)
    # Deduplicate by canonical rotation
    unique = set()
    result = []
    for w in walks:
        best = w
        for i in range(len(w)):
            rot = w[i:] + w[:i]
            if rot < best:
                best = rot
        if best not in unique:
            unique.add(best)
            result.append(list(best))
    return result


def step_dir(word, t, n):
    """Direction of step t: CW = +1, CCW = -1, stay = 0."""
    L = len(word)
    curr = word[t]
    nxt = word[(t + 1) % L]
    d = (nxt - curr) % n
    if d == 1:
        return 1  # CW
    elif d == n - 1:
        return -1  # CCW
    return 0


def winding_number(word, n):
    """Net winding: sum of directions."""
    return sum(step_dir(word, t, n) for t in range(len(word)))


def is_sweep(word, n):
    L = len(word)
    dirs = [(word[(i + 1) % L] - word[i]) % n for i in range(L)]
    return all(d == 1 for d in dirs) or all(d == n - 1 for d in dirs)


def enumerate_state_sequences(m, k):
    """Enumerate all length-(k+1) sequences starting and ending at 0,
    with consecutive elements different, each taking values in {0,...,m-1}."""
    seqs = []
    def dfs(seq, remaining):
        if remaining == 0:
            if seq[-1] == 0:
                seqs.append(list(seq))
            return
        for nv in range(m):
            if nv != seq[-1]:
                if remaining == 1 and nv != 0:
                    continue
                seq.append(nv)
                dfs(seq, remaining - 1)
                seq.pop()
    dfs([0], k)
    return seqs


def build_configs(word, n, ms, combo):
    """Build config sequence from state-sequence combo."""
    L = len(word)
    ss = {p: combo[p] for p in range(n)}
    fcc = [0] * n
    configs = [tuple(ss[p][0] for p in range(n))]
    for t in range(L):
        fcc[word[t]] += 1
        configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
    return configs


def main():
    print("=" * 72)
    print("RA14: Palindromic Entry Conflict — Existential Data Characterization")
    print("=" * 72)

    # =====================================================================
    # PART 1: Enumerate zero-winding good cycles, verify CL = 2n
    # =====================================================================
    print("\n" + "=" * 72)
    print("PART 1: Zero-winding cycles and CL = 2n verification")
    print("=" * 72)

    for n in [5, 7]:
        print(f"\n--- n = {n} ---")
        walks = enumerate_fc2_walks(n)
        print(f"Total fc=2 walks (length {2*n}): {len(walks)}")

        zw_walks = [w for w in walks if winding_number(w, n) == 0]
        sweep_walks = [w for w in walks if is_sweep(w, n)]
        nonsweep_zw = [w for w in zw_walks if not is_sweep(w, n)]

        print(f"Zero-winding walks: {len(zw_walks)}")
        print(f"Sweep walks: {len(sweep_walks)}")
        print(f"Non-sweep zero-winding: {len(nonsweep_zw)}")

        # All fc=2 walks have length 2n by construction
        all_2n = all(len(w) == 2 * n for w in walks)
        print(f"All walks have length 2n = {2*n}: {all_2n}")

        # Verify: for ZW walks, winding = 0 means #CW = #CCW = n
        for w in nonsweep_zw[:3]:
            cw = sum(1 for t in range(len(w)) if step_dir(w, t, n) == 1)
            ccw = sum(1 for t in range(len(w)) if step_dir(w, t, n) == -1)
            stay = sum(1 for t in range(len(w)) if step_dir(w, t, n) == 0)
            print(f"  Walk {w}: CW={cw}, CCW={ccw}, stay={stay}")

    # =====================================================================
    # PART 2: Palindromic structure analysis
    # =====================================================================
    print("\n" + "=" * 72)
    print("PART 2: Palindromic structure — CW/CCW phases for ZW walks")
    print("=" * 72)

    for n in [5, 7]:
        print(f"\n--- n = {n} ---")
        walks = enumerate_fc2_walks(n)
        nonsweep_zw = [w for w in walks
                       if winding_number(w, n) == 0 and not is_sweep(w, n)]

        # Classify ZW walks by their CW/CCW phase structure
        has_clean_palindrome = 0
        total = len(nonsweep_zw)

        for wi, w in enumerate(nonsweep_zw):
            L = len(w)
            dirs = [step_dir(w, t, n) for t in range(L)]

            # Find phase transitions (CW→CCW or CCW→CW)
            transitions = []
            for t in range(L):
                if dirs[t] != dirs[(t + 1) % L]:
                    transitions.append(t)

            # A "clean palindrome" has exactly 2 transitions: CW→CCW and CCW→CW
            if len(transitions) == 2:
                has_clean_palindrome += 1

            if wi < 3:
                print(f"\n  Walk {w}")
                print(f"  Dirs: {['CW' if d==1 else ('CCW' if d==-1 else 'S') for d in dirs]}")
                print(f"  Phase transitions at steps: {transitions}")
                print(f"  Is clean palindrome (2 transitions): {len(transitions) == 2}")

                # Show CW and CCW firing steps per proc
                cw_steps = defaultdict(list)
                ccw_steps = defaultdict(list)
                for t in range(L):
                    p = w[t]
                    if dirs[t] == 1:
                        cw_steps[p].append(t)
                    elif dirs[t] == -1:
                        ccw_steps[p].append(t)
                print(f"  CW firing steps:  {dict(sorted(cw_steps.items()))}")
                print(f"  CCW firing steps: {dict(sorted(ccw_steps.items()))}")

        print(f"\n  Clean palindromes (2 transitions): {has_clean_palindrome}/{total}")

    # =====================================================================
    # PART 3: Context matching at interior binary processors
    # =====================================================================
    print("\n" + "=" * 72)
    print("PART 3: Context match at interior binary — detailed step pairs")
    print("=" * 72)

    for n in [5, 7]:
        print(f"\n{'='*60}")
        print(f"n = {n}")
        print(f"{'='*60}")

        walks = enumerate_fc2_walks(n)
        nonsweep_zw = [w for w in walks
                       if winding_number(w, n) == 0 and not is_sweep(w, n)]

        # Test with canonical ms: 3 binary at start
        ms = [2, 2, 2] + [3] * (n - 3)
        binary_pos = [i for i in range(n) if ms[i] == 2]
        print(f"ms = {ms}, binary at {binary_pos}")

        total_valid_combos = 0
        total_with_ec = 0
        total_without_ec = 0

        for wi, w in enumerate(nonsweep_zw):
            L = len(w)
            dirs = [step_dir(w, t, n) for t in range(L)]

            # For each proc: identify its CW and CCW firing steps
            cw_fire = {}  # proc → CW step
            ccw_fire = {}  # proc → CCW step
            for t in range(L):
                p = w[t]
                if dirs[t] == 1:
                    cw_fire[p] = t
                elif dirs[t] == -1:
                    ccw_fire[p] = t

            # Generate all valid state-sequence combos
            fc = [0] * n
            for p in w:
                fc[p] += 1
            proc_seqs = {p: enumerate_state_sequences(ms[p], fc[p]) for p in range(n)}
            sl = [proc_seqs[p] for p in range(n)]

            walk_valid = 0
            walk_ec = 0

            for combo in iproduct(*sl):
                configs = build_configs(w, n, ms, combo)
                if configs[-1] != configs[0]:
                    continue
                if len(set(configs[:L])) != L:
                    continue

                walk_valid += 1
                good = configs[:L]

                found_ec = False
                for b in binary_pos:
                    rb = (b + 1) % n
                    lb = (b - 1) % n

                    # Lean approach: k1 = ccwSteps[b] (b fires CCW, b is mover)
                    #                 k2 = cwSteps[right(b)] (right(b) fires CW, b is non-mover)
                    if b not in ccw_fire or rb not in cw_fire:
                        continue

                    t_mover = ccw_fire[b]       # b fires CCW (b is mover)
                    t_nonmover = cw_fire[rb]    # right(b) fires CW (b is non-mover)

                    c_mover = good[t_mover]
                    c_nonmover = good[t_nonmover]

                    ctx_mover = (c_mover[lb], c_mover[b], c_mover[rb])
                    ctx_nonmover = (c_nonmover[lb], c_nonmover[b], c_nonmover[rb])

                    if ctx_mover == ctx_nonmover:
                        found_ec = True
                        # Print details for first few
                        if walk_valid <= 2 and wi < 2:
                            print(f"\n  Walk {w}, combo #{walk_valid}")
                            print(f"    b={b}, left(b)={lb}, right(b)={rb}")
                            print(f"    t_mover={t_mover} (b fires CCW): ctx={ctx_mover}")
                            print(f"    t_nonmover={t_nonmover} (right(b) fires CW): ctx={ctx_nonmover}")
                            print(f"    MATCH → entry conflict!")

                            # Detailed: what fires between t_nonmover and t_mover?
                            if t_nonmover < t_mover:
                                between = list(range(t_nonmover, t_mover))
                            else:
                                between = list(range(t_nonmover, L)) + list(range(0, t_mover))
                            movers_between = [w[t] for t in between]
                            fires_lb = movers_between.count(lb)
                            fires_b = movers_between.count(b)
                            fires_rb = movers_between.count(rb)
                            print(f"    Steps between t_nonmover and t_mover: {between}")
                            print(f"    Movers between: {movers_between}")
                            print(f"    Fires of left(b)={lb}: {fires_lb}, b={b}: {fires_b}, right(b)={rb}: {fires_rb}")
                        break

                if found_ec:
                    walk_ec += 1
                else:
                    walk_without_ec_combo = combo
                    walk_without_ec = True

            total_valid_combos += walk_valid
            total_with_ec += walk_ec
            total_without_ec += (walk_valid - walk_ec)

        print(f"\nTotal valid combos: {total_valid_combos}")
        print(f"With palindromic EC: {total_with_ec}")
        print(f"Without palindromic EC: {total_without_ec}")

    # =====================================================================
    # PART 4: Firing analysis between the two steps — what does Lean need?
    # =====================================================================
    print("\n" + "=" * 72)
    print("PART 4: Firing analysis — what data does the existential carry?")
    print("=" * 72)

    for n in [5, 7, 9]:
        print(f"\n--- n = {n} ---")

        walks = enumerate_fc2_walks(n) if n <= 7 else []
        if n == 9:
            # For n=9, just test canonical palindromic walk
            walks = [list(range(n)) + list(range(n-2, 0, -1)) + [0, n-1]]

        nonsweep_zw = [w for w in walks
                       if winding_number(w, n) == 0 and not is_sweep(w, n)]

        ms = [2, 2, 2] + [3] * (n - 3)
        binary_pos = [i for i in range(n) if ms[i] == 2]

        # For EVERY ZW walk and EVERY binary proc b, compute:
        # Between t_nonmover (cwSteps[right(b)]) and t_mover (ccwSteps[b]),
        # how many times do left(b), b, right(b) fire?
        fire_patterns = defaultdict(int)  # (fires_lb, fires_b, fires_rb) → count

        for w in nonsweep_zw:
            L = len(w)
            dirs = [step_dir(w, t, n) for t in range(L)]

            cw_fire = {}
            ccw_fire = {}
            for t in range(L):
                p = w[t]
                if dirs[t] == 1:
                    cw_fire[p] = t
                elif dirs[t] == -1:
                    ccw_fire[p] = t

            for b in binary_pos:
                rb = (b + 1) % n
                lb = (b - 1) % n

                if b not in ccw_fire or rb not in cw_fire:
                    continue

                t_nonmover = cw_fire[rb]  # right(b) fires CW; b is non-mover
                t_mover = ccw_fire[b]     # b fires CCW; b is mover

                # Count fires between t_nonmover (exclusive) and t_mover (exclusive)
                # i.e., steps t_nonmover+1, ..., t_mover-1 (modular)
                if t_nonmover < t_mover:
                    between = list(range(t_nonmover + 1, t_mover))
                else:
                    between = list(range(t_nonmover + 1, L)) + list(range(0, t_mover))

                movers_between = [w[t] for t in between]
                fires_lb = movers_between.count(lb)
                fires_b = movers_between.count(b)
                fires_rb = movers_between.count(rb)
                fire_patterns[(fires_lb, fires_b, fires_rb)] += 1

        print(f"  Fire patterns (left(b), b, right(b)) between the two key steps:")
        for pattern, count in sorted(fire_patterns.items()):
            lb_fires, b_fires, rb_fires = pattern
            lb_even = "EVEN" if lb_fires % 2 == 0 else "ODD"
            b_even = "EVEN" if b_fires % 2 == 0 else "ODD"
            rb_even = "EVEN" if rb_fires % 2 == 0 else "ODD"
            print(f"    ({lb_fires}, {b_fires}, {rb_fires}) [{lb_even}, {b_even}, {rb_even}]: {count} cases")

    # =====================================================================
    # PART 5: The alternative — step ordering and the "no fire between" argument
    # =====================================================================
    print("\n" + "=" * 72)
    print("PART 5: Alternative — does 'no fire between' work for all walks?")
    print("=" * 72)

    for n in [5, 7]:
        print(f"\n--- n = {n} ---")
        walks = enumerate_fc2_walks(n)
        nonsweep_zw = [w for w in walks
                       if winding_number(w, n) == 0 and not is_sweep(w, n)]

        ms = [2, 2, 2] + [3] * (n - 3)
        binary_pos = [i for i in range(n) if ms[i] == 2]

        # For each walk and each binary b:
        # Find ALL pairs (t1, t2) where b is non-mover at t1 and mover at t2
        # and check if there's a pair with NO fires of {lb, b, rb} between them
        total_pairs = 0
        no_fire_works = 0
        even_fire_works = 0
        some_pair_works = 0  # for each (walk, b): is there at least one good pair?
        total_walkb = 0
        walkb_with_good_pair = 0

        for w in nonsweep_zw:
            L = len(w)
            dirs = [step_dir(w, t, n) for t in range(L)]

            for b in binary_pos:
                rb = (b + 1) % n
                lb = (b - 1) % n

                # Steps where b is non-mover
                nonmover_steps = [t for t in range(L) if w[t] != b]
                # Steps where b is mover
                mover_steps = [t for t in range(L) if w[t] == b]

                total_walkb += 1
                found_good = False

                for t1 in nonmover_steps:
                    for t2 in mover_steps:
                        total_pairs += 1

                        # Count fires of {lb, b, rb} between t1 and t2
                        if t1 < t2:
                            between = list(range(t1 + 1, t2))
                        else:
                            between = list(range(t1 + 1, L)) + list(range(0, t2))

                        movers_between = [w[t] for t in between]
                        neighborhood = {lb, b, rb}
                        fires = sum(1 for m in movers_between if m in neighborhood)

                        if fires == 0:
                            no_fire_works += 1
                            found_good = True

                        # Check even fires for each of {lb, b, rb}
                        f_lb = movers_between.count(lb)
                        f_b = movers_between.count(b)
                        f_rb = movers_between.count(rb)
                        if f_lb % 2 == 0 and f_b % 2 == 0 and f_rb % 2 == 0:
                            even_fire_works += 1

                if found_good:
                    walkb_with_good_pair += 1

        print(f"  Total (walk, b) pairs: {total_walkb}")
        print(f"  Pairs with a 'no-fire-between' step pair: {walkb_with_good_pair}/{total_walkb}")
        print(f"  Individual pairs with no fires between: {no_fire_works}/{total_pairs}")
        print(f"  Individual pairs with all-even fires: {even_fire_works}/{total_pairs}")

    # =====================================================================
    # PART 6: The Lean-specific step pair (cwSteps[right(b)], ccwSteps[b])
    # =====================================================================
    print("\n" + "=" * 72)
    print("PART 6: Lean step pair — detailed firing between cwSteps[rb] and ccwSteps[b]")
    print("=" * 72)

    for n in [5, 7]:
        print(f"\n--- n = {n} ---")
        walks = enumerate_fc2_walks(n)
        nonsweep_zw = [w for w in walks
                       if winding_number(w, n) == 0 and not is_sweep(w, n)]

        ms = [2, 2, 2] + [3] * (n - 3)
        binary_pos = [i for i in range(n) if ms[i] == 2]

        # For each walk: trace the exact step ordering
        for wi, w in enumerate(nonsweep_zw[:5]):
            L = len(w)
            dirs = [step_dir(w, t, n) for t in range(L)]

            # Build CW/CCW firing maps
            cw_fire = {}
            ccw_fire = {}
            for t in range(L):
                p = w[t]
                if dirs[t] == 1:
                    cw_fire[p] = t
                elif dirs[t] == -1:
                    ccw_fire[p] = t

            print(f"\n  Walk {w}")
            print(f"  Step details:")
            for t in range(L):
                d = 'CW' if dirs[t] == 1 else ('CCW' if dirs[t] == -1 else 'S')
                print(f"    t={t}: mover={w[t]}, dir={d}")

            for b in binary_pos:
                rb = (b + 1) % n
                lb = (b - 1) % n

                if b not in ccw_fire or rb not in cw_fire:
                    continue

                t_nm = cw_fire[rb]   # right(b) fires CW, b non-mover
                t_m = ccw_fire[b]    # b fires CCW, b mover

                print(f"\n    Binary b={b} (lb={lb}, rb={rb}):")
                print(f"    t_nonmover = {t_nm} (rb={rb} fires CW)")
                print(f"    t_mover    = {t_m} (b={b} fires CCW)")

                # Steps between t_nm (inclusive) and t_m (exclusive)
                # = steps t_nm, t_nm+1, ..., t_m-1
                if t_nm <= t_m:
                    between_incl = list(range(t_nm, t_m))
                else:
                    between_incl = list(range(t_nm, L)) + list(range(0, t_m))

                print(f"    Steps from t_nm to t_m (excl): {between_incl}")
                for t in between_incl:
                    d = 'CW' if dirs[t] == 1 else ('CCW' if dirs[t] == -1 else 'S')
                    marker = ""
                    if w[t] == lb:
                        marker = " <-- left(b)"
                    elif w[t] == b:
                        marker = " <-- b FIRES!"
                    elif w[t] == rb:
                        marker = " <-- right(b)"
                    print(f"      t={t}: mover={w[t]} dir={d}{marker}")

                # Also check: t_nm+1 to t_m-1 (strictly between)
                if t_nm < t_m:
                    strict_between = list(range(t_nm + 1, t_m))
                else:
                    strict_between = list(range(t_nm + 1, L)) + list(range(0, t_m))

                movers_strict = [w[t] for t in strict_between]
                fires_lb = movers_strict.count(lb)
                fires_b = movers_strict.count(b)
                fires_rb = movers_strict.count(rb)
                print(f"    Strictly between (t_nm+1..t_m-1): fires lb={fires_lb}, b={fires_b}, rb={fires_rb}")

    # =====================================================================
    # PART 7: Sorry 1 argument — CL = 2n from fc=2
    # =====================================================================
    print("\n" + "=" * 72)
    print("PART 7: Sorry 1 — CL = 2n argument analysis")
    print("=" * 72)

    print("""
    The argument for CL = 2n:

    1. fc(p) = 2 for all p (already proved in Lean via allFireCount_eq_2_of_zeroWinding)
    2. CL = sum of fc(p) = sum of 2 = 2n
       This uses gc.sum_fireCount which says sum_p fc(p) = configs.length.

    Wait — this is NOT a sorry. The Lean code already USES hlen to prove fc=2.
    The sorry is INSIDE the proof of allFireCount_eq_2_of_zeroWinding:
      "gc.configs.length = 2 * sys.rs.n"
    which is needed BEFORE fc=2 is established.

    The argument should be:
    - Zero winding → #CW = #CCW
    - No safe processor + fairness → every proc fires at least once
    - fc ≥ 1 for all → each proc fires in CW and in CCW direction
    - #CW ≥ n (each of n procs fires at least once in CW direction)
    - Similarly #CCW ≥ n
    - CL = #CW + #CCW + #stay ≥ 2n
    - Upper bound: configs are distinct → CL ≤ product of ms

    But we need CL = EXACTLY 2n, not just ≥ 2n.

    Alternative: fc ≥ 2 for all (from fireCount_ne_one) → CL = sum fc ≥ 2n.
    If CL > 2n, some fc > 2. For binary proc with fc ≥ 4:
    Binary proc fires 4 times with only 2 states → must revisit a state.
    State sequence: 0, v1, v2, v3, 0 with m=2. So v1,v2,v3 ∈ {0,1} with consecutive ≠.
    The sequence must be 0,1,0,1,0 — the ONLY fc=4 binary sequence.

    But this alone doesn't force CL = 2n. Need: CL > 2n → contradiction.

    Actual argument (from Lean comment):
    "any extra edge crossing or stay step forces fc > 2 at some processor,
    and binary parity + config distinctness then produce a config collision."

    This needs formalization. Let me check computationally:
    """)

    # Check: are there ANY valid walks with fc != 2 for all that are ZW?
    for n in [5, 7]:
        print(f"\n  n={n}: Checking ZW walks with fc != [2,...,2]...")
        # Enumerate walks with various cycle lengths
        for CL in range(2*n + 1, 3*n + 1):
            count = 0
            def enum_walks_cl(n, CL):
                walks = []
                def dfs(path, fc):
                    if len(path) == CL:
                        nxt = path[0]
                        d = (nxt - path[-1]) % n
                        if d == 1 or d == n - 1:
                            # Check winding = 0
                            w = sum(step_dir(path, t, n) for t in range(CL))
                            if w == 0:
                                walks.append(tuple(path))
                        return
                    pos = path[-1]
                    for d in [1, -1]:
                        nxt = (pos + d) % n
                        if fc[nxt] < 3:  # allow up to fc=3
                            fc[nxt] += 1
                            path.append(nxt)
                            dfs(path, fc)
                            path.pop()
                            fc[nxt] -= 1
                fc = [0] * n
                fc[0] = 1
                dfs([0], fc)
                return walks
            if CL <= 2*n + 2 and n <= 5:
                ws = enum_walks_cl(n, CL)
                if ws:
                    print(f"    CL={CL}: {len(ws)} ZW walks found")
                    # Check fc distribution
                    for w in ws[:3]:
                        fc = [0] * n
                        for p in w:
                            fc[p] += 1
                        print(f"      Walk {list(w)}: fc={fc}")

    # =====================================================================
    # PART 8: Synthesis — what should the existential carry?
    # =====================================================================
    print("\n" + "=" * 72)
    print("PART 8: SYNTHESIS — What the Lean existential should carry")
    print("=" * 72)

    print("""
    Current Lean structure in palindromic_ec_of_interior_binary:

    The function receives:
      - hfc2 : ∀ p, gc.fireCount p = 2
      - hpalindromic : ∃ (cwSteps ccwSteps : Fin n → Fin CL), ...
        with cwSteps/ccwSteps giving the CW/CCW firing step for each proc
      - b : Fin n (interior binary processor)

    It constructs the EC witness:
      k1 = ccwSteps b       (b fires CCW → b is mover)
      k2 = cwSteps (right b) (right(b) fires CW → b is non-mover)

    The 3 sorrys need to prove:
      config[k2](left b) = config[k1](left b)    -- sorry 4a
      config[k2](b) = config[k1](b)              -- sorry 4b
      config[k2](right b) = config[k1](right b)  -- sorry 4c

    These reduce to: for each of {left(b), b, right(b)}, the processor's value
    doesn't change between step k2 and step k1.

    The key tool already exists in Lean:
      config_val_eq_of_no_move_between : if proc p doesn't fire between steps a and b,
        then config[a](p) = config[b](p)

      localContext_eq_of_no_neighborhood_moves_between : if none of {left(b), b, right(b)}
        fire between steps a and b, then all three values match.

    So the question is: between k2 = cwSteps[right(b)] and k1 = ccwSteps[b],
    do any of {left(b), b, right(b)} fire?
    """)

    # Check the CANONICAL palindromic walk specifically
    for n in [5, 7, 9]:
        print(f"\n  === Canonical palindromic walk, n={n} ===")
        # Canonical: [0, 1, ..., n-1, n-2, ..., 1, 0, n-1]
        w = list(range(n)) + list(range(n-2, 0, -1)) + [0, n-1]
        L = len(w)
        dirs = [step_dir(w, t, n) for t in range(L)]
        print(f"  Walk: {w}")
        print(f"  Length: {L} = 2*{n}")

        cw_fire = {}
        ccw_fire = {}
        for t in range(L):
            p = w[t]
            if dirs[t] == 1:
                cw_fire[p] = t
            elif dirs[t] == -1:
                ccw_fire[p] = t

        print(f"  CW fire:  {dict(sorted(cw_fire.items()))}")
        print(f"  CCW fire: {dict(sorted(ccw_fire.items()))}")

        # For each interior proc (not endpoints 0 and n-1)
        for b in range(1, n-1):
            rb = (b + 1) % n
            lb = (b - 1) % n

            if b not in ccw_fire or rb not in cw_fire:
                print(f"  b={b}: missing CW/CCW fire step, skip")
                continue

            k2 = cw_fire[rb]   # right(b) fires CW
            k1 = ccw_fire[b]   # b fires CCW

            # Steps strictly between k2 and k1
            if k2 < k1:
                between = list(range(k2 + 1, k1))
            else:
                between = list(range(k2 + 1, L)) + list(range(0, k1))

            movers = [w[t] for t in between]
            neighborhood_fires = [(t, w[t]) for t in between if w[t] in {lb, b, rb}]

            print(f"  b={b}: k2(cwSteps[rb={rb}])={k2}, k1(ccwSteps[b])={k1}")
            print(f"    Between: movers={movers}")
            print(f"    Neighborhood fires: {neighborhood_fires}")

            if not neighborhood_fires:
                print(f"    ==> NO neighborhood fires! localContext_eq_of_no_neighborhood_moves_between applies directly.")
            else:
                print(f"    ==> HAS neighborhood fires. Need different argument.")

    # =====================================================================
    # PART 9: For ALL walks, find the right step pair
    # =====================================================================
    print("\n" + "=" * 72)
    print("PART 9: For ALL ZW walks — is there ALWAYS a no-neighborhood-fire pair?")
    print("=" * 72)

    for n in [5, 7]:
        print(f"\n--- n = {n} ---")
        walks = enumerate_fc2_walks(n)
        nonsweep_zw = [w for w in walks
                       if winding_number(w, n) == 0 and not is_sweep(w, n)]

        ms = [2, 2, 2] + [3] * (n - 3)
        binary_pos = [i for i in range(n) if ms[i] == 2]

        total_walkb = 0
        lean_pair_no_fire = 0  # the specific Lean pair has no neighborhood fire
        lean_pair_has_fire = 0
        bad_walks = []

        for w in nonsweep_zw:
            L = len(w)
            dirs = [step_dir(w, t, n) for t in range(L)]

            cw_fire = {}
            ccw_fire = {}
            for t in range(L):
                p = w[t]
                if dirs[t] == 1:
                    cw_fire[p] = t
                elif dirs[t] == -1:
                    ccw_fire[p] = t

            for b in binary_pos:
                rb = (b + 1) % n
                lb = (b - 1) % n

                if b not in ccw_fire or rb not in cw_fire:
                    continue

                total_walkb += 1
                k2 = cw_fire[rb]
                k1 = ccw_fire[b]

                if k2 < k1:
                    between = list(range(k2 + 1, k1))
                else:
                    between = list(range(k2 + 1, L)) + list(range(0, k1))

                movers = [w[t] for t in between]
                fires_nb = sum(1 for m in movers if m in {lb, b, rb})

                if fires_nb == 0:
                    lean_pair_no_fire += 1
                else:
                    lean_pair_has_fire += 1
                    if len(bad_walks) < 5:
                        bad_walks.append((list(w), b, lb, rb, k2, k1, movers))

        print(f"  Total (walk, b) pairs: {total_walkb}")
        print(f"  Lean pair has no neighborhood fires: {lean_pair_no_fire}/{total_walkb}")
        print(f"  Lean pair HAS neighborhood fires: {lean_pair_has_fire}/{total_walkb}")

        if bad_walks:
            print(f"\n  BAD cases (neighborhood fires in Lean pair):")
            for w, b, lb, rb, k2, k1, movers in bad_walks:
                fires = [(i, m) for i, m in enumerate(movers) if m in {lb, b, rb}]
                print(f"    Walk {w}, b={b}: k2={k2}, k1={k1}, movers={movers}")
                print(f"      Neighborhood fires: {fires}")
                # What's the alternative? Try the OTHER pair: cwSteps[b] and ccwSteps[rb]
                # or try different binary procs
                dirs_w = [step_dir(w, t, n) for t in range(len(w))]
                cw_fire_w = {}
                ccw_fire_w = {}
                for t in range(len(w)):
                    p = w[t]
                    if dirs_w[t] == 1:
                        cw_fire_w[p] = t
                    elif dirs_w[t] == -1:
                        ccw_fire_w[p] = t

                # Try ALL binary procs
                for b2 in binary_pos:
                    rb2 = (b2 + 1) % n
                    lb2 = (b2 - 1) % n
                    if b2 not in ccw_fire_w or rb2 not in cw_fire_w:
                        continue
                    k2b = cw_fire_w[rb2]
                    k1b = ccw_fire_w[b2]
                    if k2b < k1b:
                        btwn = list(range(k2b + 1, k1b))
                    else:
                        btwn = list(range(k2b + 1, len(w))) + list(range(0, k1b))
                    mvrs = [w[t] for t in btwn]
                    fires_nb = sum(1 for m in mvrs if m in {lb2, b2, rb2})
                    if fires_nb == 0:
                        print(f"      Alt binary b={b2} works! (no neighborhood fires)")
                        break

    # =====================================================================
    # PART 10: The alternative approach — two-interval argument
    # =====================================================================
    print("\n" + "=" * 72)
    print("PART 10: Two-interval approach (binary toggle-back)")
    print("=" * 72)

    print("""
    For binary procs, firing twice returns to original value (0→1→0 or 0→1→0).
    So even if left(b) or right(b) fires between the two steps, if they fire
    an EVEN number of times, the value returns.

    For the specific Lean pair (k2=cwSteps[rb], k1=ccwSteps[b]):
    - b itself: fires 0 times between k2 and k1? Let's check.
    - left(b): fires how many times?
    - right(b): fires how many times?

    If all three fire an even number of times → context matches.
    """)

    for n in [5, 7]:
        print(f"\n--- n = {n} ---")
        walks = enumerate_fc2_walks(n)
        nonsweep_zw = [w for w in walks
                       if winding_number(w, n) == 0 and not is_sweep(w, n)]

        ms = [2, 2, 2] + [3] * (n - 3)
        binary_pos = [i for i in range(n) if ms[i] == 2]

        all_even = 0
        not_all_even = 0
        fire_detail = defaultdict(int)

        for w in nonsweep_zw:
            L = len(w)
            dirs = [step_dir(w, t, n) for t in range(L)]

            cw_fire = {}
            ccw_fire = {}
            for t in range(L):
                p = w[t]
                if dirs[t] == 1:
                    cw_fire[p] = t
                elif dirs[t] == -1:
                    ccw_fire[p] = t

            for b in binary_pos:
                rb = (b + 1) % n
                lb = (b - 1) % n

                if b not in ccw_fire or rb not in cw_fire:
                    continue

                k2 = cw_fire[rb]
                k1 = ccw_fire[b]

                if k2 < k1:
                    between = list(range(k2 + 1, k1))
                else:
                    between = list(range(k2 + 1, L)) + list(range(0, k1))

                movers = [w[t] for t in between]
                f_lb = movers.count(lb)
                f_b = movers.count(b)
                f_rb = movers.count(rb)

                fire_detail[(f_lb, f_b, f_rb)] += 1

                if f_lb % 2 == 0 and f_b % 2 == 0 and f_rb % 2 == 0:
                    all_even += 1
                else:
                    not_all_even += 1

        print(f"  All even fires: {all_even}")
        print(f"  Not all even: {not_all_even}")
        print(f"  Fire count distribution:")
        for pattern, count in sorted(fire_detail.items()):
            f_lb, f_b, f_rb = pattern
            parity = f"[{'E' if f_lb%2==0 else 'O'},{'E' if f_b%2==0 else 'O'},{'E' if f_rb%2==0 else 'O'}]"
            print(f"    (lb={f_lb}, b={f_b}, rb={f_rb}) {parity}: {count}")

    # =====================================================================
    # FINAL: Recommendation for Lean existential type
    # =====================================================================
    print("\n" + "=" * 72)
    print("FINAL RECOMMENDATION")
    print("=" * 72)

    print("""
    Based on the analysis above, here is what the Lean proof needs:

    The 3 sorrys (4a, 4b, 4c) in palindromic_ec_of_interior_binary need:

      config[cwSteps(right b)](left b)  = config[ccwSteps b](left b)    -- 4a
      config[cwSteps(right b)](b)       = config[ccwSteps b](b)         -- 4b
      config[cwSteps(right b)](right b) = config[ccwSteps b](right b)   -- 4c

    APPROACH 1 (no-fire-between): If {left(b), b, right(b)} don't fire between
    the two steps, use localContext_eq_of_no_neighborhood_moves_between (already in Lean).
    This works for the CANONICAL walk but may fail for some rotations.

    APPROACH 2 (even-parity for binary): For binary procs, firing an even number
    of times returns to the original value (since m=2: toggle twice = identity).
    For ternary procs, this is more complex.

    APPROACH 3 (step ordering in palindromic walk): The palindromic structure
    guarantees a specific mover ordering. For the Lean pair (cwSteps[rb], ccwSteps[b]):
    - The CW phase fires procs in order: ..., b-1, b, b+1, ...
    - The CCW phase fires procs in order: ..., b+1, b, b-1, ...
    - cwSteps[rb] comes BEFORE ccwSteps[b] in the CW→CCW ordering
    - Between these two steps, the only procs that fire are those in the
      "forward" part of the CW phase and the "backward" part of the CCW phase

    The existential should carry:
    1. Step ordering: cwSteps(right b).val < ccwSteps(b).val
       (or the appropriate modular ordering)
    2. No-fire-between: ∀ k, cwSteps(right b) < k < ccwSteps(b) →
       moverAt k ≠ left b ∧ moverAt k ≠ b ∧ moverAt k ≠ right b

    OR (if no-fire-between doesn't hold universally):
    The existential carries the ACTUAL step orderings from the palindromic structure
    which imply the context equality directly via localContext_eq_of_no_neighborhood_moves_between.
    """)


if __name__ == "__main__":
    main()
