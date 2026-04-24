#!/usr/bin/env python3
"""
RA13 v4: Dream Theorem — correct formulation.

KEY INSIGHT from debugging:
- At n=5,7 the DFS finds thousands of no-EC non-sweep cycles using arbitrary
  (non-incrementing) transition functions. These are genuine consistent cycles.
- The dream theorem "EC ∨ sweep" is FALSE for arbitrary transitions.
- The dream theorem MIGHT hold for proc-level-monotone transitions (inc or dec),
  which is the class relevant to minimum-length cycles.

But actually the lower bound proof needs to handle ALL transitions (since we're
proving impossibility of any valid system). So the right question is:

Q: For each no-EC cycle found, can it be completed to a valid self-stabilizing system?

If NOT: what's the obstruction? It's NOT entry conflict (by assumption).
It must be a COMPLETION obstruction — the cycle can't be extended to cover
all configs with convergence.

NEW FORMULATION: The dream theorem should be:
  "Every sub-threshold good cycle either has EC OR has a completion obstruction."

But that's trivially true (since valid sub-threshold systems don't exist at n≥9).
The useful version is:
  "Every sub-threshold good cycle with ≥3 binary either:
   (a) has entry conflict, OR
   (b) has a shadow/companion (Mode B), OR
   (c) has a completion obstruction (no valid system can use it)."

This is the REAL dichotomy. Let's test which obstruction each cycle has.

Actually, re-reading the task: the master theorem is about modes A and B
at the CYCLE level. Mode A = entry conflict. Mode B = shadow/companion.
The question is whether A ∨ B holds for all sub-threshold cycles.

Let's test that directly: for each no-EC cycle, does it have a shadow cycle
(a disjoint companion with the same mover word)?
"""

import sys
import time
from collections import defaultdict, Counter
from itertools import product as iproduct, combinations
from math import prod

def check_ec(good, word, n):
    L = len(word)
    mover_triples = defaultdict(set)
    nonmover_triples = defaultdict(set)
    for t in range(L):
        c = good[t]
        mover = word[t]
        for j in range(n):
            triple = (c[(j-1)%n], c[j], c[(j+1)%n])
            if j == mover:
                mover_triples[j].add(triple)
            else:
                nonmover_triples[j].add(triple)
    conflicts = {}
    for j in range(n):
        overlap = mover_triples[j] & nonmover_triples[j]
        if overlap:
            conflicts[j] = overlap
    return conflicts


def check_shadow(good, word, n, ms, det):
    """Check if there's a disjoint shadow cycle using the SAME transition function."""
    L = len(word)
    orig_set = set(good)
    product_val = prod(ms)

    for start in iproduct(*(range(m) for m in ms)):
        if tuple(start) in orig_set:
            continue
        configs = [list(start)]
        valid = True
        for t in range(L):
            c = list(configs[-1])
            p = word[t]
            key = (p, c[(p-1)%n], c[p], c[(p+1)%n])
            if key in det:
                c[p] = det[key]
            else:
                # Undetermined: this entry could be anything.
                # For shadow detection, we're asking: does there EXIST
                # a completion that creates a shadow?
                # Simplest: try incrementing as default
                c[p] = (c[p] + 1) % ms[p]
            configs.append(c)
        if tuple(configs[-1]) == tuple(configs[0]):
            cycle_set = set(tuple(c) for c in configs[:L])
            if len(cycle_set) == L and not (cycle_set & orig_set):
                return True
    return False


def check_shadow_any_completion(good, word, n, ms, det):
    """Check if for ANY completion of undetermined entries,
    there exists a disjoint shadow cycle.

    This is hard in general, so we check: under the cycle's own
    transition for determined entries, are there non-cycle configs
    that form a cycle of the same length?

    We try multiple completions of undetermined entries.
    """
    L = len(word)
    orig_set = set(good)
    product_val = prod(ms)

    # Collect which entries are undetermined
    undet_entries = set()
    for start in iproduct(*(range(m) for m in ms)):
        for p in range(n):
            key = (p, start[(p-1)%n], start[p], start[(p+1)%n])
            if key not in det:
                undet_entries.add(key)

    # For each non-cycle start config, try to trace with det + identity for undet
    for start in iproduct(*(range(m) for m in ms)):
        if tuple(start) in orig_set:
            continue
        configs = [list(start)]
        for t in range(L):
            c = list(configs[-1])
            p = word[t]
            key = (p, c[(p-1)%n], c[p], c[(p+1)%n])
            if key in det:
                c[p] = det[key]
            else:
                # Identity (no change) — most permissive for shadow
                pass
            configs.append(c)
        if tuple(configs[-1]) == tuple(configs[0]):
            cycle_set = set(tuple(c) for c in configs[:L])
            if len(cycle_set) == L and not (cycle_set & orig_set):
                return True, "identity-shadow"

    # Try inc completion
    for start in iproduct(*(range(m) for m in ms)):
        if tuple(start) in orig_set:
            continue
        configs = [list(start)]
        for t in range(L):
            c = list(configs[-1])
            p = word[t]
            key = (p, c[(p-1)%n], c[p], c[(p+1)%n])
            if key in det:
                c[p] = det[key]
            else:
                c[p] = (c[p] + 1) % ms[p]
            configs.append(c)
        if tuple(configs[-1]) == tuple(configs[0]):
            cycle_set = set(tuple(c) for c in configs[:L])
            if len(cycle_set) == L and not (cycle_set & orig_set):
                return True, "inc-shadow"

    # Try dec completion
    for start in iproduct(*(range(m) for m in ms)):
        if tuple(start) in orig_set:
            continue
        configs = [list(start)]
        for t in range(L):
            c = list(configs[-1])
            p = word[t]
            key = (p, c[(p-1)%n], c[p], c[(p+1)%n])
            if key in det:
                c[p] = det[key]
            else:
                c[p] = (c[p] - 1) % ms[p]
            configs.append(c)
        if tuple(configs[-1]) == tuple(configs[0]):
            cycle_set = set(tuple(c) for c in configs[:L])
            if len(cycle_set) == L and not (cycle_set & orig_set):
                return True, "dec-shadow"

    return False, None


def enumerate_good_cycles_dfs(ms, n, max_cycles=5000, max_time=60.0):
    t0 = time.time()
    product_val = prod(ms)
    if product_val > 2000:
        return []
    start = tuple([0]*n)
    results = []
    seen = set()
    max_len = min(4*n, product_val)

    def dfs(config, path, word, det, depth):
        nonlocal results
        if time.time() - t0 > max_time or len(results) >= max_cycles:
            return
        for p in range(n):
            for new_val in range(ms[p]):
                if new_val == config[p]:
                    continue
                if word:
                    last = word[-1]
                    diff = min(abs(p - last), n - abs(p - last))
                    if diff > 1:
                        continue
                L = config[(p-1)%n]; S = config[p]; R = config[(p+1)%n]
                key_m = (p, L, S, R)
                new_det = dict(det)
                ok = True
                if key_m in new_det:
                    if new_det[key_m] != new_val:
                        ok = False
                else:
                    new_det[key_m] = new_val
                if not ok:
                    continue
                for i in range(n):
                    if i == p:
                        continue
                    Li = config[(i-1)%n]; Si = config[i]; Ri = config[(i+1)%n]
                    key_i = (i, Li, Si, Ri)
                    if key_i in new_det:
                        if new_det[key_i] != Si:
                            ok = False; break
                    else:
                        new_det[key_i] = Si
                if not ok:
                    continue
                new_config = list(config)
                new_config[p] = new_val
                new_config = tuple(new_config)
                new_word = word + [p]
                if new_config == start and len(path) >= 2*n:
                    cycle = list(path)
                    me_ok = True
                    for idx in range(len(cycle)):
                        c = cycle[idx]
                        priv = []
                        for i in range(n):
                            Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
                            ki = (i, Li, Si, Ri)
                            if ki in new_det and new_det[ki] != Si:
                                priv.append(i)
                        if len(priv) != 1:
                            me_ok = False; break
                    if me_ok:
                        cycle_key = frozenset(cycle)
                        if cycle_key not in seen:
                            seen.add(cycle_key)
                            results.append((cycle, new_word, dict(new_det)))
                    continue
                if new_config not in set(path) and len(path) < max_len:
                    path.append(new_config)
                    dfs(new_config, path, new_word, new_det, depth+1)
                    path.pop()
    dfs(start, [start], [], {}, 0)
    return results


def is_sweep(word, n):
    if len(word) % n != 0:
        return False
    reps = len(word) // n
    doubled = word + word
    for start in range(n):
        for direction in [1, -1]:
            sweep = [(start + direction * i) % n for i in range(n)]
            full = sweep * reps
            for offset in range(len(word)):
                if doubled[offset:offset+len(word)] == full:
                    return True
    return False


def gap_pattern_ms(n, binary_positions):
    ms = [3]*n
    for p in binary_positions:
        ms[p] = 2
    return ms


# =========================================================================
# MAIN
# =========================================================================

if __name__ == "__main__":
    print("=" * 70)
    print("RA13 v4: EC ∨ GlobalObstruction for ALL transitions")
    print("=" * 70)

    for n in [5, 7]:
        threshold = 4 * 3**(n-2)
        print(f"\n{'='*60}")
        print(f"n = {n}, threshold = {threshold}")
        print(f"{'='*60}")

        total = 0
        n_ec = 0
        n_noec = 0
        n_noec_shadow = 0
        n_noec_noshadow = 0
        n_noec_sweep = 0
        shadow_details = Counter()
        noshadow_examples = []

        for bp in combinations(range(n), 3):
            ms = gap_pattern_ms(n, bp)
            if prod(ms) >= threshold:
                continue

            t0 = time.time()
            cycles = enumerate_good_cycles_dfs(ms, n, max_cycles=500, max_time=20.0)

            for cyc, w, det in cycles:
                total += 1
                ec = check_ec(cyc, w, n)
                if ec:
                    n_ec += 1
                    continue

                n_noec += 1
                sw = is_sweep(w, n)
                if sw:
                    n_noec_sweep += 1

                # Check shadow
                has_sh, sh_type = check_shadow_any_completion(cyc, w, n, ms, det)
                if has_sh:
                    n_noec_shadow += 1
                    shadow_details[sh_type] += 1
                else:
                    n_noec_noshadow += 1
                    if len(noshadow_examples) < 5:
                        fc = Counter(w)
                        noshadow_examples.append({
                            'bp': bp, 'ms': ms, 'CL': len(w),
                            'sweep': sw, 'fc': dict(sorted(fc.items())),
                            'word': w
                        })

        print(f"\nTotal cycles: {total}")
        print(f"  With EC (Mode A): {n_ec}")
        print(f"  Without EC: {n_noec}")
        print(f"    Of which sweeps: {n_noec_sweep}")
        print(f"    With shadow (Mode B): {n_noec_shadow} {dict(shadow_details)}")
        print(f"    Without shadow: {n_noec_noshadow}")

        if n_noec_noshadow == 0:
            print(f"\n*** EC ∨ Shadow HOLDS at n={n} ***")
            print("Every no-EC cycle has a shadow companion!")
        else:
            print(f"\n*** EC ∨ Shadow FAILS at n={n} ***")
            print(f"Counterexamples ({n_noec_noshadow}):")
            for ex in noshadow_examples:
                print(f"  bp={ex['bp']}, CL={ex['CL']}, sweep={ex['sweep']}, "
                      f"fc={ex['fc']}")

    # =====================================================================
    print("\n" + "=" * 70)
    print("ALTERNATIVE: Check completion obstruction directly")
    print("For no-EC, no-shadow cycles: can they form valid systems?")
    print("=" * 70)

    n = 5
    threshold = 4 * 3**(n-2)
    bp = (0, 1, 2)
    ms = gap_pattern_ms(n, bp)

    print(f"\nn={n}, bp={bp}, ms={ms}, product={prod(ms)}")

    cycles = enumerate_good_cycles_dfs(ms, n, max_cycles=100, max_time=15.0)
    print(f"Found {len(cycles)} cycles")

    # For each no-EC cycle, try to complete to a valid system
    for idx, (cyc, w, det) in enumerate(cycles[:5]):
        ec = check_ec(cyc, w, n)
        if ec:
            continue
        fc = Counter(w)
        print(f"\nCycle {idx}: CL={len(w)}, fc={dict(sorted(fc.items()))}")

        # Check: does every non-cycle config converge?
        # Build the complete reachability graph
        cycle_set = set(cyc)
        all_configs = list(iproduct(*[range(m) for m in ms]))
        non_cycle = [c for c in all_configs if c not in cycle_set]

        # Determine: for each non-cycle config, which procs are privileged?
        # A proc p is privileged at config c if f_p(L,S,R) ≠ S
        stuck = 0
        reachable = set()
        for cfg in non_cycle:
            priv_procs = []
            for p in range(n):
                L = cfg[(p-1)%n]; S = cfg[p]; R = cfg[(p+1)%n]
                key = (p, L, S, R)
                if key in det:
                    if det[key] != S:
                        priv_procs.append(p)
                # If key not in det: undetermined, could go either way

            if not priv_procs:
                # Check if all entries determined
                all_det = True
                for p in range(n):
                    L = cfg[(p-1)%n]; S = cfg[p]; R = cfg[(p+1)%n]
                    key = (p, L, S, R)
                    if key not in det:
                        all_det = False
                        break
                if all_det:
                    stuck += 1
                    # This config has NO privileged proc — stuck!
                    # This IS a legitimate config. In self-stabilization,
                    # every non-good config must have at least one privileged proc.
                    # If stuck > 0, no valid system can use this cycle.
                    if stuck <= 2:
                        print(f"  STUCK config: {cfg}")

        if stuck > 0:
            print(f"  -> {stuck} stuck configs: COMPLETION IMPOSSIBLE")
        else:
            print(f"  -> No stuck configs, completion might be possible")
            # But there could still be convergence issues (loops)
