#!/usr/bin/env python3
"""
RA13 v3: Focused Dream Theorem investigation.

Key findings from v2:
- n=9: Dream theorem HOLDS (all 43,712 cycles have EC, 0 counterexamples)
- n=5,7: Dream theorem FAILS massively (14K and 70K counterexamples)

But wait — at n=5 and n=7, the DFS finds cycles with arbitrary transition
functions. The EC check requires (L,S,R) overlap between mover and non-mover
steps. With arbitrary transitions, a non-sweep cycle CAN avoid EC.

However, the real question is: can such a cycle be EXTENDED to a valid
self-stabilizing system? A cycle with no EC means the transition function
is consistent (no mover/non-mover conflict), but that's exactly what we
DON'T want — we want to show every cycle MUST have EC, meaning no valid
system can use it as its good cycle.

Wait — re-reading the problem:
- hasEntryConflict = same (L,S,R) appears at both mover step (requires
  f(L,S,R)≠S) and non-mover step (requires f(L,S,R)=S). This is a
  CONTRADICTION, meaning no deterministic f can satisfy both.
- So no-EC means the cycle IS consistent — there exists a valid f.
- The theorem says: sub-threshold good cycle → EC ∨ GlobalObstruction.
- No-EC cycles are exactly those that CAN form valid systems.
- We need to show these are all obstructed by Mode B.

So the question is:
1. At n=5,7: do the no-EC cycles actually form valid self-stabilizing systems?
2. If yes, that means the lower bound DOESN'T hold at n=5,7 for those ms vectors.
3. But we KNOW M_5=96 and all sub-threshold products fail. So what's wrong?

KEY INSIGHT: A good cycle being consistent (no EC) is NECESSARY but not
SUFFICIENT for a valid system. The system also needs:
- The good cycle covers all "good" configs (or at least, all configs
  converge to the good cycle)
- Liveness: every non-good config eventually reaches the good cycle

So a no-EC cycle means "this cycle could exist in a valid system" but doesn't
mean the system is valid overall.

For the LOWER BOUND, what we need is:
- Every VALID SYSTEM has a good cycle
- That good cycle either has EC (impossible) or is a WaterfallCycle (→ GlobalObstruction)

Actually wait. EC means the transition function has a contradiction. If the
good cycle has EC, no consistent transition function exists, so no valid
system can realize that cycle. We want to show ALL good cycles have EC
(so no system exists) OR have some other obstruction.

But at n=5, the DFS finds 14K+ no-EC cycles with 3+ binary, sub-threshold.
These are consistent cycles. The question is whether they can be COMPLETED
to valid systems. The answer must be NO (since M_5=96), but the obstruction
is NOT at the cycle level — it's at the system level (completion fails).

So the dream theorem "EC ∨ WaterfallCycle" is TOO STRONG at n=5,7.

Let me verify this understanding by checking a specific n=5 no-EC cycle.
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


def is_uniform_sweep(word, n):
    if len(word) % n != 0:
        return False
    reps = len(word) // n
    for start in range(n):
        for direction in [1, -1]:
            sweep = [(start + direction * i) % n for i in range(n)]
            full = sweep * reps
            if word == full:
                return True
    return False


def is_generalized_sweep(word, n):
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


def enumerate_good_cycles_exhaustive(ms, n, max_cycles=50000, max_time=60.0):
    """Enumerate good cycles via DFS from zero config."""
    t0 = time.time()
    product_val = prod(ms)
    if product_val > 2000:
        return []

    start = tuple([0]*n)
    results = []
    seen = set()
    max_len = min(4 * n, product_val)

    def dfs(config, path, word, det, depth):
        nonlocal results
        if time.time() - t0 > max_time:
            return
        if len(results) >= max_cycles:
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

                L = config[(p-1) % n]
                S = config[p]
                R = config[(p+1) % n]
                key_m = (p, L, S, R)

                new_det = dict(det)
                consistent = True

                if key_m in new_det:
                    if new_det[key_m] != new_val:
                        consistent = False
                else:
                    new_det[key_m] = new_val

                if not consistent:
                    continue

                ok = True
                for i in range(n):
                    if i == p:
                        continue
                    Li = config[(i-1) % n]
                    Si = config[i]
                    Ri = config[(i+1) % n]
                    key_i = (i, Li, Si, Ri)
                    if key_i in new_det:
                        if new_det[key_i] != Si:
                            ok = False
                            break
                    else:
                        new_det[key_i] = Si

                if not ok:
                    continue

                new_config = list(config)
                new_config[p] = new_val
                new_config = tuple(new_config)
                new_word = word + [p]

                if new_config == start and len(path) >= 2 * n:
                    cycle = list(path)
                    me_ok = True
                    for idx in range(len(cycle)):
                        c = cycle[idx]
                        priv = []
                        for i in range(n):
                            Li = c[(i-1) % n]
                            Si = c[i]
                            Ri = c[(i+1) % n]
                            ki = (i, Li, Si, Ri)
                            if ki in new_det and new_det[ki] != Si:
                                priv.append(i)
                        if len(priv) != 1:
                            me_ok = False
                            break
                    if me_ok:
                        cycle_key = frozenset(cycle)
                        if cycle_key not in seen:
                            seen.add(cycle_key)
                            results.append((cycle, new_word, dict(new_det)))
                    continue

                if new_config not in set(path) and len(path) < max_len:
                    path.append(new_config)
                    dfs(new_config, path, new_word, new_det, depth + 1)
                    path.pop()

    dfs(start, [start], [], {}, 0)
    return results


def can_complete_to_system(cycle, word, det, ms, n):
    """Check if a cycle's partial transition function can be completed to a
    valid self-stabilizing system. Returns (can_complete, reason)."""
    product_val = prod(ms)
    cycle_set = set(cycle)
    all_configs = list(iproduct(*[range(m) for m in ms]))

    # The cycle determines f at some (p, L, S, R) entries.
    # For a valid system, we also need:
    # 1. Every non-cycle config has at least one privileged proc
    #    (f(L,S,R) != S for some proc p)
    # 2. Every config eventually reaches the cycle (convergence)

    # First, check how many configs are in the cycle
    # For self-stabilization, we need exactly ONE token in good configs
    # and convergence from all others

    # Count how many (p, L, S, R) entries are determined
    det_mover = {}  # entries where f != S (mover)
    det_nonmover = {}  # entries where f = S (non-mover)

    for key, val in det.items():
        p, L, S, R = key
        if val != S:
            det_mover[key] = val
        else:
            det_nonmover[key] = val

    # For each non-cycle config, check if it has at least one undetermined
    # entry or a determined mover entry (so it's privileged)
    problem_configs = []
    for cfg in all_configs:
        if cfg in cycle_set:
            continue
        has_priv = False
        all_determined_identity = True
        for p in range(n):
            L = cfg[(p-1) % n]
            S = cfg[p]
            R = cfg[(p+1) % n]
            key = (p, L, S, R)
            if key in det:
                if det[key] != S:
                    has_priv = True
                    break
                # else identity, proc not privileged
            else:
                all_determined_identity = False
                # Not yet determined — could be set to make priv or not

        if all_determined_identity and not has_priv:
            problem_configs.append(cfg)

    return len(problem_configs), len(cycle_set), product_val


def gap_pattern_ms(n, binary_positions):
    ms = [3]*n
    for p in binary_positions:
        ms[p] = 2
    return ms


def get_gaps(binary_pos, n):
    bp = sorted(binary_pos)
    gaps = []
    for i in range(len(bp)):
        nxt = bp[(i+1) % len(bp)]
        cur = bp[i]
        gap = (nxt - cur) % n
        gaps.append(gap)
    return gaps


# =========================================================================
# MAIN
# =========================================================================

if __name__ == "__main__":

    print("=" * 70)
    print("SECTION 1: Examine n=5 no-EC cycles")
    print("=" * 70)

    n = 5
    threshold = 4 * 3**(n-2)
    print(f"n={n}, threshold={threshold}")

    total_noec = 0
    total_ec = 0
    total_noec_sweep = 0
    total_noec_nonsweep = 0
    noec_examples = []

    for bp in combinations(range(n), 3):
        ms = gap_pattern_ms(n, bp)
        p_val = prod(ms)
        if p_val >= threshold:
            continue

        gaps = get_gaps(bp, n)

        cycles = enumerate_good_cycles_exhaustive(ms, n, max_cycles=5000, max_time=20.0)
        for cyc, w, det in cycles:
            ec = check_ec(cyc, w, n)
            is_sw = is_uniform_sweep(w, n) or is_generalized_sweep(w, n)
            if ec:
                total_ec += 1
            else:
                total_noec += 1
                if is_sw:
                    total_noec_sweep += 1
                else:
                    total_noec_nonsweep += 1
                    if len(noec_examples) < 5:
                        noec_examples.append((bp, gaps, ms, cyc, w, det))

    print(f"\nTotal: {total_ec} EC, {total_noec} no-EC")
    print(f"No-EC: {total_noec_sweep} sweep, {total_noec_nonsweep} non-sweep")

    print(f"\nExamining {len(noec_examples)} no-EC non-sweep examples:")
    for bp, gaps, ms, cyc, w, det in noec_examples:
        fc = Counter(w)
        print(f"\n  bp={bp}, gaps={gaps}, ms={ms}, CL={len(w)}")
        print(f"  word={w}")
        print(f"  fire counts={dict(sorted(fc.items()))}")
        print(f"  cycle configs (first 3): {cyc[:3]}")

        # Check completability
        n_problem, n_good, n_total = can_complete_to_system(cyc, w, det, ms, n)
        print(f"  Good configs: {n_good}/{n_total}")
        print(f"  Problem configs (all determined as identity): {n_problem}")
        print(f"  Determined entries: {len(det)}")

        # Check shadow
        L = len(w)
        orig_set = set(cyc)
        shadow_count = 0
        for start in iproduct(*(range(m) for m in ms)):
            if tuple(start) in orig_set:
                continue
            configs = [list(start)]
            for t in range(L):
                c = list(configs[-1])
                p2 = w[t]
                # Use the SAME transition function
                key = (p2, c[(p2-1)%n], c[p2], c[(p2+1)%n])
                if key in det:
                    c[p2] = det[key]
                else:
                    c[p2] = (c[p2] + 1) % ms[p2]  # default inc
                configs.append(c)
            if configs[-1] == list(configs[0]):
                cycle_set = set(tuple(c) for c in configs[:L])
                if len(cycle_set) == L and not (cycle_set & orig_set):
                    shadow_count += 1
        print(f"  Shadow cycles (same det): {shadow_count}")

    # =====================================================================
    print("\n" + "=" * 70)
    print("SECTION 2: What makes n=9 different?")
    print("At n=9, ALL 43K cycles have EC. Why?")
    print("=" * 70)

    # The key insight from memory: at n=9, sub-threshold products have ≥3
    # binary. With product < 8748 = 4*3^7, ms must contain enough 2s.
    # The specific ms vectors at n=9 with 3 binary are [2,2,2,3,3,3,3,3,3]
    # (product = 4*3^6 = 2916) and permutations.

    # At n=5, sub-threshold = product < 108. With 3 binary:
    # ms like [2,2,2,3,3] has product 72 < 108.
    # There are also ms like [2,2,2,3,4] with product 96 = M_5.
    # Wait, 96 < 108 so that's sub-threshold too.

    # The question: WHY does EC hold universally at n=9 but not n=5?

    print("\nSub-threshold multisets:")
    for n_val in [5, 7, 9]:
        threshold = 4 * 3**(n_val-2)
        print(f"\nn={n_val}, threshold={threshold}")
        for bp in combinations(range(n_val), 3):
            ms = gap_pattern_ms(n_val, bp)
            if prod(ms) < threshold:
                print(f"  bp={bp}, ms={ms}, product={prod(ms)}, "
                      f"ratio={prod(ms)/threshold:.3f}")
                break  # just one example per n

    # =====================================================================
    print("\n" + "=" * 70)
    print("SECTION 3: n=5 focused — verify no-EC cycles can't complete")
    print("=" * 70)

    # Take a specific no-EC non-sweep cycle and try to complete it
    if noec_examples:
        bp, gaps, ms, cyc, w, det = noec_examples[0]
        print(f"\nExample: bp={bp}, ms={ms}, CL={len(w)}, word={w}")
        print(f"Cycle: {cyc}")
        print(f"Determined entries ({len(det)}):")
        for key, val in sorted(det.items()):
            p, L, S, R = key
            marker = " <- MOVER" if val != S else ""
            print(f"  f_{p}({L},{S},{R}) = {val}{marker}")

        # Count undetermined entries
        all_possible = set()
        for cfg in iproduct(*[range(m) for m in ms]):
            for p in range(n):
                L = cfg[(p-1) % n]
                S = cfg[p]
                R = cfg[(p+1) % n]
                all_possible.add((p, L, S, R))
        undetermined = all_possible - set(det.keys())
        print(f"\nTotal possible entries: {len(all_possible)}")
        print(f"Determined: {len(det)}")
        print(f"Undetermined: {len(undetermined)}")

        # For each non-cycle config, show its status
        cycle_set = set(cyc)
        all_configs = list(iproduct(*[range(m) for m in ms]))
        non_cycle = [c for c in all_configs if c not in cycle_set]

        print(f"\nNon-cycle configs: {len(non_cycle)}")
        priv_status = Counter()
        for cfg in non_cycle:
            n_priv = 0
            n_undet = 0
            for p in range(n):
                L_val = cfg[(p-1) % n]
                S_val = cfg[p]
                R_val = cfg[(p+1) % n]
                key = (p, L_val, S_val, R_val)
                if key in det:
                    if det[key] != S_val:
                        n_priv += 1
                else:
                    n_undet += 1
            priv_status[(n_priv, n_undet)] += 1

        print("Status (priv_count, undet_count): count")
        for (np, nu), cnt in sorted(priv_status.items()):
            print(f"  ({np} privileged, {nu} undetermined): {cnt} configs")

    # =====================================================================
    print("\n" + "=" * 70)
    print("SECTION 4: REFINED Dream Theorem — minimum cycle length")
    print("=" * 70)
    print("The minimum-length good cycle for sub-threshold 3-binary systems")
    print("has length 2n (each proc fires exactly ms[p] times).")
    print("Test: does the dream theorem hold for MINIMUM-LENGTH cycles?")

    for n_val in [5, 7]:
        threshold = 4 * 3**(n_val-2)
        print(f"\nn={n_val}, threshold={threshold}")

        min_len_ec = 0
        min_len_noec_sweep = 0
        min_len_noec_nonsweep = 0

        for bp in combinations(range(n_val), 3):
            ms = gap_pattern_ms(n_val, bp)
            if prod(ms) >= threshold:
                continue

            # Minimum cycle length: each proc fires ms[p] times
            # Total = sum(ms[p]) for binary (fire 2x) + ternary (fire 3x)
            min_cl = sum(ms)

            cycles = enumerate_good_cycles_exhaustive(ms, n_val,
                                                       max_cycles=10000, max_time=15.0)

            for cyc, w, det in cycles:
                if len(w) != min_cl:
                    continue
                ec = check_ec(cyc, w, n_val)
                is_sw = (is_uniform_sweep(w, n_val) or
                         is_generalized_sweep(w, n_val))
                if ec:
                    min_len_ec += 1
                elif is_sw:
                    min_len_noec_sweep += 1
                else:
                    min_len_noec_nonsweep += 1
                    fc = Counter(w)
                    print(f"  COUNTEREXAMPLE: bp={bp}, ms={ms}, CL={len(w)}, "
                          f"fc={dict(sorted(fc.items()))}")

        print(f"Min-length cycles: {min_len_ec} EC, {min_len_noec_sweep} sweep, "
              f"{min_len_noec_nonsweep} non-sweep")
        if min_len_noec_nonsweep == 0:
            print(f"=> REFINED DREAM HOLDS at n={n_val}")
        else:
            print(f"=> REFINED DREAM FAILS at n={n_val}")

    # =====================================================================
    print("\n" + "=" * 70)
    print("SECTION 5: Even stronger test — does EVERY no-EC cycle have")
    print("a global obstruction (shadow/companion)?")
    print("=" * 70)

    n = 5
    threshold = 4 * 3**(n-2)
    noec_with_shadow = 0
    noec_without_shadow = 0
    noec_total = 0
    noec_noshadow_examples = []

    for bp in combinations(range(n), 3):
        ms = gap_pattern_ms(n, bp)
        if prod(ms) >= threshold:
            continue

        cycles = enumerate_good_cycles_exhaustive(ms, n, max_cycles=2000, max_time=15.0)

        for cyc, w, det in cycles:
            ec = check_ec(cyc, w, n)
            if ec:
                continue
            noec_total += 1

            # Check for shadow using incrementing
            L = len(w)
            orig_set = set(cyc)
            found_shadow = False
            for start_cfg in iproduct(*(range(m) for m in ms)):
                if tuple(start_cfg) in orig_set:
                    continue
                configs = [list(start_cfg)]
                for t in range(L):
                    c = list(configs[-1])
                    p = w[t]
                    # Use the cycle's own transition
                    key = (p, c[(p-1)%n], c[p], c[(p+1)%n])
                    if key in det:
                        c[p] = det[key]
                    else:
                        # Undetermined — try identity (non-move)
                        pass  # c[p] unchanged
                    configs.append(c)
                if tuple(configs[-1]) == tuple(configs[0]):
                    cycle_set = set(tuple(c) for c in configs[:L])
                    if len(cycle_set) == L and not (cycle_set & orig_set):
                        found_shadow = True
                        break

            if found_shadow:
                noec_with_shadow += 1
            else:
                noec_without_shadow += 1
                if len(noec_noshadow_examples) < 3:
                    noec_noshadow_examples.append((bp, ms, cyc, w, det))

    print(f"\nn={n}: {noec_total} no-EC cycles")
    print(f"  With shadow: {noec_with_shadow}")
    print(f"  Without shadow: {noec_without_shadow}")

    # =====================================================================
    print("\n" + "=" * 70)
    print("SECTION 6: THE REAL QUESTION — incrementing-only dream theorem")
    print("Do all sub-threshold good cycles under INCREMENTING transitions")
    print("satisfy EC ∨ sweep?")
    print("=" * 70)

    for n_val in [5, 7]:
        threshold = 4 * 3**(n_val-2)
        print(f"\nn={n_val}, threshold={threshold}")

        inc_ec = 0
        inc_noec_sweep = 0
        inc_noec_nonsweep = 0

        for bp in combinations(range(n_val), 3):
            ms = gap_pattern_ms(n_val, bp)
            if prod(ms) >= threshold:
                continue

            # Enumerate ALL adjacent-mover words up to length 4n
            # that form valid cycles under incrementing
            t0 = time.time()
            max_cl = min(4 * n_val, prod(ms))
            start = tuple([0]*n_val)

            found = set()
            stack = [(start, [start], [])]

            while stack and time.time() - t0 < 20.0:
                config, path, word = stack.pop()

                for p in range(n_val):
                    if config[p] == (ms[p] - 1) and ms[p] > 1:
                        new_val = 0
                    else:
                        new_val = (config[p] + 1) % ms[p]
                    # Only incrementing transition
                    if new_val == config[p]:
                        continue

                    if word:
                        last = word[-1]
                        diff = min(abs(p - last), n_val - abs(p - last))
                        if diff > 1:
                            continue

                    new_config = list(config)
                    new_config[p] = new_val
                    new_config = tuple(new_config)
                    new_word = word + [p]

                    if new_config == start and len(path) >= 2 * n_val:
                        # Check distinct
                        if len(set(path)) == len(path):
                            cycle_key = frozenset(path)
                            if cycle_key not in found:
                                found.add(cycle_key)
                                cyc = list(path)
                                ec = check_ec(cyc, new_word, n_val)
                                is_sw = (is_uniform_sweep(new_word, n_val) or
                                         is_generalized_sweep(new_word, n_val))
                                if ec:
                                    inc_ec += 1
                                elif is_sw:
                                    inc_noec_sweep += 1
                                else:
                                    inc_noec_nonsweep += 1
                                    fc = Counter(new_word)
                                    if inc_noec_nonsweep <= 3:
                                        print(f"  CE: bp={bp}, ms={ms}, "
                                              f"CL={len(new_word)}, "
                                              f"fc={dict(sorted(fc.items()))}, "
                                              f"word={new_word}")
                        continue

                    if new_config not in set(path) and len(path) < max_cl:
                        stack.append((new_config, path + [new_config],
                                     new_word))

        print(f"  Inc-only: {inc_ec} EC, {inc_noec_sweep} sweep, "
              f"{inc_noec_nonsweep} non-sweep")
        if inc_noec_nonsweep == 0:
            print(f"  => INC-ONLY DREAM HOLDS at n={n_val}")
        else:
            print(f"  => INC-ONLY DREAM FAILS at n={n_val}")

    # n=9 with constructed words only (too large for exhaustive)
    print(f"\nn=9: tested in v2, ALL 43,712 cycles have EC (HOLDS)")
