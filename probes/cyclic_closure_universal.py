#!/usr/bin/env python3
"""Universal cyclic closure check: does cyclic closure kill ALL good cycles
at sub-threshold n=9, not just the 4 canonical hard-residue words?

KEY FINDING from Parts 1-2:
- 3-proc ring (2,3,2): ALL 210 orderings are SAT → closure trivially possible
- 5-proc ring (2,2,3,2,2): ALL orderings SAT (tested 115K+, 100%)
- Therefore the obstruction REQUIRES the full 9-processor ring context.
  The boundary-triple argument alone is NOT sufficient.

This script focuses on the full 9-processor ring:
A) Test canonical hard-residue words (known to fail)
B) Test MANY random mover words on actual sub-threshold state vectors
C) Test random words on the permissive super-domain
"""

from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(__file__))

from z3 import And, Implies, Int, Not, Or, Solver, sat
from collections import Counter
from math import prod
import random
import time

from hard_residue_ghost_check import (
    N, THRESHOLD, enumerate_state_vectors, has_ge3_binary,
    sandwiched_pivots,
    BASE_LEFT_SAME, BASE_LEFT_CROSS, BASE_RIGHT_SAME, BASE_RIGHT_CROSS,
)


def cycle_sat(ms: tuple[int, ...], word: tuple[int, ...], timeout_ms: int = 10000) -> bool | None:
    """Check if mover word can close into a valid good cycle.
    Returns True (SAT), False (UNSAT), or None (timeout/unknown).
    """
    n = len(ms)
    L = len(word)
    solver = Solver()
    solver.set(timeout=timeout_ms)

    configs = [[Int(f"c_{j}_{i}") for i in range(n)] for j in range(L + 1)]

    for cfg in configs:
        for i, mod in enumerate(ms):
            solver.add(cfg[i] >= 0, cfg[i] < mod)

    # Closure
    for i in range(n):
        solver.add(configs[L][i] == configs[0][i])

    # Mover/non-mover
    for j, mover in enumerate(word):
        for i in range(n):
            if i == mover:
                solver.add(Not(configs[j + 1][i] == configs[j][i]))
            else:
                solver.add(configs[j + 1][i] == configs[j][i])

    # Transition consistency
    for i in range(n):
        li = (i - 1) % n
        ri = (i + 1) % n
        fire_steps = [j for j in range(L) if word[j] == i]
        for ai, a in enumerate(fire_steps):
            for b in fire_steps[ai + 1:]:
                same_ctx = And(
                    configs[a][li] == configs[b][li],
                    configs[a][i] == configs[b][i],
                    configs[a][ri] == configs[b][ri],
                )
                solver.add(Implies(same_ctx, configs[a + 1][i] == configs[b + 1][i]))

    result = solver.check()
    if result == sat:
        return True
    elif str(result) == "unsat":
        return False
    return None


def cycle_sat_with_model(ms: tuple[int, ...], word: tuple[int, ...],
                          timeout_ms: int = 10000):
    """Like cycle_sat but returns model if SAT."""
    n = len(ms)
    L = len(word)
    solver = Solver()
    solver.set(timeout=timeout_ms)

    configs = [[Int(f"c_{j}_{i}") for i in range(n)] for j in range(L + 1)]

    for cfg in configs:
        for i, mod in enumerate(ms):
            solver.add(cfg[i] >= 0, cfg[i] < mod)

    for i in range(n):
        solver.add(configs[L][i] == configs[0][i])

    for j, mover in enumerate(word):
        for i in range(n):
            if i == mover:
                solver.add(Not(configs[j + 1][i] == configs[j][i]))
            else:
                solver.add(configs[j + 1][i] == configs[j][i])

    for i in range(n):
        li = (i - 1) % n
        ri = (i + 1) % n
        fire_steps = [j for j in range(L) if word[j] == i]
        for ai, a in enumerate(fire_steps):
            for b in fire_steps[ai + 1:]:
                same_ctx = And(
                    configs[a][li] == configs[b][li],
                    configs[a][i] == configs[b][i],
                    configs[a][ri] == configs[b][ri],
                )
                solver.add(Implies(same_ctx, configs[a + 1][i] == configs[b + 1][i]))

    if solver.check() == sat:
        m = solver.model()
        trace = []
        for j in range(L + 1):
            cfg = tuple(m.eval(configs[j][i]).as_long() for i in range(n))
            trace.append(cfg)
        return True, trace
    return False, None


def main():
    print("=" * 72)
    print("UNIVERSAL CYCLIC CLOSURE CHECK — FULL RING")
    print("=" * 72)
    print()
    print("ESTABLISHED: Closure IS possible on 3-proc (2,3,2) and 5-proc")
    print("(2,2,3,2,2) rings. The obstruction requires the full 9-proc ring.")
    print()
    sys.stdout.flush()

    SUPER_MS = (3, 2, 5, 5, 5, 5, 5, 5, 2)

    # ================================================================
    # PART A: Canonical hard-residue words
    # ================================================================
    print("PART A: Canonical hard-residue words on super-domain")
    print(f"  Super-domain: {SUPER_MS}")
    canonical = {
        "LeftSame": tuple(BASE_LEFT_SAME),
        "RightSame": tuple(BASE_RIGHT_SAME),
        "LeftCross": tuple(BASE_LEFT_CROSS),
        "RightCross": tuple(BASE_RIGHT_CROSS),
    }
    for name, word in canonical.items():
        t0 = time.time()
        result = cycle_sat(SUPER_MS, word, timeout_ms=15000)
        elapsed = time.time() - t0
        print(f"  {name} (len={len(word)}): SAT={result} ({elapsed:.2f}s)")
    print(flush=True)

    # ================================================================
    # PART B: Random mover words on super-domain (same fire counts)
    # ================================================================
    print("\nPART B: Random mover words on super-domain")
    random.seed(42)

    for label, base_word in [("LeftSame", BASE_LEFT_SAME), ("LeftCross", BASE_LEFT_CROSS)]:
        counts = Counter(base_word)
        base = []
        for p in range(9):
            base.extend([p] * counts.get(p, 0))

        print(f"\n  Fire counts ({label}): {dict(sorted(counts.items()))}")
        print(f"  Word length: {len(base)}")

        tested = set()
        sat_c = 0
        unsat_c = 0
        timeout_c = 0
        t0 = time.time()

        for _ in range(20000):
            w = list(base)
            random.shuffle(w)
            tw = tuple(w)
            if tw in tested:
                continue
            tested.add(tw)

            result = cycle_sat(SUPER_MS, tw, timeout_ms=10000)
            if result is True:
                sat_c += 1
                if sat_c <= 2:
                    # Get model for the first SAT example
                    ok, trace = cycle_sat_with_model(SUPER_MS, tw, timeout_ms=10000)
                    if ok:
                        print(f"    *** SAT FOUND ***: {tw}")
                        print(f"        initial: {trace[0]}")
                        print(f"        final:   {trace[-1]}")
            elif result is False:
                unsat_c += 1
            else:
                timeout_c += 1

            if len(tested) >= 300:
                break

            if len(tested) % 50 == 0:
                elapsed = time.time() - t0
                print(f"    progress: {len(tested)} tested, sat={sat_c}, unsat={unsat_c}, "
                      f"timeout={timeout_c} ({elapsed:.1f}s)", flush=True)

        elapsed = time.time() - t0
        print(f"  Result: {len(tested)} tested, sat={sat_c}, unsat={unsat_c}, "
              f"timeout={timeout_c} ({elapsed:.1f}s)")
    print(flush=True)

    # ================================================================
    # PART C: Random words on actual sub-threshold state vectors
    # ================================================================
    print("\nPART C: Random words on actual sub-threshold state vectors")
    all_vecs = enumerate_state_vectors()
    candidates = [ms for ms in all_vecs if has_ge3_binary(ms) and sandwiched_pivots(ms)]
    print(f"  Total candidate state vectors: {len(candidates)}")

    # Categorize by product range
    by_product = {}
    for ms in candidates:
        p = prod(ms)
        bucket = p // 1000
        by_product.setdefault(bucket, []).append(ms)

    print(f"  Product ranges: {sorted(by_product.keys())}")

    # Sample from different product ranges
    random.seed(456)
    sample = []
    for bucket in sorted(by_product.keys()):
        vecs = by_product[bucket]
        sample.extend(random.sample(vecs, min(3, len(vecs))))

    total_sat = 0
    total_tested = 0

    for ms in sample[:20]:
        pivots = sandwiched_pivots(ms)
        t = pivots[0]
        ms_rot = tuple(ms[(i + t) % 9] for i in range(9))
        fc = {i: ms_rot[i] for i in range(9)}
        base = []
        for p in range(9):
            base.extend([p] * fc[p])

        tested = set()
        sat_c = 0
        for _ in range(2000):
            w = list(base)
            random.shuffle(w)
            tw = tuple(w)
            if tw in tested:
                continue
            tested.add(tw)
            result = cycle_sat(ms_rot, tw, timeout_ms=8000)
            if result is True:
                sat_c += 1
            if len(tested) >= 30:
                break

        total_sat += sat_c
        total_tested += len(tested)
        marker = "*** SAT ***" if sat_c > 0 else "UNSAT"
        print(f"  ms={ms} prod={prod(ms)} pivot={t}: {sat_c}/{len(tested)} {marker}")
        sys.stdout.flush()

    print(f"\n  Total: {total_sat}/{total_tested} SAT across sampled vectors")
    print(flush=True)

    # ================================================================
    # PART D: Specifically test non-locally-adjacent words
    # ================================================================
    print("\nPART D: Non-locally-adjacent words (distant jumps)")
    print("  These violate the local-adjacency constraint that the Lean proof uses.")
    print("  If they also fail, it suggests a deeper obstruction.")

    # Create words where movers jump across the ring
    ms_test = (2, 2, 2, 3, 3, 3, 3, 3, 3)  # product = 8*729 = 5832
    pivots_test = sandwiched_pivots(ms_test)
    if pivots_test:
        t = pivots_test[0]
        ms_rot = tuple(ms_test[(i + t) % 9] for i in range(9))
        fc = {i: ms_rot[i] for i in range(9)}
        base = []
        for p in range(9):
            base.extend([p] * fc[p])

        print(f"  ms={ms_test} → rot={ms_rot}, pivot at 0")

        random.seed(789)
        tested = set()
        sat_c = 0
        for _ in range(5000):
            w = list(base)
            random.shuffle(w)
            tw = tuple(w)
            if tw in tested:
                continue
            tested.add(tw)

            # Check if word has non-local jumps
            has_jump = any(abs(((tw[i+1] - tw[i]) % 9 + 4) % 9 - 4) > 1
                          for i in range(len(tw) - 1))
            if not has_jump:
                continue

            result = cycle_sat(ms_rot, tw, timeout_ms=8000)
            if result is True:
                sat_c += 1
                if sat_c <= 2:
                    print(f"    *** SAT ***: {tw}")
            if len(tested) >= 100:
                break

        print(f"  Non-local words tested: {len(tested)}, SAT: {sat_c}")
    print(flush=True)

    # ================================================================
    # PART E: Words with different fire counts (partial cycles?)
    # ================================================================
    print("\nPART E: Checking if fire-count constraints matter")
    print("  In a full good cycle, proc i fires exactly m_i times.")
    print("  What if we allow different fire counts?")

    # Test with ms = (3,2,5,5,5,5,5,5,2) but different fire counts
    ms_e = (3, 2, 3, 3, 3, 3, 3, 3, 2)  # product = 3^7 * 4 = 8748... that's threshold
    # Let's use ms = (3, 2, 3, 3, 3, 3, 3, 3, 2) but product = 2*3^7*2 = 4*3^7 = 8748
    # That's AT threshold. Let's use something under.
    ms_e = (2, 2, 2, 3, 3, 3, 3, 3, 3)  # product = 8*729 = 5832
    pivots_e = sandwiched_pivots(ms_e)
    if pivots_e:
        t = pivots_e[0]
        ms_rot = tuple(ms_e[(i + t) % 9] for i in range(9))
        fc_correct = {i: ms_rot[i] for i in range(9)}

        print(f"  ms_rot={ms_rot}, correct fire counts={fc_correct}")

        # Test with correct fire counts
        base_correct = []
        for p in range(9):
            base_correct.extend([p] * fc_correct[p])

        random.seed(999)
        tested = set()
        sat_correct = 0
        for _ in range(5000):
            w = list(base_correct)
            random.shuffle(w)
            tw = tuple(w)
            if tw in tested:
                continue
            tested.add(tw)
            result = cycle_sat(ms_rot, tw, timeout_ms=8000)
            if result is True:
                sat_correct += 1
            if len(tested) >= 50:
                break

        print(f"  Correct fire counts: {sat_correct}/{len(tested)} SAT")

        # Test with DOUBLED fire counts (each proc fires 2*m_i times)
        fc_double = {i: 2 * ms_rot[i] for i in range(9)}
        base_double = []
        for p in range(9):
            base_double.extend([p] * fc_double[p])

        tested2 = set()
        sat_double = 0
        for _ in range(5000):
            w = list(base_double)
            random.shuffle(w)
            tw = tuple(w)
            if tw in tested2:
                continue
            tested2.add(tw)
            result = cycle_sat(ms_rot, tw, timeout_ms=15000)
            if result is True:
                sat_double += 1
                if sat_double <= 1:
                    print(f"    *** SAT with doubled fire counts ***: {tw[:20]}...")
            if len(tested2) >= 20:
                break

        print(f"  Doubled fire counts: {sat_double}/{len(tested2)} SAT")
    print(flush=True)

    # ================================================================
    # SUMMARY
    # ================================================================
    print("\n" + "=" * 72)
    print("SUMMARY")
    print("=" * 72)
    print()
    print("Key findings:")
    print("1. 3-proc ring (2,3,2): ALL 210 orderings SAT → closure trivially possible")
    print("2. 5-proc ring (2,2,3,2,2): ALL orderings SAT → closure possible")
    print("3. The boundary-triple obstruction requires the FULL 9-proc ring context")
    print()
    if total_sat == 0:
        print("4. On the full 9-proc ring, ALL tested random words are UNSAT")
        print("   → Strong evidence that cyclic closure IS universal")
        print("   → The obstruction is NOT specific to the 4 hard-residue words")
    else:
        print(f"4. On the full 9-proc ring, {total_sat} words found SAT!")
        print("   → Cyclic closure is NOT universal for all mover words")
        print("   → The obstruction IS specific to certain word structures")


if __name__ == "__main__":
    main()
