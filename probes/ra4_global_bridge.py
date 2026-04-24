#!/usr/bin/env python3
"""
RA4 Script 4: The global-local bridge + sorry strategy.

FINDINGS SO FAR (from Scripts 1-3):
- n=6: ALL 2232 cycles have EC. Zero EC-free cycles exist.
- ALL mixed phases occur in EC-bearing cycles.
- The assumption (¬EC + allNormalForm) is vacuously False at n=6.

This means the sorrys COULD potentially be closed by a different
approach entirely: prove that ¬EC is impossible at a higher level,
before even entering the phase analysis.

This script investigates:
1. Is the "all cycles have EC" result specific to n=6, or universal?
2. Does the existing Universal Entry Conflict theorem already give this?
3. What's the simplest path to close the sorrys?

The Universal Entry Conflict (BinSCC Expl 10) proves:
  For >=3 non-adjacent binary at sub-threshold product,
  EVERY good cycle has entry conflict.

If this is already formalized, then hasEntryConflict gc is always True,
so ¬hasEntryConflict gc is False, and sparse_phase_false is trivially True.

Let's check: what's the actual Lean proof path and where does
Universal EC get invoked?
"""
from collections import Counter


def enumerate_good_cycles(ms, n, max_length=None):
    if max_length is None:
        max_length = 4 * sum(ms)
    ring_adj = {p: [(p - 1) % n, (p + 1) % n] for p in range(n)}
    seen = set()
    results = []
    start = tuple(0 for _ in range(n))

    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= 2 * n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                w = tuple(word)
                best = w
                for i in range(len(w)):
                    rot = w[i:] + w[:i]
                    if rot < best:
                        best = rot
                if best not in seen:
                    seen.add(best)
                    results.append(list(best))
                return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n)
                     if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            nc = list(config)
            nc[nxt] = (nc[nxt] + 1) % ms[nxt]
            nf = list(fc)
            nf[nxt] += 1
            word.append(nxt)
            dfs(word, nf, tuple(nc))
            word.pop()

    for p in range(n):
        fc_init = list(start)
        fc_init[p] = (fc_init[p] + 1) % ms[p]
        dfs([p], [1 if i == p else 0 for i in range(n)], tuple(fc_init))
    return results


def build_configs(ms, n, word):
    configs = [tuple(0 for _ in range(n))]
    for i in range(len(word)):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    return configs[:len(word)]


def has_entry_conflict(configs, movers, n):
    ell = len(movers)
    for p in range(n):
        L, R = (p - 1) % n, (p + 1) % n
        mt, nmt = set(), set()
        for i in range(ell):
            triple = (configs[i][L], configs[i][p], configs[i][R])
            if movers[i] == p:
                mt.add(triple)
            else:
                nmt.add(triple)
        if mt & nmt:
            return True
    return False


def main():
    print("="*70)
    print("Universal Entry Conflict Check: do ALL cycles have EC?")
    print("="*70)

    # Test at n=5 with various configs
    test_cases = [
        # n=5, consecutive binary (Case 3a)
        (5, [2, 2, 2, 3, 3], "3 consec binary"),
        (5, [2, 3, 2, 3, 2], "alternating (0,2,4 binary; 0-4 adjacent)"),
        (5, [2, 2, 3, 3, 2], "binary at 0,1,4 (0-1 adj, 4-0 adj)"),
        # n=6
        (6, [2, 3, 2, 3, 2, 3], "alternating binary at 0,2,4"),
        # n=7
        (7, [3, 2, 3, 2, 3, 2, 3], "binary at 1,3,5 -- truly non-adjacent"),
    ]

    for n, ms, label in test_cases:
        binary_pos = [i for i in range(n) if ms[i] == 2]
        prod = 1
        for m in ms:
            prod *= m
        threshold = 4 * 3 ** (n - 2)

        print(f"\nn={n}, ms={ms} ({label})")
        print(f"  product={prod}, threshold={threshold}, sub={prod < threshold}")
        print(f"  binary at {binary_pos}")

        max_len = 3 * n if n <= 6 else 2 * n + 4
        print(f"  Enumerating (max len {max_len})...")
        words = enumerate_good_cycles(ms, n, max_length=max_len)
        print(f"  Found {len(words)} cycles")

        ec_count = 0
        noec_count = 0
        for word in words:
            configs = build_configs(ms, n, word)
            if has_entry_conflict(configs, word, n):
                ec_count += 1
            else:
                noec_count += 1

        print(f"  EC: {ec_count}, no-EC: {noec_count}")
        if noec_count == 0 and words:
            print(f"  *** ALL cycles have EC ***")
        elif noec_count > 0:
            print(f"  *** {noec_count} EC-free cycles exist ***")

    # === Analysis ===
    print(f"\n{'='*70}")
    print("ANALYSIS: Sorry closure strategy")
    print(f"{'='*70}")
    print("""
SORRY INVENTORY (AllNormalFormFalse2.lean):

Sorry 1-3 (lines 1012, 1077, 1121): Adjacent-chain backward scanning
  GOAL: show hasEntryConflict gc
  CONTEXT: ¬hasEntryConflict gc (assumed), mixed phase J>=1, K>=1,
           second-neighbor adjacent to first-neighbor fire

Sorry 4 (line 1129): Summation fc(L)+fc(R) <= fc(t)
  GOAL: derive from per-phase J+K <= 1
  CONTEXT: requires fire-count decomposition lemma

Sorry 5 (line 1172): Final EC derivation from fc equality
  GOAL: show hasEntryConflict gc
  CONTEXT: fc(L)+fc(R) = fc(t), all phases normalForm, ¬EC

CLOSURE STRATEGIES:

Strategy A: Close sorrys 1-3 directly (adjacent-chain proof)
  - Need: inductive backward scan showing chain terminates at EC
  - Difficulty: moderate (index arithmetic, ring topology)
  - Once 1-3 closed: sorry 4 is mechanical (fire-count decomposition)
  - Sorry 5 still needs: domino argument across phases

Strategy B: Bypass sparse_phase_false entirely
  - The Universal Entry Conflict theorem (BinSCC Expl 10) proves
    ALL good cycles have EC under the hypotheses.
  - If this is ALREADY formalized in Lean at a higher level,
    then ¬EC is False, and sparse_phase_false is trivially True.
  - Check: is UniversalEC formalized?

Strategy C: Prove mixed phase -> EC directly (without chain scanning)
  - Script 2 showed: ALL mixed phases occur in EC cycles.
  - Could prove: if a phase has J>=1, K>=1, then the GLOBAL cycle
    must have EC (via a simpler argument than backward scanning).
  - E.g.: mixed phase forces certain mover patterns that conflict
    with the binary parity constraint.

RECOMMENDATION:
  Check the Lean formalization to see if Universal EC is already
  available above sparse_phase_false. If so: the sorrys are
  closable by contradiction (¬EC is impossible).
  If not: Strategy A (close the adjacent chains one by one) is
  the most direct path, as each is a finite case analysis.
""")

    # Check the actual structure: what does the Lean proof assume?
    print(f"\n{'='*70}")
    print("PROOF STRUCTURE TRACE")
    print(f"{'='*70}")
    print("""
File: AllNormalFormFalse2.lean

sparse_phase_false
  Assumes: gc, ¬EC, allNormalForm, ternary pivot t with binary neighbors,
           all procs fire, fc(t) >= 2
  Goal: False

  Step 1: fc(L) >= 2, fc(R) >= 2
  Step 2: per-phase J+K <= 1 (SORRYS 1-3 for mixed case)
  Step 3: fc(L)+fc(R) <= fc(t) (SORRY 4: summation)
  Step 4: fc(t) >= 4 from Step 1
  Step 5: sparse_phase_sum_ge gives fc(L)+fc(R) >= fc(t)
  Step 6: fc(L)+fc(R) = fc(t), each phase has J+K = 1
  Step 7: derive EC (SORRY 5: domino argument)

allNormalForm_false2
  Assumes: gc, ¬EC, all larger assumptions
  Goal: False
  Delegates to sparse_phase_false after establishing pivot.

The key question: WHERE in the call chain does Universal EC get invoked?
Does it happen BEFORE or AFTER allNormalForm_false2?
""")


if __name__ == '__main__':
    main()
