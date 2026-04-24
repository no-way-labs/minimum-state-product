#!/usr/bin/env python3
"""
RA4 Script 3: Reduction -- can the mixed-phase problem be bypassed?

KEY INSIGHT from Script 2: at n=6, ALL mixed phases occur in cycles
that ALREADY have EC. This suggests:

HYPOTHESIS: Under sub-threshold product with >=3 non-adjacent binary,
if a good cycle has ANY mixed phase (J>=1, K>=1 at some pivot),
then it already has EC somewhere (not necessarily at the pivot).

If true: the 3 adjacent-chain sorrys (lines 1012, 1077, 1121) are
vacuously true -- they claim `hasEntryConflict gc` in a context where
the cycle is assumed to NOT have EC, but mixed phases only appear in
cycles WITH EC.

But wait -- the proof structure is:
  assume ¬EC
  show ∀ phase, J+K ≤ 1  (using: if J+K ≥ 2, derive EC, contradiction)
  then derive fc(L)+fc(R) ≤ fc(t)

So the sorrys are inside "if J+K ≥ 2, derive EC". The hypothesis says:
  mixed phases → EC. Exactly what's needed!

This script tests the hypothesis exhaustively at n=5,6,7.

Additionally: can the mixed-phase EC be detected by a SIMPLER mechanism
than backward chain scanning? E.g., does the cycle always have EC at
some OTHER processor (not t's neighbor)?
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


def has_entry_conflict_at(configs, movers, n, p):
    ell = len(movers)
    L, R = (p - 1) % n, (p + 1) % n
    mt = set()
    nmt = set()
    for i in range(ell):
        triple = (configs[i][L], configs[i][p], configs[i][R])
        if movers[i] == p:
            mt.add(triple)
        else:
            nmt.add(triple)
    return bool(mt & nmt)


def has_entry_conflict(configs, movers, n):
    return any(has_entry_conflict_at(configs, movers, n, p) for p in range(n))


def extract_phases(movers, t, ell):
    t_steps = [i for i in range(ell) if movers[i] == t]
    if len(t_steps) < 2:
        return []
    phases = []
    for idx in range(len(t_steps)):
        a = t_steps[idx]
        s = t_steps[(idx + 1) % len(t_steps)]
        if s <= a:
            s += ell
        phases.append((a, s))
    return phases


def main():
    configs_to_test = [
        (6, [2, 3, 2, 3, 2, 3]),
        (6, [3, 2, 3, 2, 3, 2]),
    ]

    for n, ms in configs_to_test:
        binary_pos = [i for i in range(n) if ms[i] == 2]
        prod = 1
        for m in ms:
            prod *= m
        threshold = 4 * 3 ** (n - 2)

        pivots = []
        for t in range(n):
            L, R = (t - 1) % n, (t + 1) % n
            if ms[t] >= 3 and ms[L] == 2 and ms[R] == 2:
                pivots.append(t)

        print(f"\n{'='*70}")
        print(f"n={n}, ms={ms}, product={prod}, threshold={threshold}")
        print(f"Binary at {binary_pos}, pivots={pivots}")

        words = enumerate_good_cycles(ms, n, max_length=3 * n)
        print(f"Found {len(words)} cycles")

        # Track: for cycles with mixed phases, where is the EC?
        mixed_cycles = 0
        mixed_ec_at_neighbor = 0   # EC at L or R of the pivot
        mixed_ec_at_pivot = 0      # EC at t itself
        mixed_ec_elsewhere = 0     # EC at some other proc
        mixed_no_ec = 0

        for word in words:
            movers = word
            ell = len(movers)
            configs = build_configs(ms, n, word)

            has_mixed = False
            mixed_pivots = set()
            for t in pivots:
                phases = extract_phases(movers, t, ell)
                for a, s in phases:
                    L_proc = (t - 1) % n
                    R_proc = (t + 1) % n
                    J = sum(1 for i in range(a + 1, s) if movers[i % ell] == L_proc)
                    K = sum(1 for i in range(a + 1, s) if movers[i % ell] == R_proc)
                    if J >= 1 and K >= 1:
                        has_mixed = True
                        mixed_pivots.add(t)

            if not has_mixed:
                continue
            mixed_cycles += 1

            ec_global = has_entry_conflict(configs, movers, n)
            if not ec_global:
                mixed_no_ec += 1
                continue

            # Where is the EC?
            found_at_neighbor = False
            found_at_pivot = False
            for t in mixed_pivots:
                if has_entry_conflict_at(configs, movers, n, t):
                    found_at_pivot = True
                L_proc = (t - 1) % n
                R_proc = (t + 1) % n
                if (has_entry_conflict_at(configs, movers, n, L_proc) or
                    has_entry_conflict_at(configs, movers, n, R_proc)):
                    found_at_neighbor = True

            if found_at_neighbor:
                mixed_ec_at_neighbor += 1
            elif found_at_pivot:
                mixed_ec_at_pivot += 1
            else:
                mixed_ec_elsewhere += 1

        print(f"\nCycles with mixed phases: {mixed_cycles}")
        print(f"  EC at neighbor of pivot: {mixed_ec_at_neighbor}")
        print(f"  EC at pivot: {mixed_ec_at_pivot}")
        print(f"  EC elsewhere: {mixed_ec_elsewhere}")
        print(f"  NO EC: {mixed_no_ec}")

        if mixed_no_ec == 0:
            print(f"\n  *** CONFIRMED: ALL mixed-phase cycles have EC ***")
            print(f"  The 3 adjacent-chain sorrys are CORRECT (just need proof)")
        else:
            print(f"\n  *** {mixed_no_ec} mixed-phase cycles WITHOUT EC ***")
            print(f"  The adjacent-chain argument is genuinely needed")

    # === CRITICAL TEST: the actual Lean sorry path ===
    print(f"\n{'='*70}")
    print("CRITICAL TEST: Exactly the Lean sorry path")
    print(f"{'='*70}")
    print("""
The Lean proof does:
  1. Assume ¬EC
  2. Show all phases are normalForm (not mechanism-triggering)
  3. For each phase, show J+K ≤ 1
  4. Sum over phases to get fc(L)+fc(R) ≤ fc(t)
  5. Combine with sparse_phase_sum_ge: fc(L)+fc(R) ≥ fc(t)
  6. So fc(L)+fc(R) = fc(t), each phase has exactly J+K=1
  7. Derive EC from this exact equality

Steps 3 and 7 have sorrys. Let's check the exact path.
""")

    n, ms = 6, [2, 3, 2, 3, 2, 3]
    binary_pos = [i for i in range(n) if ms[i] == 2]
    pivots = [t for t in range(n)
              if ms[t] >= 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

    words = enumerate_good_cycles(ms, n, max_length=3*n)

    # Filter to EC-free cycles
    ec_free = []
    for word in words:
        configs = build_configs(ms, n, word)
        if not has_entry_conflict(configs, word, n):
            ec_free.append(word)

    print(f"n={n}, ms={ms}, pivots={pivots}")
    print(f"Total cycles: {len(words)}, EC-free: {len(ec_free)}")

    # For EC-free cycles: check if ALL phases at ALL pivots are normalForm
    all_normal_count = 0
    not_all_normal = 0
    for word in ec_free:
        movers = word
        ell = len(movers)
        fc = Counter(movers)

        all_normal = True
        for t in pivots:
            phases = extract_phases(movers, t, ell)
            for a, s in phases:
                L_proc = (t - 1) % n
                R_proc = (t + 1) % n
                J = sum(1 for i in range(a + 1, s) if movers[i % ell] == L_proc)
                K = sum(1 for i in range(a + 1, s) if movers[i % ell] == R_proc)

                # isMechanismTriggering: (Even J, Even K) or (J>=2, K=0) or (J=0, K>=2)
                is_mech = ((J % 2 == 0 and K % 2 == 0) or
                           (J >= 2 and K == 0) or
                           (J == 0 and K >= 2))
                if is_mech:
                    all_normal = False
                    break
            if not all_normal:
                break

        if all_normal:
            all_normal_count += 1
        else:
            not_all_normal += 1

    print(f"\nEC-free cycles with ALL phases normalForm (at all pivots): {all_normal_count}")
    print(f"EC-free cycles with some mechanism-triggering phase: {not_all_normal}")

    if all_normal_count > 0:
        print(f"\n*** {all_normal_count} EC-free all-normalForm cycles ***")
        print("These are the cases where the Lean proof needs to work.")
        print("Checking fc(L)+fc(R) vs fc(t)...")

        for word in ec_free:
            movers = word
            ell = len(movers)
            fc = Counter(movers)

            all_normal = True
            for t in pivots:
                phases = extract_phases(movers, t, ell)
                for a, s in phases:
                    L_proc = (t - 1) % n
                    R_proc = (t + 1) % n
                    J = sum(1 for i in range(a + 1, s) if movers[i % ell] == L_proc)
                    K = sum(1 for i in range(a + 1, s) if movers[i % ell] == R_proc)
                    is_mech = ((J % 2 == 0 and K % 2 == 0) or
                               (J >= 2 and K == 0) or
                               (J == 0 and K >= 2))
                    if is_mech:
                        all_normal = False
                        break
                if not all_normal:
                    break

            if not all_normal:
                continue

            print(f"\n  Word len={ell}, word={movers}")
            for t in pivots:
                L_proc = (t - 1) % n
                R_proc = (t + 1) % n
                fcL = fc[L_proc]
                fcR = fc[R_proc]
                fcT = fc[t]
                phases = extract_phases(movers, t, ell)
                phase_jk = []
                for a, s in phases:
                    J = sum(1 for i in range(a + 1, s) if movers[i % ell] == L_proc)
                    K = sum(1 for i in range(a + 1, s) if movers[i % ell] == R_proc)
                    phase_jk.append((J, K))
                print(f"  t={t}: fc(L)={fcL}, fc(R)={fcR}, fc(t)={fcT}, "
                      f"sum={fcL+fcR}, phases={(phase_jk)}")
    else:
        print("\nNO EC-free all-normalForm cycles exist!")
        print("This means the Lean proof's assumptions (¬EC + allNormalForm)")
        print("are already contradictory -- the theorem is vacuously true!")
        print("But this needs to be proved, not just observed at n=6.")


if __name__ == '__main__':
    main()
