#!/usr/bin/env python3
"""
RA12b: Deep analysis of union MNU failure.

Union MNU fails 100%: the original and flipped cycles CANNOT coexist
under the same transition function. This means the binary flip argument
needs refinement.

Key question: At a binary proc p that is flipped, p fires at ms[p]=2 steps.
In the original cycle, p sees contexts (L1,0,R1)->(fire to 1) and (L2,1,R2)->(fire to 0).
In the companion, p sees contexts (L1',1,R1')->(fire to 0) and (L2',0,R2')->(fire to 1).

If (L1',1,R1') appears as a non-mover context in the original, then union MNU fails:
the system's f_p would need to map it to both 1 (non-mover, don't fire) and 0 (mover, fire).

Let's understand exactly which triples conflict and whether this is fundamental.

REVISED ARGUMENT STRATEGY:
If binary flip doesn't give two cycles in the SAME system, what does it give?
The companion cycle is a valid good cycle for a DIFFERENT system.
This alone doesn't prove non-convergence.

But maybe: the original cycle + flip = entry conflict?
Or: the flip shows that the system's transition function has a specific structure
that forces non-convergence through another mechanism?

Or simply: the binary flip argument is the WRONG approach for this sorry,
and we should use shadow cycle or entry conflict instead.
"""
from collections import defaultdict
from itertools import combinations
import time


def total_displacement(word, n):
    disp = 0
    L = len(word)
    for i in range(L):
        nxt = word[(i + 1) % L]
        cur = word[i]
        diff = (nxt - cur) % n
        if diff == 1:
            disp += 1
        elif diff == n - 1:
            disp -= 1
        else:
            return None
    return disp


def enumerate_words_dfs(n, ms, max_results=5000, timeout=60):
    target_cl = sum(ms)
    results = []
    t0 = time.time()
    def dfs(word, fc):
        if time.time() - t0 > timeout or len(results) >= max_results:
            return
        if len(word) == target_cl:
            if all(fc[p] == ms[p] for p in range(n)):
                diff = (word[0] - word[-1]) % n
                if diff in (1, n - 1):
                    results.append(tuple(word))
            return
        remaining = target_cl - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n))
        if needed > remaining:
            return
        last = word[-1]
        for nxt in [(last + 1) % n, (last - 1) % n]:
            if fc[nxt] < ms[nxt]:
                fc[nxt] += 1
                word.append(nxt)
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1
    for start in range(n):
        if time.time() - t0 > timeout or len(results) >= max_results:
            break
        fc = [0] * n
        fc[start] = 1
        if fc[start] <= ms[start]:
            dfs([start], fc)
    return results


def canonicalize(word):
    L = len(word)
    best = word
    for i in range(L):
        rot = word[i:] + word[:i]
        if rot < best:
            best = rot
    return best


def find_nonadj_pair(bins_set, n):
    bin_list = sorted(bins_set)
    for b1, b2 in combinations(bin_list, 2):
        if (b2 - b1) % n != 1 and (b1 - b2) % n != 1:
            return (b1, b2)
    return None


def build_cycle_configs(word, n, ms, trans_dir):
    L = len(word)
    configs = [[0] * n]
    for t in range(L):
        c = list(configs[-1])
        p = word[t]
        c[p] = (c[p] + trans_dir[p]) % ms[p]
        configs.append(c)
    if configs[-1] != configs[0]:
        return None
    config_set = set(tuple(c) for c in configs[:L])
    if len(config_set) != L:
        return None
    return [tuple(c) for c in configs[:L]]


def flip_configs(configs, flip_set):
    return [tuple(1 - c[p] if p in flip_set else c[p] for p in range(len(c)))
            for c in configs]


def main():
    print("RA12b: Union MNU Failure Analysis")
    print("=" * 70)

    # Detailed analysis at n=7, first example
    n = 7
    threshold = 4 * (3 ** (n - 2))

    for bin_combo in combinations(range(n), 3):
        bins_set = set(bin_combo)
        has_triple = any(
            i in bins_set and (i + 1) % n in bins_set and (i + 2) % n in bins_set
            for i in range(n))
        if has_triple:
            continue
        ms = [2 if p in bins_set else 3 for p in range(n)]
        product = 1
        for m in ms:
            product *= m
        if product >= threshold:
            continue
        pair = find_nonadj_pair(bins_set, n)
        if pair is None:
            continue

        words = enumerate_words_dfs(n, ms, max_results=500, timeout=5)
        unique = {}
        for w in words:
            c = canonicalize(w)
            if c not in unique:
                unique[c] = w
        sweep_words = [w for w in unique.values()
                       if total_displacement(list(w), n) is not None
                       and abs(total_displacement(list(w), n)) >= 2 * n]
        if not sweep_words:
            continue

        ternary = [p for p in range(n) if ms[p] == 3]

        # Take first sweep word, first trans combo
        w = sweep_words[0]
        wl = list(w)
        L = len(wl)

        trans_dir = {p: 1 for p in bins_set}
        for p in ternary:
            trans_dir[p] = 1

        configs = build_cycle_configs(wl, n, ms, trans_dir)
        if configs is None:
            continue

        print(f"\nn={n}, ms={ms}, bins={list(bin_combo)}, pair={pair}")
        print(f"word={wl}, L={L}")
        print(f"First 5 configs:")
        for t in range(min(5, L)):
            print(f"  t={t}: {configs[t]} mover={wl[t]}")

        flip_set = set(pair)
        companion = flip_configs(configs, flip_set)

        print(f"\nFlipped configs (flip at {pair}):")
        for t in range(min(5, L)):
            print(f"  t={t}: {companion[t]} mover={wl[t]}")

        # Detailed MNU analysis at the flipped binary proc
        for p in sorted(pair):
            print(f"\n--- Proc {p} (binary, flipped) ---")
            print(f"  Neighbors: L={(p-1)%n} (ms={ms[(p-1)%n]}), R={(p+1)%n} (ms={ms[(p+1)%n]})")

            orig_mover = []
            orig_nonmover = []
            comp_mover = []
            comp_nonmover = []

            for t in range(L):
                # Original
                Li = configs[t][(p - 1) % n]
                Si = configs[t][p]
                Ri = configs[t][(p + 1) % n]
                if wl[t] == p:
                    orig_mover.append((Li, Si, Ri, t))
                else:
                    orig_nonmover.append((Li, Si, Ri, t))
                # Companion
                Li2 = companion[t][(p - 1) % n]
                Si2 = companion[t][p]
                Ri2 = companion[t][(p + 1) % n]
                if wl[t] == p:
                    comp_mover.append((Li2, Si2, Ri2, t))
                else:
                    comp_nonmover.append((Li2, Si2, Ri2, t))

            print(f"  Original mover triples: {[(L,S,R) for L,S,R,t in orig_mover]}")
            print(f"  Original nonmover triples: {set((L,S,R) for L,S,R,t in orig_nonmover)}")
            print(f"  Companion mover triples: {[(L,S,R) for L,S,R,t in comp_mover]}")
            print(f"  Companion nonmover triples: {set((L,S,R) for L,S,R,t in comp_nonmover)}")

            # Union analysis
            all_mover = set((L, S, R) for L, S, R, t in orig_mover + comp_mover)
            all_nonmover = set((L, S, R) for L, S, R, t in orig_nonmover + comp_nonmover)
            conflict = all_mover & all_nonmover
            print(f"  Union mover: {all_mover}")
            print(f"  Union nonmover: {len(all_nonmover)} triples")
            print(f"  CONFLICT: {conflict}")

            if conflict:
                # Show the conflicting steps
                for tri in conflict:
                    print(f"\n  Triple {tri} appears as:")
                    for L2, S2, R2, t2 in orig_mover:
                        if (L2, S2, R2) == tri:
                            print(f"    Original MOVER at t={t2}: config={configs[t2]}")
                    for L2, S2, R2, t2 in orig_nonmover:
                        if (L2, S2, R2) == tri:
                            print(f"    Original NONMOVER at t={t2}: config={configs[t2]}")
                    for L2, S2, R2, t2 in comp_mover:
                        if (L2, S2, R2) == tri:
                            print(f"    Companion MOVER at t={t2}: config={companion[t2]}")
                    for L2, S2, R2, t2 in comp_nonmover:
                        if (L2, S2, R2) == tri:
                            print(f"    Companion NONMOVER at t={t2}: config={companion[t2]}")

        # Only analyze first example
        break

    # ─────────────────────────────────────────────────────────────────
    # Key insight: the union MNU failure is at the FLIPPED binary procs
    # ─────────────────────────────────────────────────────────────────

    print(f"\n{'='*70}")
    print("ANALYSIS: Where does union MNU fail?")
    print("=" * 70)

    fail_at_flipped = 0
    fail_at_nonflipped = 0
    fail_at_ternary = 0
    total_failures = 0

    for n in [7]:
        threshold = 4 * (3 ** (n - 2))
        for bin_combo in combinations(range(n), 3):
            bins_set = set(bin_combo)
            has_triple = any(
                i in bins_set and (i + 1) % n in bins_set and (i + 2) % n in bins_set
                for i in range(n))
            if has_triple:
                continue
            ms = [2 if p in bins_set else 3 for p in range(n)]
            product = 1
            for m in ms:
                product *= m
            if product >= threshold:
                continue
            pair = find_nonadj_pair(bins_set, n)
            if pair is None:
                continue
            words = enumerate_words_dfs(n, ms, max_results=500, timeout=5)
            unique = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique:
                    unique[c] = w
            sweep_words = [w for w in unique.values()
                           if total_displacement(list(w), n) is not None
                           and abs(total_displacement(list(w), n)) >= 2 * n]
            if not sweep_words:
                continue
            ternary = [p for p in range(n) if ms[p] == 3]
            flip_set = set(pair)
            for w in sweep_words[:5]:
                wl = list(w)
                L = len(wl)
                for trans_bits in range(1 << len(ternary)):
                    trans_dir_map = {p: 1 for p in bins_set}
                    for idx, p in enumerate(ternary):
                        trans_dir_map[p] = 1 if not ((trans_bits >> idx) & 1) else -1
                    configs = build_cycle_configs(wl, n, ms, trans_dir_map)
                    if configs is None:
                        continue
                    companion = flip_configs(configs, flip_set)

                    for p in range(n):
                        mover_triples = set()
                        nonmover_triples = set()
                        for cycle_configs in [configs, companion]:
                            for t in range(L):
                                Li = cycle_configs[t][(p - 1) % n]
                                Si = cycle_configs[t][p]
                                Ri = cycle_configs[t][(p + 1) % n]
                                triple = (Li, Si, Ri)
                                if wl[t] == p:
                                    mover_triples.add(triple)
                                else:
                                    nonmover_triples.add(triple)
                        if mover_triples & nonmover_triples:
                            total_failures += 1
                            if p in flip_set:
                                fail_at_flipped += 1
                            elif p in bins_set:
                                fail_at_nonflipped += 1
                            else:
                                fail_at_ternary += 1

    print(f"  Total union MNU failures: {total_failures}")
    print(f"  At flipped binary procs: {fail_at_flipped}")
    print(f"  At non-flipped binary procs: {fail_at_nonflipped}")
    print(f"  At ternary procs: {fail_at_ternary}")

    # ─────────────────────────────────────────────────────────────────
    # Understand the mechanism: binary proc sees all 4 possible (S,neighbor) combos
    # ─────────────────────────────────────────────────────────────────

    print(f"\n{'='*70}")
    print("WHY Union MNU Must Fail at Binary Procs")
    print("=" * 70)

    print("""
A binary proc p with ms[p]=2 fires exactly 2 times in the cycle.
Its mover triples are 2 triples where S changes (0->1 or 1->0).

In the ORIGINAL cycle, p's mover triples have S=0 (fire to 1) and S=1 (fire to 0).
In the COMPANION cycle (p flipped), p's mover triples have S=1 and S=0.

So the union of mover triples has both S=0 and S=1 triples.
The nonmover triples also have both S=0 and S=1.

For a binary proc with small neighbor state counts, the total number of
possible triples is M_L * 2 * M_R. The mover triples from the union are 4
(2 original + 2 companion, potentially overlapping). The nonmover triples
from the union can be up to 2*(L-2) unique triples.

If M_L * M_R is small (e.g., both neighbors are binary: 2*2=4 possible
triples per S value, 8 total), then 4 mover triples + many nonmover
triples must fit in 8 slots without overlap. With L = sum(ms) ~ 2n+1,
nonmover count ~ 2(2n+1-2) = 4n-2, this WILL have collisions.

For binary p with binary neighbor(s), the triple space is tiny:
  If L-neighbor is binary, R-neighbor is ternary: 2 * 2 * 3 = 12 triples total
  Original mover: 2 triples (S=0,1)
  Companion mover: 2 triples (S=1,0) — same S values, possibly different L,R
  Union mover: up to 4 triples
  Nonmover: up to 2*(L-2) entries, covering many of the 12 possible triples

  The original cycle's mover triple at S=0 has some (L,0,R).
  The companion's nonmover triples include configs where p has S=0 (those steps
  where p is not flipped... wait, p IS flipped. So companion S values are inverted.

  Actually: in companion, at steps where p doesn't fire, p's value is 1-original.
  So if original has nonmover triple (L,S,R) at step t, companion has (L',1-S,R').
  The companion's nonmover triple (L',1-S,R') at S-slot = 1-S.

  Original mover at step t: (L,0,R) -> fire to 1. Companion mover: (L',1,R') -> fire to 0.
  Original nonmover at step t: (L,S,R), companion nonmover: (L',1-S,R').

  Union mover S=0 triples: from original.
  Union mover S=1 triples: from original AND companion.
  Union nonmover S=0 triples: from companion (which has 1-1=0 at originally-S=1 nonmover steps).
  Union nonmover S=1 triples: from companion (which has 1-0=1 at originally-S=0 nonmover steps).

  Conflict happens when a mover triple from original (L,0,R) equals a nonmover
  triple from companion. Companion nonmover triples at S=0 come from original
  steps where S=1 and p is nonmover. After flip, these become (L', 0, R') where
  L'=flip(L) if L-neighbor is flipped, else L.

  If L-neighbor is NOT flipped and R-neighbor is NOT flipped:
    Companion nonmover (L, 1-S, R) at originally-(L, S, R) step.
    So companion nonmover at S=0 slot: (L, 0, R) from original (L, 1, R) steps.
    Original mover at S=0: (L_m, 0, R_m).
    If (L_m, 0, R_m) = (L_nm, 0, R_nm) where nm is a nonmover step with S=1:
    then L_m = L_nm and R_m = R_nm.
    This means: at step t_m (mover), config has (L_m, 0, R_m).
    At step t_nm (nonmover, S=1), config has (L_m, 1, R_m).
    These are two configs that differ ONLY at p. They exist iff
    the cycle passes through both (L_m, 0, R_m) and (L_m, 1, R_m) at proc p.
    For a sweep cycle, this is almost guaranteed: the cycle visits
    both S=0 and S=1 for proc p, and if the neighbors happen to have
    the same values at both visits... which they will if the sweep
    passes p while neighbors are in certain phases.

CONCLUSION:
  Union MNU failure is INHERENT for binary procs that are flipped.
  The flip creates companion cycles that cannot coexist with the original
  under the same transition function.

  This means: binary flip does NOT directly prove non-convergence of a
  specific system. It shows that the CONFIG SEQUENCE has a companion,
  but not that the SAME SYSTEM has two good cycles.

  For the lower bound proof, we need a DIFFERENT argument for sweep cycles
  with non-consecutive binary. The shadow cycle and entry conflict approaches
  are the correct tools.
""")

    # ─────────────────────────────────────────────────────────────────
    # Check: does the original cycle ALONE already have entry conflict?
    # ─────────────────────────────────────────────────────────────────

    print("=" * 70)
    print("ALTERNATIVE: Do these sweep cycles have entry conflict or shadow?")
    print("=" * 70)

    ec_total = 0
    ec_yes = 0
    shadow_total = 0
    shadow_yes = 0

    for n in [7]:
        threshold = 4 * (3 ** (n - 2))
        for bin_combo in combinations(range(n), 3):
            bins_set = set(bin_combo)
            has_triple = any(
                i in bins_set and (i + 1) % n in bins_set and (i + 2) % n in bins_set
                for i in range(n))
            if has_triple:
                continue
            ms = [2 if p in bins_set else 3 for p in range(n)]
            product = 1
            for m in ms:
                product *= m
            if product >= threshold:
                continue
            pair = find_nonadj_pair(bins_set, n)
            if pair is None:
                continue

            words = enumerate_words_dfs(n, ms, max_results=500, timeout=5)
            unique = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique:
                    unique[c] = w
            sweep_words = [w for w in unique.values()
                           if total_displacement(list(w), n) is not None
                           and abs(total_displacement(list(w), n)) >= 2 * n]
            if not sweep_words:
                continue
            ternary = [p for p in range(n) if ms[p] == 3]

            for w in sweep_words[:10]:
                wl = list(w)
                L = len(wl)
                for trans_bits in range(1 << len(ternary)):
                    trans_dir_map = {p: 1 for p in bins_set}
                    for idx, p in enumerate(ternary):
                        trans_dir_map[p] = 1 if not ((trans_bits >> idx) & 1) else -1
                    configs = build_cycle_configs(wl, n, ms, trans_dir_map)
                    if configs is None:
                        continue

                    # Entry conflict check
                    has_ec = False
                    for p in range(n):
                        mover_triples = set()
                        nonmover_triples = set()
                        for t in range(L):
                            Li = configs[t][(p - 1) % n]
                            Si = configs[t][p]
                            Ri = configs[t][(p + 1) % n]
                            triple = (Li, Si, Ri)
                            if wl[t] == p:
                                mover_triples.add(triple)
                            else:
                                nonmover_triples.add(triple)
                        if mover_triples & nonmover_triples:
                            has_ec = True
                            break

                    ec_total += 1
                    if has_ec:
                        ec_yes += 1

    print(f"  Entry conflict in ORIGINAL cycle: {ec_yes}/{ec_total}")
    if ec_yes == ec_total:
        print("  ALL original sweep cycles have entry conflict!")
        print("  Binary flip is UNNECESSARY — entry conflict already blocks these.")
    elif ec_yes == 0:
        print("  NO entry conflict in originals — need shadow or other argument.")
    else:
        print(f"  Mixed: {ec_yes} with EC, {ec_total - ec_yes} without.")

    print(f"\n{'='*70}")
    print("FINAL VERDICT")
    print("=" * 70)
    print("""
FINDING: Binary flip creates a valid companion cycle (same mover word,
valid transitions, distinct configs, disjoint from original). However,
union MNU fails 100%: the original and companion CANNOT be good cycles
of the SAME system.

IMPLICATION: The binary flip argument, as stated in RA10, is INCOMPLETE
for proving non-convergence. It proves that a disjoint good cycle EXISTS
(for some system with same ms), but not that the GIVEN system has two
good cycles.

FOR THE LEAN PROOF: The binary flip approach should be ABANDONED for
sorry 6. Instead, use one of:
  1. Entry conflict (if it applies to all sweep + non-consec binary cycles)
  2. Shadow cycle (which IS known to work for these cases)
  3. Universal Entry Conflict (BinSCC Expl 10, already proved analytically)

The correct proof strategy for sweep + non-consecutive binary is:
  - These fall under the Universal Entry Conflict theorem (BinSCC Expl 10)
  - Or the shadow cycle argument (CIC/BinSCC)
  - Binary flip is a red herring for formalization.
""")


if __name__ == '__main__':
    main()
