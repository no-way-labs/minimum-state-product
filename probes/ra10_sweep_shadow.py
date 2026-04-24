#!/usr/bin/env python3
"""
RA10d: Check if sweep cycles with ≥3 binary are killed by shadow cycles.

Key finding from ra10c: these sweep cycles have NO entry conflict.
The proof must use a different mechanism. The Shadow Cycle Mirror Theorem
should apply — sweep → uniform sweep (from the codebase, this may be proved),
and uniform sweeps are WaterfallCycles that have shadow cycles.

Let's verify:
1. Are all these sweep cycles uniform (all steps same direction)?
2. Do they satisfy WaterfallCycle conditions?
3. Can we construct the shadow cycle?
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


def is_uniform(word, n):
    """Check if all steps are in the same direction."""
    L = len(word)
    dirs = set()
    for i in range(L):
        nxt = word[(i + 1) % L]
        cur = word[i]
        diff = (nxt - cur) % n
        if diff == 1:
            dirs.add('CW')
        elif diff == n - 1:
            dirs.add('CCW')
    return len(dirs) == 1


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


def check_good_cycle_multi(word, ms, n):
    """Check good cycle with all transition combos."""
    L = len(word)
    wl = list(word)
    bins = {p for p in range(n) if ms[p] == 2}
    ternary = [p for p in range(n) if ms[p] == 3]
    n_tern = len(ternary)

    results = []
    for trans_bits in range(1 << n_tern):
        trans_dir = {}
        for p in bins:
            trans_dir[p] = 1
        for idx, p in enumerate(ternary):
            trans_dir[p] = 1 if not ((trans_bits >> idx) & 1) else -1

        configs = [[0] * n]
        for t in range(L):
            c = list(configs[-1])
            p = wl[t]
            c[p] = (c[p] + trans_dir[p]) % ms[p]
            configs.append(c)

        if configs[-1] != configs[0]:
            continue
        config_set = set(tuple(c) for c in configs[:L])
        if len(config_set) != L:
            continue
        results.append((trans_dir.copy(), configs[:L]))
    return results


def is_waterfall(word, n, configs):
    """Check if cycle satisfies MNU (Mover Non-repetition under Uniform sweep).
    In a uniform sweep, MNU means: no two mover steps at the same proc
    see the same boundary triple. Since binary fires exactly twice with
    different c[p] values, this is automatic at binary procs.
    At ternary procs (fire 3 times), need to check no two of the 3
    mover triples coincide."""
    L = len(word)
    wl = list(word)
    for p in range(n):
        positions = [t for t in range(L) if wl[t] == p]
        triples = set()
        for t in positions:
            c = tuple(configs[t])
            triple = (c[(p-1)%n], c[p], c[(p+1)%n])
            if triple in triples:
                return False, f"MNU fails at proc {p}"
            triples.add(triple)
    return True, "OK"


def construct_shadow(word, n, configs, ms):
    """Try to construct shadow cycle using the Shadow Cycle Mirror Theorem.
    For uniform CW sweep of length CL = sum(ms), shadow has length 2n.
    Shadow permutation: sigma(0)=n-4, sigma(1)=n-1, sigma(2)=0,
    sigma(k)=k-2 for 3<=k<=n-3, sigma(n-2)=n-2, sigma(n-1)=n-3.

    But this shadow was defined for specific ms. Let me just check
    if the cycle has a companion cycle (different config sequence using
    same word, same transition, with distinct configs disjoint from original).
    """
    # For sweep, the shadow approach constructs a second cycle
    # with the same mover word but different config sequence.
    # This is done by shifting the config assignment.
    # If the original cycle visits configs C, the shadow visits C'
    # where C ∩ C' = ∅, |C'| = |C|.
    # This means |C ∪ C'| = 2|C| = 2*CL configs needed.
    # Product of ms = available configs.
    # Need 2*CL ≤ product for shadow to fit.

    CL = len(word)
    product = 1
    for m in ms:
        product *= m

    return 2 * CL <= product, f"2*CL={2*CL}, product={product}"


def main():
    print("RA10d: Shadow Cycle Analysis for Sweep Cycles")
    print("=" * 70)

    for n in [7, 9]:
        threshold = 4 * (3 ** (n - 2))
        print(f"\n{'='*70}")
        print(f"n={n}, threshold={threshold}")
        print("=" * 70)

        for bin_combo in combinations(range(n), 3):
            bins_set = set(bin_combo)
            has_triple = any(i in bins_set and (i+1)%n in bins_set and (i+2)%n in bins_set for i in range(n))
            if has_triple:
                continue

            ms = [2 if p in bins_set else 3 for p in range(n)]
            product = 1
            for m in ms:
                product *= m
            if product >= threshold:
                continue

            words = enumerate_words_dfs(n, ms, max_results=2000, timeout=10)
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

            has_pair = any(i in bins_set and (i+1)%n in bins_set for i in range(n))
            adj_label = "adj" if has_pair else "nonadj"

            # Check uniformity
            n_uniform = sum(1 for w in sweep_words if is_uniform(list(w), n))

            print(f"\nbins={list(bin_combo)} [{adj_label}]: {len(sweep_words)} sweep words, {n_uniform} uniform")

            # For each sweep word + valid transition: check MNU and shadow
            for w in sweep_words[:2]:
                valid_cycles = check_good_cycle_multi(w, ms, n)
                for td, configs in valid_cycles[:2]:
                    uniform = is_uniform(list(w), n)
                    mnu_ok, mnu_msg = is_waterfall(list(w), n, configs)
                    shadow_ok, shadow_msg = construct_shadow(list(w), n, configs, ms)
                    disp = total_displacement(list(w), n)
                    print(f"  word start: {list(w)[:12]}... disp={disp}")
                    print(f"    uniform={uniform}, MNU={mnu_ok} ({mnu_msg})")
                    print(f"    shadow feasible: {shadow_ok} ({shadow_msg})")

    # KEY ANALYSIS: uniform sweep + sub-threshold → shadow exists → contradiction
    print(f"\n{'='*70}")
    print("KEY ANALYSIS: Can we prove sweep → uniform?")
    print("=" * 70)
    print("""
For the sweep case in CaseObstructions.lean, the proof structure is:

1. isSweep → |disp| ≥ 2n
2. Every proc fires ≥ 2 times
3. For binary proc: fc = 2 (must be even)

Now: is every sweep UNIFORM (all steps same direction)?
If disp = CL (all CW) or disp = -CL (all CCW), then yes, uniform.
For disp = 2n with CL = 3n-3 (3 binary): need CW - CCW = 2n, CW + CCW = 3n-3.
So CW = (5n-3)/2, CCW = (n-3)/2. Both must be non-negative integers.
(5n-3)/2 integer iff n is odd. (n-3)/2 ≥ 0 iff n ≥ 3.

For n=7: CW = 16, CCW = 2. CL = 18 = 16+2. Not uniform (has 2 CCW steps).
For n=9: CW = 21, CCW = 3. CL = 24 = 21+3. Not uniform (has 3 CCW steps).

Hmm, but wait - all our sweep words had |disp| = 2n. And they are NOT uniform.

Let me check: are they in fact |disp| = CL (fully uniform)?
""")

    # Check if sweep words are fully uniform or have |disp| = 2n exactly
    for n in [7, 9]:
        threshold = 4 * (3 ** (n - 2))
        for bin_combo in combinations(range(n), 3):
            bins_set = set(bin_combo)
            has_triple = any(i in bins_set and (i+1)%n in bins_set and (i+2)%n in bins_set for i in range(n))
            if has_triple:
                continue
            ms = [2 if p in bins_set else 3 for p in range(n)]
            product = 1
            for m in ms:
                product *= m
            if product >= threshold:
                continue

            words = enumerate_words_dfs(n, ms, max_results=2000, timeout=10)
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

            CL = sum(ms)
            disps = set()
            for w in sweep_words:
                d = total_displacement(list(w), n)
                disps.add(d)

            has_pair = any(i in bins_set and (i+1)%n in bins_set for i in range(n))
            print(f"  n={n} bins={list(bin_combo)} CL={CL}: sweep disps={sorted(disps)}, 2n={2*n}")

    # Now let's check: the shadow cycle theorem needs the cycle to be a
    # WaterfallCycle. A sweep that's not fully uniform still wraps ≥ 2n.
    # The shadow construction might still work.
    #
    # Actually, the KEY question is different. The proof currently says:
    # sweep → pick binary p → trichotomy → isolated → recurse.
    # But we've shown NO SWEEP has EC (so the trichotomy must give permanent or isolated).
    # permanent → disp=0 contradiction.
    # So ALL sweeps land in "isolated".
    #
    # The question is: can we close "isolated + sweep → False" directly?
    #
    # Alternative: DON'T go through the trichotomy at all.
    # Instead: sweep + sub-threshold → shadow cycle → contradiction.
    # The shadow cycle mirror theorem applies to sweep cycles directly.

    print(f"\n{'='*70}")
    print("SHADOW CYCLE CONSTRUCTION")
    print("=" * 70)

    # The shadow cycle mirror theorem: for any good cycle with ≥3 binary
    # (no triple) and uniform sweep, construct a companion cycle with
    # 2n distinct configs, all disjoint from the original.
    # Original has CL = 3n-k configs.
    # Shadow has 2n configs.
    # Total: CL + 2n = (3n-k) + 2n = 5n-k configs needed.
    # Available: product < 4*3^(n-2) (sub-threshold).
    # For k=3: need 5n-3 ≤ product. But product < 4*3^(n-2).
    # 4*3^(n-2) vs 5n-3: for n=7, 4*27=108 vs 32; for n=9, 4*243=972 vs 42.
    # Always 5n-3 << product. So there's room for the shadow.
    #
    # Wait, that's about configs, not the shadow construction itself.
    # The shadow theorem shows configs exist AND they form a valid good cycle.
    # But for converges: original good cycle + shadow good cycle = 2 cycles
    # in the system → contradicts convergence? No, convergence means the
    # system CONVERGES to the good cycle from any start. If there are 2
    # good cycles, some start config can't converge to both.
    # Actually: convergence in this context means "the system reaches a
    # good configuration from any start in finite steps", which requires
    # ALL configurations are either good or can reach a good config.
    # Two disjoint good cycles is fine for convergence.
    #
    # Hmm wait — what does "contradicts converges" mean here?
    # The shadow cycle theorem proves that the TOTAL number of good configs
    # is at least CL + 2n. If this exceeds the product of state sizes,
    # contradiction.

    # Let me re-examine. The shadow approach:
    # 1. Take the good cycle (CL configs)
    # 2. Construct shadow cycle (2n configs, disjoint from original)
    # 3. Total good configs ≥ CL + 2n
    # 4. Total configs = product of ms
    # 5. Need CL + 2n > product for contradiction
    # But CL = 3n-3 and product = 72 (n=5), so 12 + 10 = 22 ≤ 72. No contradiction!

    # The shadow obstruction works differently. Let me re-read the key result.
    # The shadow cycle is a valid good cycle if and only if no entry conflict
    # exists in the COMBINED set. The shadow IS valid for these sweep cycles.
    # But then convergence still works (two disjoint good cycles).
    #
    # Wait — I think the issue is that having a shadow cycle means the SYSTEM
    # cannot converge: from a config in the shadow cycle, the system would
    # cycle through the shadow, never reaching the original good cycle.
    # But convergence requires reaching THE good cycle. So if there's a second
    # good cycle (shadow), convergence fails.
    #
    # Actually: convergence in Dijkstra's model means "from ANY starting
    # config, the system eventually enters a legitimate (good) config."
    # If the shadow configs are all good, then convergence still holds —
    # any starting config reaches SOME good config.
    # The issue is UNIQUENESS: there should be only ONE maximal closed set
    # of good configs (one attractor). If there are two disjoint closed sets
    # (original cycle + shadow cycle), then the system is not self-stabilizing
    # in the sense that it might enter the "wrong" cycle.
    #
    # Hmm, I think I'm confusing things. Let me check what "converges" means
    # in the Lean code.

    print("\nNeed to check Lean definition of 'converges'...")
    print("In the paper: converges means there exists a UNIQUE good cycle")
    print("such that all configs eventually reach it.")
    print("If shadow cycle exists and is valid: two disjoint good cycles → ¬converges.")
    print()
    print("But actually the shadow might not close — it needs its own transition.")
    print("The shadow theorem constructs configs for a DIFFERENT good cycle")
    print("under the SAME system. If the system has two good cycles, it can't converge.")

    # Let me verify: do the sweep cycles actually produce disjoint shadow cycles?
    # For this I need to construct the shadow explicitly.

    print(f"\n{'='*70}")
    print("EXPLICIT SHADOW CONSTRUCTION")
    print("=" * 70)

    n = 9
    ms_test = [2, 3, 3, 2, 3, 3, 2, 3, 3]  # bins at {0,3,6}
    bins_set = {0, 3, 6}

    words = enumerate_words_dfs(n, ms_test, max_results=100, timeout=10)
    unique = {}
    for w in words:
        c = canonicalize(w)
        if c not in unique:
            unique[c] = w

    sweep_words = [w for w in unique.values()
                   if total_displacement(list(w), n) is not None
                   and abs(total_displacement(list(w), n)) >= 2 * n]

    print(f"ms={ms_test}, {len(sweep_words)} sweep words")

    for w in sweep_words[:2]:
        wl = list(w)
        CL = len(wl)
        disp = total_displacement(wl, n)
        print(f"\nword={wl}, disp={disp}")
        print(f"  CL={CL}, uniform={is_uniform(wl, n)}")

        # Detailed step analysis
        for i in range(CL):
            cur = wl[i]
            nxt = wl[(i+1) % CL]
            diff = (nxt - cur) % n
            direction = "CW" if diff == 1 else "CCW"
            print(f"  step {i:2d}: {cur} → {nxt} [{direction}]")


if __name__ == '__main__':
    main()
