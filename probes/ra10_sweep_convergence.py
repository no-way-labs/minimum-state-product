#!/usr/bin/env python3
"""
RA10f: Can the shadow/convergence argument kill sweep cycles directly?

The sweep cycles with ≥3 binary have:
- fc(p) = ms[p] for all p
- L = CL = 3n-k (k binary procs)
- |disp| = 2n
- 3 CCW wiggles (for 3 binary)
- MNU (mover non-repetition)
- NO entry conflict

The shadow cycle mirror theorem works for UNIFORM sweeps (L = 2n, all fc = 2).
These non-uniform sweeps need a different shadow construction.

KEY INSIGHT: Maybe we don't need a shadow at all. Maybe these sweep cycles
simply can't be part of a CONVERGING system because:
1. The transition function must be consistent with the good cycle
2. Under sub-threshold, the configs in the good cycle + liveness
   constraints force a contradiction

Let's check: for each sweep good cycle, try to BUILD a complete transition
function that produces exactly this good cycle, and check if the resulting
system converges.

If NO valid system with this good cycle converges → sweep + sub-threshold
+ ≥3 binary → ¬converges.
"""
from collections import defaultdict
from itertools import product as iproduct
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


def build_system_from_cycle(word, n, ms, configs):
    """Build transition function from good cycle.
    Returns the forced transitions (context → new_value) for each proc.
    Also returns free contexts (not constrained by cycle)."""
    L = len(word)
    wl = list(word)

    # For each proc p: at mover steps, f(L, S, R) determines new value S'.
    # At non-mover steps, f(L, S, R) = S (must not change).
    transitions = {}  # (proc, (L, S, R)) → new_S
    for p in range(n):
        transitions[p] = {}

    for t in range(L):
        c = tuple(configs[t])
        mover = wl[t]
        c_next = tuple(configs[(t + 1) % L])

        for p in range(n):
            L_val = c[(p - 1) % n]
            S_val = c[p]
            R_val = c[(p + 1) % n]
            ctx = (L_val, S_val, R_val)

            if p == mover:
                new_S = c_next[p]
                if ctx in transitions[p]:
                    if transitions[p][ctx] != new_S:
                        return None, None  # inconsistent!
                transitions[p][ctx] = new_S
            else:
                # Non-mover: f must return S (no change)
                if ctx in transitions[p]:
                    if transitions[p][ctx] != S_val:
                        return None, None  # inconsistent!
                transitions[p][ctx] = S_val

    # Count forced and free contexts
    total_contexts = {}
    free_contexts = {}
    for p in range(n):
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        all_ctx = [(l, s, r) for l in range(m_L) for s in range(m_S) for r in range(m_R)]
        total_contexts[p] = len(all_ctx)
        free = [ctx for ctx in all_ctx if ctx not in transitions[p]]
        free_contexts[p] = free

    return transitions, free_contexts


def check_convergence_simple(n, ms, transitions, configs_good, max_steps=1000):
    """Quick convergence check: from random non-good configs, does the system
    reach a good config within max_steps?
    Returns (converges, counter_example_if_not)."""
    good_set = set(tuple(c) for c in configs_good)

    # Need a complete transition function. For free contexts, use default (no change).
    complete_trans = {}
    for p in range(n):
        complete_trans[p] = dict(transitions[p])
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        for l in range(m_L):
            for s in range(m_S):
                for r in range(m_R):
                    ctx = (l, s, r)
                    if ctx not in complete_trans[p]:
                        complete_trans[p][ctx] = s  # default: no change

    # Check: from every config, can we reach a good config?
    product = 1
    for m in ms:
        product *= m

    # Enumerate all configs (for small product)
    if product > 10000:
        return None, "product too large"

    all_configs = [[]]
    for p in range(n):
        new_all = []
        for c in all_configs:
            for v in range(ms[p]):
                new_all.append(c + [v])
        all_configs = new_all

    # Check daemon-based convergence: from each config, does EVERY possible
    # execution reach a good config?
    # This is the self-stabilization check.
    # For now: just check if the good configs form a valid cycle under the
    # transition, and check if other configs have any path to good configs.

    # Simpler check: is the good cycle actually a valid attractor?
    # i.e., from configs in good_set, does the system stay in good_set?
    for c in configs_good:
        tc = tuple(c)
        # Find privileged procs (can fire)
        privileged = []
        for p in range(n):
            ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
            new_val = complete_trans[p][ctx]
            if new_val != c[p]:  # proc p is privileged
                privileged.append(p)

        if len(privileged) != 1:
            return False, f"Config {c} has {len(privileged)} privileged procs (need 1 for good cycle)"

    # Check from all non-good configs: at least one firing leads closer to good
    # (This is a simplification — full convergence check is hard)
    non_good_trapped = []
    for c in all_configs:
        tc = tuple(c)
        if tc in good_set:
            continue

        # Find privileged procs
        privileged = []
        for p in range(n):
            ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
            new_val = complete_trans[p][ctx]
            if new_val != c[p]:
                privileged.append(p)

        if len(privileged) == 0:
            non_good_trapped.append(c)

    return len(non_good_trapped) == 0, non_good_trapped


def main():
    print("RA10f: Sweep Cycle Convergence Analysis")
    print("=" * 70)

    # Test with n=7, bins=[0,3,6] (non-adjacent)
    # Wait, n=7 bins=[0,3,6]: 0 and 6 are adjacent on ring of 7!
    # (6+1)%7 = 0. So this has an adjacent pair.
    # Let me just use the first example from ra10d.

    n = 7
    ms = [2, 2, 3, 3, 2, 3, 3]  # bins at {0,1,4}
    bins_set = {0, 1, 4}

    words = enumerate_words_dfs(n, ms, max_results=100, timeout=10)
    unique = {}
    for w in words:
        c = canonicalize(w)
        if c not in unique:
            unique[c] = w

    sweep_words = [w for w in unique.values()
                   if total_displacement(list(w), n) is not None
                   and abs(total_displacement(list(w), n)) >= 2 * n]

    print(f"n={n}, ms={ms}, bins={sorted(bins_set)}")
    print(f"{len(sweep_words)} sweep words")

    # For each sweep word, try all transition combos, build system, check convergence
    ternary = [p for p in range(n) if ms[p] == 3]
    n_tern = len(ternary)

    for w in sweep_words[:2]:
        wl = list(w)
        L = len(wl)
        disp = total_displacement(wl, n)
        print(f"\nword={wl}, disp={disp}")

        for trans_bits in range(1 << n_tern):
            trans_dir = {}
            for p in bins_set:
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

            # Build system
            transitions, free_ctx = build_system_from_cycle(wl, n, ms, configs[:L])
            if transitions is None:
                print(f"  trans={trans_dir}: INCONSISTENT transitions")
                continue

            n_forced = sum(len(t) for t in transitions.values())
            n_free = sum(len(f) for f in free_ctx.values())
            print(f"  trans={trans_dir}: {n_forced} forced, {n_free} free contexts")

            # Check convergence
            converges, info = check_convergence_simple(n, ms, transitions, configs[:L])
            if converges is None:
                print(f"    convergence: skipped ({info})")
            elif converges:
                print(f"    *** CONVERGES — sweep cycle IS part of converging system! ***")
            else:
                if isinstance(info, list):
                    print(f"    does NOT converge: {len(info)} trapped non-good configs")
                    if info:
                        print(f"      example trapped: {info[0]}")
                else:
                    print(f"    does NOT converge: {info}")

            if trans_bits >= 3:  # just check first few combos
                break

    # OK the simple convergence check won't find the right answer because
    # we're using default transitions (no change) for free contexts.
    # The real question is: does ANY completion of the free contexts give convergence?
    # If not, then sweep + this cycle → ¬converges.
    #
    # This is equivalent to asking: can we complete the transition table
    # so that the system is self-stabilizing with this good cycle?
    #
    # That's computationally hard for large n. Let me try a different approach.

    print(f"\n{'='*70}")
    print("APPROACH: Shadow cycle for non-uniform sweep")
    print("=" * 70)

    # The key observation from the MEMORY.md entries:
    # - Shadow Cycle Mirror Theorem applies to UNIFORM sweep (WaterfallCycle)
    # - Wiggle Shadow Cycle applies to WIGGLE words
    # - These sweep cycles ARE wiggle cycles (they have single wiggles)!
    #
    # A "single-wiggle word" in CIC Expl 12-15 is a mover word that
    # goes mostly in one direction with occasional back-and-forth wiggles.
    # Our sweep words are exactly this pattern!
    #
    # From MEMORY.md:
    # "Wiggle Shadow Cycle (CIC Expl 12-13+15, PROVED SYMBOLICALLY):
    #  For single-wiggle words with ≥3 non-adjacent binary, shadow cycle
    #  of length L=2n+2. ALL 5 PROPERTIES PROVED."
    #
    # So the wiggle shadow cycle theorem should apply directly to these sweep words!
    # The shadow gives a companion cycle of length 2n+2, and combined with the
    # original cycle (length 3n-k), the total good configs exceed product.
    # Wait, is that the argument? Or does the shadow directly give ¬converges?

    print("""
KEY INSIGHT: The sweep cycles with ≥3 non-consecutive binary are exactly
"single-wiggle words" from the Wiggle Shadow Cycle theorem (CIC Expl 12-15).

The Wiggle Shadow Cycle theorem proves:
1. For single-wiggle words with ≥3 non-adjacent binary
2. Shadow cycle of length L = 2n+2 exists
3. All 5 shadow properties hold (closure, movers, distinctness, disjointness, escape)
4. Combined: a second disjoint good cycle exists → ¬converges

This means:
sweep + ≥3 non-adjacent binary + sub-threshold → ¬converges (via wiggle shadow)

The proof path would be:
1. Sweep → walk structure is "wiggle" (has ≥1 back-and-forth)
2. ≥3 non-adjacent binary → wiggle shadow cycle exists
3. Shadow cycle → second good cycle in the system
4. Two disjoint good cycles → ¬converges
5. Combined with hconv → False

This does NOT need to go through binary_ring_impossibility at all!
""")

    # Let me verify: do our sweep words satisfy the wiggle shadow cycle conditions?
    # The wiggle shadow needs: ≥3 non-adjacent binary, sub-threshold product.
    # The sweep words are the mover sequences.
    # Check: is each sweep word a "single-wiggle word"?

    print("Verifying sweep words are single-wiggle words:")
    for n_test in [7, 9]:
        threshold = 4 * (3 ** (n_test - 2))
        from itertools import combinations
        for bin_combo in combinations(range(n_test), 3):
            bins_set = set(bin_combo)
            has_triple = any(i in bins_set and (i+1)%n_test in bins_set and (i+2)%n_test in bins_set for i in range(n_test))
            if has_triple:
                continue
            # Skip if adjacent pair (focus on truly non-adjacent)
            has_pair = any(i in bins_set and (i+1)%n_test in bins_set for i in range(n_test))
            if has_pair:
                continue

            ms_t = [2 if p in bins_set else 3 for p in range(n_test)]
            product = 1
            for m in ms_t:
                product *= m
            if product >= threshold:
                continue

            words = enumerate_words_dfs(n_test, ms_t, max_results=100, timeout=5)
            unique = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique:
                    unique[c] = w

            for w in unique.values():
                d = total_displacement(list(w), n_test)
                if d is None or abs(d) < 2 * n_test:
                    continue

                wl = list(w)
                L = len(wl)
                # Count direction changes (wiggles)
                n_cw = 0
                n_ccw = 0
                wiggles = 0
                for i in range(L):
                    nxt = wl[(i+1)%L]
                    cur = wl[i]
                    diff = (nxt - cur) % n_test
                    if diff == 1:
                        n_cw += 1
                    else:
                        n_ccw += 1

                # A "single-wiggle" word has the form:
                # CW CW ... CW CCW CW CW ... CW CCW CW ... CW CCW CW ...
                # Each "CCW" is isolated (surrounded by CW steps)
                prev_dir = None
                dir_changes = 0
                for i in range(L):
                    nxt = wl[(i+1)%L]
                    cur = wl[i]
                    diff = (nxt - cur) % n_test
                    d_i = 1 if diff == 1 else -1
                    if prev_dir is not None and d_i != prev_dir:
                        dir_changes += 1
                    prev_dir = d_i

                # Check: is each CCW step isolated (preceded and followed by CW)?
                isolated_ccw = True
                for i in range(L):
                    nxt = wl[(i+1)%L]
                    cur = wl[i]
                    diff = (nxt - cur) % n_test
                    if diff == n_test - 1:  # CCW step
                        # Check prev and next
                        prev_nxt = wl[i]
                        prev_cur = wl[(i-1)%L]
                        prev_diff = (prev_nxt - prev_cur) % n_test
                        next_nxt = wl[(i+2)%L]
                        next_cur = wl[(i+1)%L]
                        next_diff = (next_nxt - next_cur) % n_test
                        if prev_diff != 1 or next_diff != 1:
                            isolated_ccw = False

                print(f"  n={n_test} bins={list(bin_combo)}: CW={n_cw} CCW={n_ccw} "
                      f"dir_changes={dir_changes} isolated_CCW={isolated_ccw}")
                break  # just first sweep word per config

    # SUMMARY: What is the proposed proof?
    print(f"\n{'='*70}")
    print("PROPOSED PROOF SKETCH")
    print("=" * 70)
    print("""
Theorem: sweep + sub-threshold + ≥3 non-consecutive binary → False

PROOF (direct, no recursion):

Case 1: ≥3 consecutive binary (threeConsecutiveBinary exists)
  → Already handled by consecutive_binary_isolated_false (sorry-free)

Case 2: ≥3 binary, no triple (the problematic case)
  Sub-case 2a: uniformDirection
    → uniformDirection + binary + ternary → fireCount constant
    → But binary fc=2, ternary fc=3. Contradiction.
    → So sweep + mixed state sizes → ¬uniformDirection.
    → This sub-case is vacuously true.

  Sub-case 2b: ¬uniformDirection (the actual case)
    → The walk has both CW and CCW steps.
    → Sweep (|disp| ≥ 2n) with CL = 3n-k steps.
    → CCW steps = (CL - |disp|)/2 ≤ (3n-k - 2n)/2 = (n-k)/2.
    → Each CCW step is "isolated" (surrounded by CW steps).
    → The walk is a "wiggle word" with ≤ (n-3)/2 wiggles.

    APPROACH A: Apply the Wiggle Shadow Cycle theorem directly.
    This gives a second good cycle → ¬converges → False.
    Requires: the wiggle shadow construction works for sweep-type wiggles.

    APPROACH B: Observe that sweep → ¬zeroWinding → no safe processor.
    Then use the existing MNU + Universal Escape argument on the sweep
    walk to construct a shadow. The shadow disjointness comes from
    the binary parity structure.

    APPROACH C (simplest): Note that sweep + non-consecutive binary
    forces |disp| = 2n exactly (data shows this). Then:
    - CW = (CL + 2n)/2 = (5n-k)/2
    - CCW = (CL - 2n)/2 = (n-k)/2
    This is a "nearly uniform" walk. The wiggles are exactly at the
    positions where the walk needs to "compensate" for binary procs
    firing fewer times. Each wiggle adds one extra mover step at a
    ternary proc (who fires 3x instead of 2x).

    Can we extract a uniform 2n-cycle as a "quotient" of the 3n-k cycle?
    If we remove the (n-k)/2 wiggle pairs (CCW then CW), we get a
    uniform CW walk of length CL - 2*(n-k)/2 = CL - (n-k) = 3n-k-(n-k) = 2n.
    This is a uniform CW walk of length 2n!
    Apply the shadow theorem to this extracted 2n-walk.

    Key question: does the extracted 2n-walk form a valid good cycle?
    Probably NOT (different configs). But maybe we can build the shadow
    directly from the original cycle by "skipping" the wiggle steps.

RECOMMENDED: Approach C seems most promising. Check computationally
whether removing wiggles gives a valid 2n-cycle with shadow.
""")


if __name__ == '__main__':
    main()
