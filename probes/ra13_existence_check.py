#!/usr/bin/env python3
"""
ra13_existence_check.py — Definitive existence check: do odd-winding non-uniform
transition-consistent good cycles EXIST at n=5 with >=3 non-consecutive binary?

Two approaches:
1. Forward: for each word + starting config, DFS over all transition choices
2. Backward: enumerate ALL possible transition functions, find ALL good cycles,
   check if any are odd-winding non-uniform

Approach 2 is cleaner: enumerate systems, extract good cycles.
For n=5 with ms=[2,3,2,3,2], product=72, there are 72 configs total.
"""
import time
from itertools import combinations, product as iproduct
from collections import defaultdict


def total_displacement(word, n):
    W = 0
    L = len(word)
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 0:
            pass
        elif diff <= n // 2:
            W += diff
        else:
            W -= (n - diff)
    return W


def step_directions(word, n):
    L = len(word)
    dirs = []
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 0:
            dirs.append(0)
        elif diff == 1:
            dirs.append(1)
        elif diff == n - 1:
            dirs.append(-1)
        else:
            dirs.append(diff if diff <= n // 2 else diff - n)
    return dirs


def find_good_cycles_from_system(n, ms, trans_func, max_cl=None):
    """
    Given a transition function trans_func: (proc, L, S, R) -> new_S,
    find all good cycles by BFS from each config.

    A good cycle: sequence of configs c_0, c_1, ..., c_{L-1} where:
    - At each step t, exactly one proc p_t fires: c_{t+1} differs from c_t only at p_t
    - c_{t+1}[p_t] = trans_func(p_t, c_t[left(p_t)], c_t[p_t], c_t[right(p_t)])
    - c_{t+1}[p_t] != c_t[p_t]
    - Cycle: c_L = c_0
    - All configs distinct
    """
    if max_cl is None:
        max_cl = sum(ms) + 4

    all_configs = list(iproduct(*[range(m) for m in ms]))
    cycles = []

    for start in all_configs:
        # DFS from start config
        stack = [(start, [start], [])]  # (current_config, path, movers)
        while stack:
            cur, path, movers = stack.pop()
            if len(movers) >= max_cl:
                continue

            for mover in range(n):
                lp = (mover - 1) % n
                rp = (mover + 1) % n
                ctx = (mover, cur[lp], cur[mover], cur[rp])
                new_val = trans_func.get(ctx, None)
                if new_val is None:
                    continue
                if new_val == cur[mover]:
                    continue  # no change, not a valid fire

                nc = list(cur)
                nc[mover] = new_val
                nc_t = tuple(nc)

                if nc_t == start and len(movers) >= 2:
                    # Found a cycle
                    cycles.append((list(path), movers + [mover]))
                elif nc_t not in set(path) and len(movers) < max_cl - 1:
                    stack.append((nc_t, path + [nc_t], movers + [mover]))

    return cycles


def main():
    print("RA13 Existence Check: Do odd-winding non-uniform cycles exist?")
    print("=" * 70)

    n = 5
    ms = [2, 3, 2, 3, 2]
    threshold = 4 * (3 ** (n - 2))
    prod = 1
    for m in ms:
        prod *= m
    print(f"n={n}, ms={ms}, prod={prod}, threshold={threshold}")
    print(f"Sub-threshold: {prod < threshold}")

    binary_procs = [p for p in range(n) if ms[p] == 2]
    ternary_procs = [p for p in range(n) if ms[p] == 3]

    # For binary procs: only ONE possible transition at each context.
    # fire: 0->1 or 1->0. So f(p, L, S, R) = 1-S when firing.
    # For non-firing: f(p, L, S, R) = S.
    # The question is: WHICH proc fires? That's determined by the mover word.
    # For the transition function: we need to define, for each proc,
    # what it does when it fires.

    # For binary: always flips. One option.
    # For ternary: when firing from value S, goes to (S+1)%3 or (S+2)%3.
    #   But this can DEPEND on context (L, R).

    # Full transition function: for each proc p and each (L, S, R):
    #   if p fires: new value = ? (must be != S)
    #   if p doesn't fire: new value = S

    # For binary: 0 -> 1, 1 -> 0. Fixed.
    # For ternary: for each (L, S, R), choose one of {(S+1)%3, (S+2)%3}.
    #   L ranges over m_{left(p)}, R ranges over m_{right(p)}, S over {0,1,2}.
    #   Number of contexts: m_L * 3 * m_R.

    # For p=1 (ternary): left=0 (binary, 2 vals), right=2 (binary, 2 vals).
    #   Contexts: 2 * 3 * 2 = 12. Each has 2 choices. Total: 2^12 = 4096.
    # For p=3 (ternary): left=2 (binary, 2 vals), right=4 (binary, 2 vals).
    #   Contexts: 2 * 3 * 2 = 12. Each has 2 choices. Total: 2^12 = 4096.
    # Total: 4096 * 4096 ≈ 16.7M systems. Too many to enumerate.

    # HOWEVER: for the good cycle, we only need consistency at the VISITED contexts.
    # And the cycle has at most sum(ms) = 12 steps, visiting at most 12 configs.
    # So most contexts are unvisited.

    # Better approach: enumerate good cycles directly.
    # For each starting config and each sequence of movers:
    # Build the config sequence, checking that:
    #   - The mover fires to SOME valid new value
    #   - All non-movers stay
    #   - All configs distinct
    #   - Cycle closes
    #   - Transition consistent

    # This is what ra13_systematic_search.py does. It found 0 cycles.
    # But let me verify with a different approach: enumerate from the SYSTEM side.

    # Simplified: use only "pure" transition functions (same direction for all contexts).
    # This is what sweep cycles use (inc or dec per proc).

    # But we already checked: 0 consistent cycles with pure transitions.
    # Now check: do cycles exist with CONTEXT-DEPENDENT transitions?

    # For small n=5, let's do a targeted approach:
    # Generate mover words that are odd-winding non-uniform.
    # For each, try ALL possible firing transitions (DFS with backtracking).

    print(f"\n--- Phase 1: Verify n=5 exhaustive (better timeout) ---")

    def gen_words(n, ms, max_results=5000, timeout=30):
        target_cl = sum(ms)
        results = []
        t0 = time.time()
        def dfs(word, fc):
            if time.time() - t0 > timeout or len(results) >= max_results:
                return
            if len(word) == target_cl:
                if all(fc[p] == ms[p] for p in range(n)):
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

    words = gen_words(n, ms, max_results=5000, timeout=30)
    unique = {}
    for w in words:
        c = canonicalize(w)
        if c not in unique:
            unique[c] = w
    print(f"Total unique words: {len(unique)}")

    ow_nu = []
    sweep_nu = []
    ow_u = []
    sweep_u = []
    zero_w = []

    for w in unique.values():
        wl = list(w)
        W = total_displacement(wl, n)
        dirs = step_directions(wl, n)
        ns = [d for d in dirs if d != 0]
        uniform = not ns or all(d == ns[0] for d in ns)

        if W == 0:
            zero_w.append(wl)
        elif abs(W) == n:
            if uniform:
                ow_u.append(wl)
            else:
                ow_nu.append(wl)
        elif abs(W) == 2 * n:
            if uniform:
                sweep_u.append(wl)
            else:
                sweep_nu.append(wl)

    print(f"\nWord classification:")
    print(f"  Zero winding: {len(zero_w)}")
    print(f"  Odd-winding uniform: {len(ow_u)}")
    print(f"  Odd-winding non-uniform: {len(ow_nu)}")
    print(f"  Sweep uniform: {len(sweep_u)}")
    print(f"  Sweep non-uniform: {len(sweep_nu)}")

    # Now exhaustively search for consistent cycles for OW-NU words
    print(f"\n--- Phase 2: Exhaustive cycle search for {len(ow_nu)} OW-NU words ---")

    all_starts = list(iproduct(*[range(m) for m in ms]))
    total_found = 0
    t0 = time.time()

    for w_idx, wl in enumerate(ow_nu):
        L = len(wl)

        for start in all_starts:
            # DFS: at each step, choose new value for mover
            def dfs(t, configs, trans):
                nonlocal total_found
                if total_found > 0:
                    return  # found one, stop
                if t == L:
                    if tuple(configs[0]) == tuple(configs[-1]):
                        # Verify all distinct
                        config_set = set(tuple(c) for c in configs[:L])
                        if len(config_set) == L:
                            total_found += 1
                            print(f"\n  FOUND! word={wl}, start={start}")
                            print(f"  W={total_displacement(wl, n)}")
                    return

                mover = wl[t]
                cur = configs[t]
                old_val = cur[mover]

                for new_val in range(ms[mover]):
                    if new_val == old_val:
                        continue

                    nxt = list(cur)
                    nxt[mover] = new_val

                    # Check transition consistency
                    consistent = True
                    new_trans = dict(trans)
                    for p in range(n):
                        lp, rp = (p - 1) % n, (p + 1) % n
                        ctx = (p, cur[lp], cur[p], cur[rp])
                        val = new_val if p == mover else cur[p]
                        if ctx in new_trans:
                            if new_trans[ctx] != val:
                                consistent = False
                                break
                        else:
                            new_trans[ctx] = val

                    if not consistent:
                        continue

                    nxt_t = tuple(nxt)
                    # Check not duplicate (unless it's the closing step)
                    if t + 1 < L:
                        if nxt_t in set(tuple(c) for c in configs[:t+1]):
                            continue

                    configs.append(nxt)
                    dfs(t + 1, configs, new_trans)
                    configs.pop()

                    if total_found > 0:
                        return

            dfs(0, [list(start)], {})
            if total_found > 0:
                break

        if total_found > 0:
            break

        if (w_idx + 1) % 10 == 0:
            elapsed = time.time() - t0
            print(f"  Checked {w_idx+1}/{len(ow_nu)} words, {elapsed:.1f}s, found={total_found}")

    elapsed = time.time() - t0
    print(f"\n{'='*70}")
    print(f"RESULT: {total_found} odd-winding non-uniform consistent cycles found")
    print(f"Checked: {len(ow_nu)} words x {len(all_starts)} starting configs")
    print(f"Time: {elapsed:.1f}s")

    if total_found == 0:
        print("""
>>> CRITICAL FINDING: NO odd-winding non-uniform transition-consistent
    good cycles exist at n=5 with ms=[2,3,2,3,2] (sub-threshold). <<<

This means: the binary flip question is MOOT for this case.
If such cycles don't exist, WP5 (odd-winding non-consecutive isolated)
can be proved by showing non-existence directly, without needing
binary flip at all.

The proof path becomes:
  odd-winding + non-uniform + >=3 non-consecutive binary + fc=ms
  => such a mover word cannot have a transition-consistent config sequence
  => no such good cycle exists
  => vacuously False
""")
    else:
        print("\nCycles exist! Need to test binary flip on them.")

    # Phase 3: Also check the OTHER winding types for comparison
    print(f"\n--- Phase 3: What types DO have consistent cycles? ---")

    for label, word_list in [("sweep_uniform", sweep_u),
                              ("sweep_nonuniform", sweep_nu),
                              ("odd_uniform", ow_u),
                              ("zero_winding", zero_w)]:
        count = 0
        checked = 0
        for wl in word_list[:5]:
            for start in all_starts:
                found = [False]
                def dfs2(t, configs, trans):
                    if found[0]:
                        return
                    L2 = len(wl)
                    if t == L2:
                        if tuple(configs[0]) == tuple(configs[-1]):
                            config_set = set(tuple(c) for c in configs[:L2])
                            if len(config_set) == L2:
                                found[0] = True
                        return
                    mover = wl[t]
                    cur = configs[t]
                    old_val = cur[mover]
                    for new_val in range(ms[mover]):
                        if new_val == old_val:
                            continue
                        nxt = list(cur)
                        nxt[mover] = new_val
                        consistent = True
                        new_trans = dict(trans)
                        for p in range(n):
                            lp, rp = (p-1)%n, (p+1)%n
                            ctx = (p, cur[lp], cur[p], cur[rp])
                            val = new_val if p == mover else cur[p]
                            if ctx in new_trans:
                                if new_trans[ctx] != val:
                                    consistent = False
                                    break
                            else:
                                new_trans[ctx] = val
                        if not consistent:
                            continue
                        nxt_t = tuple(nxt)
                        if t + 1 < len(wl):
                            if nxt_t in set(tuple(c) for c in configs[:t+1]):
                                continue
                        configs.append(nxt)
                        dfs2(t + 1, configs, new_trans)
                        configs.pop()
                        if found[0]:
                            return

                dfs2(0, [list(start)], {})
                checked += 1
                if found[0]:
                    count += 1
                    break  # found one for this word
        total_words = len(word_list)
        print(f"  {label}: {count} words have consistent cycles (checked {min(5, total_words)} words)")


if __name__ == '__main__':
    main()
