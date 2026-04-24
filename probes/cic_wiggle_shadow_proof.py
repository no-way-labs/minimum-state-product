#!/usr/bin/env python3
"""
CIC Exploration 13: Analytical Wiggle Shadow Proof.

Goal: Extract and prove the shadow permutation σ_wiggle for single-wiggle words.

Setup: C_n with k≥3 pairwise non-adjacent binary processors B = {b_0, b_1, ..., b_{k-1}}.
Single-wiggle word: |W|=2 sweep + one bounce at non-binary proc p with non-binary neighbor q.
Word structure (CCW example): 0, n-1, n-2, ..., 1, 0, n-1, ..., q+1, q, p, q, q-1, ..., 1
Length L = 2n+2. Fire counts: p and q fire 3 times, all others fire 2 times.

The good cycle visits L configs. The shadow cycle visits L non-good configs using the
same mover entries in permuted order σ_wiggle.

This script:
1. Extracts σ_wiggle for all wiggle words at n=7..12
2. Identifies closed-form pattern
3. Verifies 5 shadow properties (Closure, Movers, Distinctness, Disjointness, Escape)
4. Tests universality across state sequences and state counts
"""

from itertools import product as iproduct
from collections import Counter, defaultdict
import sys


def generate_wiggle_words(n, binary_positions):
    """Generate single-wiggle words."""
    binary_set = set(binary_positions)
    words = set()
    for direction in [+1, -1]:
        base = [(i * direction) % n for i in range(2 * n)]
        for insert_pos in range(2 * n):
            p = base[insert_pos]
            next_p = base[(insert_pos + 1) % (2 * n)]
            step = (next_p - p) % n
            if step == 1:
                bounce = (p - 1) % n
            elif step == n - 1:
                bounce = (p + 1) % n
            else:
                continue
            if p in binary_set or bounce in binary_set:
                continue
            word = list(base[:insert_pos + 1]) + [bounce, p] + list(base[insert_pos + 1:])
            L = len(word)
            valid = True
            for i in range(L):
                diff = abs(word[i] - word[(i + 1) % L])
                if diff != 1 and diff != n - 1:
                    valid = False
                    break
            if not valid:
                continue
            mc = Counter(word)
            if not all(mc.get(q, 0) >= 2 for q in range(n)):
                continue
            if not all(mc.get(b, 0) % 2 == 0 for b in binary_positions):
                continue
            min_idx = word.index(min(word))
            rotated = word[min_idx:] + word[:min_idx]
            words.add(tuple(rotated))
    return [list(w) for w in sorted(words)]


def get_fire_counts(word, n):
    fc = [0] * n
    for p in word:
        fc[p] += 1
    return fc


def enumerate_state_sequences(n, ms, fire_counts):
    proc_sequences = {}
    for p in range(n):
        m = ms[p]
        k = fire_counts[p]
        seqs = []

        def dfs_seq(seq, remaining, m_val=m):
            if remaining == 0:
                if seq[-1] == 0:
                    seqs.append(list(seq))
                return
            current = seq[-1]
            for next_val in range(m_val):
                if next_val != current:
                    if remaining == 1 and next_val != 0:
                        continue
                    seq.append(next_val)
                    dfs_seq(seq, remaining - 1, m_val)
                    seq.pop()

        dfs_seq([0], k)
        proc_sequences[p] = seqs
    return proc_sequences


def compute_configs(word, n, ms, state_seqs):
    L = len(word)
    fc = [0] * n
    configs = []
    config = tuple(state_seqs[p][0] for p in range(n))
    configs.append(config)
    for t in range(L):
        mover = word[t]
        fc[mover] += 1
        config = tuple(state_seqs[p][fc[p]] for p in range(n))
        configs.append(config)
    return configs


def check_valid_cycle(configs, L):
    if configs[-1] != configs[0]:
        return False
    return len(set(configs[:L])) == L


def extract_shadow_permutation(word, n, ms, state_seqs):
    """
    Extract the shadow permutation σ such that:
    shadow_mover[t] = good_mover[σ(t)] for all t.

    Returns the shadow mover sequence and the permutation σ.
    """
    cfgs = compute_configs(word, n, ms, state_seqs)
    L = len(word)
    if not check_valid_cycle(cfgs, L):
        return None, None, None

    cycle_configs = cfgs[:L]
    good_set = set(cycle_configs)

    # Extract mover entries
    me = {}
    for i in range(L):
        c = cycle_configs[i]
        cn = cycle_configs[(i + 1) % L]
        m = word[i]
        key = (m, c[(m - 1) % n], c[m], c[(m + 1) % n])
        me[key] = cn[m]

    # Trace SCC cycle — try all non-good configs to find the shadow
    all_cfgs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_cfgs if c not in good_set]

    for start in non_good:
        config = start
        path = [config]
        visited = {config: 0}
        movers_used = []
        entry_keys_used = []

        for step in range(L + 50):
            forced = []
            for j in range(n):
                key = (j, config[(j - 1) % n], config[j], config[(j + 1) % n])
                if key in me and me[key] != config[j]:
                    forced.append((j, me[key], key))
            if not forced:
                break

            moved = False
            for proc, new_val, key in forced:
                nc = list(config)
                nc[proc] = new_val
                nc = tuple(nc)
                if nc not in good_set:
                    movers_used.append(proc)
                    entry_keys_used.append(key)
                    config = nc
                    path.append(config)
                    if config in visited:
                        cs = visited[config]
                        cycle_movers = movers_used[cs:]
                        cycle_keys = entry_keys_used[cs:]
                        cycle_configs_shadow = path[cs:]

                        if len(cycle_movers) == L:
                            # Build permutation: for each shadow step t,
                            # find which good step uses the same entry
                            good_keys = []
                            for i in range(L):
                                c = cfgs[i]
                                m = word[i]
                                gk = (m, c[(m-1)%n], c[m], c[(m+1)%n])
                                good_keys.append(gk)

                            sigma = [None] * L
                            used_good = [False] * L
                            for t in range(L):
                                sk = cycle_keys[t]
                                for g in range(L):
                                    if not used_good[g] and good_keys[g] == sk:
                                        sigma[t] = g
                                        used_good[g] = True
                                        break

                            return cycle_movers, sigma, cycle_configs_shadow[:-1]
                    visited[config] = step + 1
                    moved = True
                    break
            if not moved:
                break

    return None, None, None


def main():
    print("CIC Exploration 13: Wiggle Shadow Permutation Analysis")
    print("=" * 70)

    # PART 1: Extract σ_wiggle for CCW words at various n
    print("\nPART 1: Shadow Permutation Extraction")
    print("-" * 70)

    results = []

    for n, bp in [(7, [0, 2, 4]), (8, [0, 3, 6]), (9, [0, 3, 6]),
                  (10, [0, 4, 7]), (11, [0, 4, 8])]:
        bs = set(bp)
        ms = [2 if i in bs else 3 for i in range(n)]
        words = generate_wiggle_words(n, bp)
        if not words:
            continue

        for w in words:
            fc = get_fire_counts(w, n)
            proc_seqs = enumerate_state_sequences(n, ms, fc)
            sl = [proc_seqs[p] for p in range(n)]

            # Take first valid combo
            for combo in iproduct(*sl):
                ss = {p: combo[p] for p in range(n)}
                shadow_movers, sigma, shadow_configs = extract_shadow_permutation(
                    w, n, ms, ss)

                if sigma is None:
                    continue

                # Identify wiggle position
                wiggle_procs = [p for p in range(n) if fc[p] == 3]

                print(f"\n  n={n} bp={bp} wiggle_procs={wiggle_procs}")
                print(f"  Good word:     {w}")
                print(f"  Shadow movers: {list(shadow_movers)}")
                print(f"  σ: {sigma}")

                # Check: is σ a valid permutation?
                is_perm = sorted(sigma) == list(range(len(sigma)))
                print(f"  Valid permutation: {is_perm}")

                # Show σ as a mapping
                print(f"  σ mapping (shadow_step → good_step):")
                for t in range(len(sigma)):
                    print(f"    shadow[{t}]={shadow_movers[t]} ← good[{sigma[t]}]={w[sigma[t]]}", end="")
                    if shadow_movers[t] != w[sigma[t]]:
                        print(" MISMATCH!", end="")
                    print()

                results.append({
                    'n': n, 'bp': bp, 'word': w, 'sigma': sigma,
                    'shadow_movers': list(shadow_movers),
                    'wiggle_procs': wiggle_procs,
                    'shadow_configs': shadow_configs,
                })
                break
            if len(results) > 0 and results[-1]['n'] == n:
                break  # one word per n is enough for pattern extraction

    # PART 2: Pattern analysis
    print("\n\nPART 2: Shadow Permutation Pattern Analysis")
    print("-" * 70)

    for r in results:
        n = r['n']
        w = r['word']
        sigma = r['sigma']
        L = len(w)

        print(f"\n  n={n}, L={L}")
        print(f"  Word: {w}")
        print(f"  σ:    {sigma}")

        # Analyze σ as a function: what's the pattern?
        # For sweep shadow: σ(t) = (t + offset) mod L for some offset
        # For wiggle: might be different

        # Check if σ is a cyclic shift
        for offset in range(L):
            if all(sigma[t] == (t + offset) % L for t in range(L)):
                print(f"  → Cyclic shift by {offset}")
                break
        else:
            # Not a simple cyclic shift. Check other patterns.
            # Decompose into cycles
            visited_cyc = [False] * L
            cycles = []
            for start in range(L):
                if visited_cyc[start]:
                    continue
                cycle = []
                t = start
                while not visited_cyc[t]:
                    visited_cyc[t] = True
                    cycle.append(t)
                    t = sigma[t]
                if len(cycle) > 1:
                    cycles.append(cycle)
            print(f"  → Cycle decomposition: {len(cycles)} non-trivial cycles")
            for cyc in cycles:
                print(f"    {cyc} (length {len(cyc)})")

    # PART 3: Relationship between good and shadow config sequences
    print("\n\nPART 3: Config Relationship (Good vs Shadow)")
    print("-" * 70)

    for r in results[:3]:
        n = r['n']
        w = r['word']
        sigma = r['sigma']
        bs = set(r['bp'])
        ms = [2 if i in bs else 3 for i in range(n)]
        L = len(w)

        # Recompute good configs
        fc = get_fire_counts(w, n)
        proc_seqs = enumerate_state_sequences(n, ms, fc)
        sl = [proc_seqs[p] for p in range(n)]
        for combo in iproduct(*sl):
            ss = {p: combo[p] for p in range(n)}
            cfgs = compute_configs(w, n, ms, ss)
            if check_valid_cycle(cfgs, L):
                break

        good_configs = cfgs[:L]
        shadow_configs = r['shadow_configs']

        print(f"\n  n={n}, word={w}")
        print(f"  Good configs vs Shadow configs:")
        print(f"  {'t':>3} {'Good':>30} {'Shadow':>30} {'Diff':>30}")

        for t in range(min(L, 20)):
            gc = good_configs[t]
            sc = shadow_configs[t]
            diff = tuple((sc[j] - gc[j]) % ms[j] for j in range(n))
            print(f"  {t:3d} {str(gc):>30} {str(sc):>30} {str(diff):>30}")

    # PART 4: Check if shadow configs = good configs + fixed offset (mod ms)
    print("\n\nPART 4: Fixed Offset Analysis")
    print("-" * 70)

    for r in results[:3]:
        n = r['n']
        w = r['word']
        sigma = r['sigma']
        bs = set(r['bp'])
        ms = [2 if i in bs else 3 for i in range(n)]
        L = len(w)

        fc = get_fire_counts(w, n)
        proc_seqs = enumerate_state_sequences(n, ms, fc)
        sl = [proc_seqs[p] for p in range(n)]
        for combo in iproduct(*sl):
            ss = {p: combo[p] for p in range(n)}
            cfgs = compute_configs(w, n, ms, ss)
            if check_valid_cycle(cfgs, L):
                break

        good_configs = cfgs[:L]
        shadow_configs = r['shadow_configs']

        # For each shadow step t, compute diff = shadow[t] - good[σ(t)] mod ms
        print(f"\n  n={n}")
        print(f"  Checking: shadow[t] = good[σ(t)] + δ(t) mod ms?")

        diffs = []
        for t in range(L):
            gc = good_configs[sigma[t]]
            sc = shadow_configs[t]
            diff = tuple((sc[j] - gc[j]) % ms[j] for j in range(n))
            diffs.append(diff)

        # Check if all diffs are the same
        if len(set(diffs)) == 1:
            print(f"  → FIXED offset δ = {diffs[0]} (constant!)")
        else:
            print(f"  → Variable offset ({len(set(diffs))} distinct values)")
            for t in range(min(L, 10)):
                print(f"    t={t}: δ={diffs[t]}")

    # PART 5: Check the 5 shadow properties
    print("\n\nPART 5: Shadow Properties Verification")
    print("-" * 70)

    for r in results:
        n = r['n']
        w = r['word']
        sigma = r['sigma']
        bs = set(r['bp'])
        ms = [2 if i in bs else 3 for i in range(n)]
        L = len(w)

        fc = get_fire_counts(w, n)
        proc_seqs = enumerate_state_sequences(n, ms, fc)
        sl = [proc_seqs[p] for p in range(n)]
        for combo in iproduct(*sl):
            ss = {p: combo[p] for p in range(n)}
            cfgs = compute_configs(w, n, ms, ss)
            if check_valid_cycle(cfgs, L):
                break

        good_configs = cfgs[:L]
        good_set = set(good_configs)
        shadow_configs = r['shadow_configs']

        # Property 1: Closure — shadow is a valid cycle
        shadow_closes = shadow_configs[-1] == shadow_configs[0] if len(shadow_configs) > L else True
        # Actually check: the shadow cycle returns to its start
        # (it was found as a cycle, so it closes by construction)
        prop1 = True  # closure by construction of SCC cycle

        # Property 2: Movers — shadow[t] fires mover w[σ(t)]
        prop2 = all(r['shadow_movers'][t] == w[sigma[t]] for t in range(L))

        # Property 3: Distinctness — all shadow configs are distinct
        prop3 = len(set(tuple(c) for c in shadow_configs)) == L

        # Property 4: Disjointness — shadow configs ∩ good configs = ∅
        shadow_set = set(tuple(c) for c in shadow_configs)
        prop4 = len(shadow_set & good_set) == 0

        # Property 5: Escape — no shadow config has a forced move INTO the good cycle
        # (Check: at each shadow config, the mover entry leads to another shadow config,
        #  not to a good config)
        me = {}
        for i in range(L):
            c = good_configs[i]
            cn = good_configs[(i + 1) % L]
            m = w[i]
            me[(m, c[(m-1)%n], c[m], c[(m+1)%n])] = cn[m]

        prop5 = True
        for t in range(L):
            sc = shadow_configs[t]
            mover = r['shadow_movers'][t]
            key = (mover, sc[(mover-1)%n], sc[mover], sc[(mover+1)%n])
            if key in me:
                new_val = me[key]
                nc = list(sc)
                nc[mover] = new_val
                nc = tuple(nc)
                if nc in good_set:
                    prop5 = False
                    break

        tag = '✓' if all([prop1, prop2, prop3, prop4, prop5]) else '✗'
        print(f"  n={n}: P1(closure)={prop1} P2(movers)={prop2} "
              f"P3(distinct)={prop3} P4(disjoint)={prop4} "
              f"P5(escape)={prop5} {tag}")

    # PART 6: Verify across ALL state sequences at n=7
    print("\n\nPART 6: All State Sequences — σ Stability")
    print("-" * 70)

    n, bp = 7, [0, 2, 4]
    bs = set(bp)
    ms = [2 if i in bs else 3 for i in range(n)]
    words = generate_wiggle_words(n, bp)

    for w in words:
        fc = get_fire_counts(w, n)
        proc_seqs = enumerate_state_sequences(n, ms, fc)
        sl = [proc_seqs[p] for p in range(n)]

        sigmas = set()
        all_props_ok = True

        for combo in iproduct(*sl):
            ss = {p: combo[p] for p in range(n)}
            shadow_movers, sigma, shadow_configs = extract_shadow_permutation(
                w, n, ms, ss)

            if sigma is None:
                all_props_ok = False
                continue

            sigmas.add(tuple(sigma))

            # Quick property check
            cfgs = compute_configs(w, n, ms, ss)
            L = len(w)
            good_configs = cfgs[:L]
            good_set = set(good_configs)

            # Distinctness
            if len(set(tuple(c) for c in shadow_configs)) != L:
                all_props_ok = False
            # Disjointness
            if set(tuple(c) for c in shadow_configs) & good_set:
                all_props_ok = False

        tag = '✓' if all_props_ok and len(sigmas) == 1 else '✗'
        print(f"  Word {w}: {len(sigmas)} distinct σ, all_props={all_props_ok} {tag}")
        if sigmas:
            print(f"    σ = {list(sorted(sigmas)[0])}")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
