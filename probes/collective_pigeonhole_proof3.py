#!/usr/bin/env python3
"""
Collective Pigeonhole Part 3: Why does the V-word die?

The V-word [0,1,0,n-1,...,2,1,2,...,n-1] has NO entry conflict at any
binary proc. But the lower bound proof says it CAN'T support a valid system.
What kills it?

Check: shadow cycle, palindromic entry conflict at NON-binary procs,
SCC completion failure, etc.
"""

from itertools import product as iproduct
from collections import Counter, defaultdict


def enumerate_state_sequences(m, k):
    seqs = []
    def dfs(seq, remaining):
        if remaining == 0:
            if seq[-1] == 0:
                seqs.append(list(seq))
            return
        for nv in range(m):
            if nv != seq[-1]:
                if remaining == 1 and nv != 0:
                    continue
                seq.append(nv)
                dfs(seq, remaining - 1)
                seq.pop()
    dfs([0], k)
    return seqs


def build_good_cycle(word, n, ms, combo):
    L = len(word)
    ss = {p: combo[p] for p in range(n)}
    fcc = [0] * n
    configs = [tuple(ss[p][0] for p in range(n))]
    for t in range(L):
        fcc[word[t]] += 1
        configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:L])) != L:
        return None
    return configs[:L]


def check_all_proc_ec(word, n, ms, combo):
    """Check entry conflict at EVERY proc (not just binary)."""
    good = build_good_cycle(word, n, ms, combo)
    if good is None:
        return None
    L = len(word)
    ec_procs = []
    for j in range(n):
        mover_ctx = set()
        nonmover_ctx = set()
        for t in range(L):
            c = good[t]
            Lp = (j - 1) % n
            Rp = (j + 1) % n
            ctx = (c[Lp], c[j], c[Rp])
            if word[t] == j:
                mover_ctx.add(ctx)
            else:
                nonmover_ctx.add(ctx)
        if mover_ctx & nonmover_ctx:
            ec_procs.append(j)
    return ec_procs, good


def check_shadow_cycle(word, n, ms, good):
    """Check if the good cycle has a shadow cycle (the real obstruction).
    Shadow: for each config c in the cycle, define shadow s(c) by
    s(c)[p] = (m_p - 1 - c[p]) for all p. If s maps the cycle to
    a set disjoint from the cycle with proper structure -> shadow exists."""
    L = len(word)
    cycle_set = set(good)

    # Standard shadow: complement each coordinate
    shadow_configs = []
    for c in good:
        s = tuple((ms[p] - 1 - c[p]) % ms[p] for p in range(n))
        shadow_configs.append(s)

    shadow_set = set(shadow_configs)
    disjoint = len(cycle_set & shadow_set) == 0
    distinct = len(shadow_set) == L

    return {
        'disjoint': disjoint,
        'distinct': distinct,
        'shadow_in_cycle': len(cycle_set & shadow_set),
        'shadow_configs': shadow_configs,
    }


def check_transition_consistency(word, n, ms, good):
    """Check if there exists ANY consistent transition function.
    For each proc j, collect all (L,S,R) -> new_S mappings from the cycle.
    Check for contradictions: same (L,S,R) -> different new_S at mover steps,
    or same (L,S,R) -> identity AND change (mover vs nonmover clash)."""
    L = len(word)

    # For each proc, collect all observations
    proc_obs = {j: {} for j in range(n)}

    for t in range(L):
        c = good[t]
        cn = good[(t + 1) % L]
        mover = word[t]

        for j in range(n):
            Lp = (j - 1) % n
            Rp = (j + 1) % n
            ctx = (c[Lp], c[j], c[Rp])
            new_s = cn[j]
            is_mover = (j == mover)

            if ctx not in proc_obs[j]:
                proc_obs[j][ctx] = {'mover': set(), 'nonmover': set()}

            if is_mover:
                proc_obs[j][ctx]['mover'].add(new_s)
            else:
                proc_obs[j][ctx]['nonmover'].add(new_s)

    # Check consistency
    conflicts = []
    for j in range(n):
        for ctx, obs in proc_obs[j].items():
            L_val, S_val, R_val = ctx
            # Mover must produce new_S != S_val (otherwise not really moving)
            # Actually: new_S != S_val is required for mover
            for ms_val in obs['mover']:
                if ms_val == S_val:
                    conflicts.append((j, ctx, 'mover_identity', ms_val))

            # Nonmover must produce S_val (identity)
            for nms_val in obs['nonmover']:
                if nms_val != S_val:
                    conflicts.append((j, ctx, 'nonmover_change', nms_val))

            # Key: mover and nonmover at SAME context require DIFFERENT outputs
            # Mover: f(L,S,R) != S. Nonmover: f(L,S,R) = S.
            # These are CONTRADICTORY for the SAME function f.
            if obs['mover'] and obs['nonmover']:
                conflicts.append((j, ctx, 'EC',
                    f"mover->{obs['mover']}, nonmover->{obs['nonmover']}"))

    return proc_obs, conflicts


def main():
    print("=" * 80)
    print("V-WORD OBSTRUCTION ANALYSIS")
    print("=" * 80)

    for n in [5, 7, 9]:
        ms = [2, 2, 2] + [3] * (n - 3)
        v_word = [0, 1, 0] + list(range(n-1, 1, -1)) + list(range(1, n))
        L = len(v_word)

        print(f"\n{'='*70}")
        print(f"n = {n}, V-word = {v_word}")
        print(f"ms = {ms}")
        print(f"{'='*70}")

        fc = Counter(v_word)
        proc_seqs = {}
        for p in range(n):
            proc_seqs[p] = enumerate_state_sequences(ms[p], fc[p])
        sl = [proc_seqs[p] for p in range(n)]

        # Take first valid combo
        for combo in iproduct(*sl):
            good = build_good_cycle(v_word, n, ms, combo)
            if good is None:
                continue

            print(f"\nCombo: {[list(combo[p]) for p in range(n)]}")

            # 1. All-proc EC check
            result = check_all_proc_ec(v_word, n, ms, combo)
            if result is None:
                continue
            ec_procs, good = result
            print(f"EC at procs: {ec_procs if ec_procs else 'NONE'}")

            # 2. Shadow check
            shadow = check_shadow_cycle(v_word, n, ms, good)
            print(f"Shadow: disjoint={shadow['disjoint']}, distinct={shadow['distinct']}")
            if not shadow['disjoint']:
                overlap = set(good) & set(shadow['shadow_configs'])
                print(f"  Shadow-cycle overlap: {len(overlap)} configs")

            # 3. Transition consistency
            obs, conflicts = check_transition_consistency(v_word, n, ms, good)
            ec_conflicts = [c for c in conflicts if c[2] == 'EC']
            other_conflicts = [c for c in conflicts if c[2] != 'EC']
            print(f"Transition conflicts: {len(ec_conflicts)} EC, "
                  f"{len(other_conflicts)} other")

            if ec_conflicts:
                print("  EC conflicts:")
                for j, ctx, typ, detail in ec_conflicts[:5]:
                    print(f"    Proc {j}: ctx={ctx} -> {detail}")

            # 4. Context utilization per proc
            print(f"\nContext utilization:")
            for j in range(n):
                total_ctx = ms[(j-1) % n] * ms[j] * ms[(j+1) % n]
                mover_contexts = set()
                nonmover_contexts = set()
                for t in range(L):
                    c = good[t]
                    ctx = (c[(j-1)%n], c[j], c[(j+1)%n])
                    if v_word[t] == j:
                        mover_contexts.add(ctx)
                    else:
                        nonmover_contexts.add(ctx)
                used = len(mover_contexts | nonmover_contexts)
                overlap = mover_contexts & nonmover_contexts
                print(f"  Proc {j} (m={ms[j]}): {used}/{total_ctx} used, "
                      f"|mover|={len(mover_contexts)}, |nonmover|={len(nonmover_contexts)}, "
                      f"overlap={len(overlap)}")

            break  # Just first combo

        # 5. Check if the V-word is a sweep or wiggle
        dirs = []
        for t in range(L):
            d = (v_word[(t+1) % L] - v_word[t]) % n
            if d > n // 2:
                d -= n
            dirs.append(d)

        turnarounds = sum(1 for t in range(L) if dirs[t] != dirs[(t-1)%L])
        print(f"\nWord structure:")
        print(f"  Directions: {dirs}")
        print(f"  Turnarounds: {turnarounds}")
        is_sweep = turnarounds == 0
        is_zigzag = turnarounds == 2
        print(f"  Type: {'sweep' if is_sweep else 'zigzag' if is_zigzag else f'{turnarounds}-turn'}")

        # The V-word has structure: right, left, left, ..., left, right, right, ..., right
        # i.e., it's a zigzag (2 turnarounds)
        # Count consecutive same-direction
        runs = []
        cur_dir = dirs[0]
        cur_len = 1
        for i in range(1, L):
            if dirs[i] == cur_dir:
                cur_len += 1
            else:
                runs.append((cur_dir, cur_len))
                cur_dir = dirs[i]
                cur_len = 1
        runs.append((cur_dir, cur_len))
        print(f"  Runs: {runs}")


if __name__ == '__main__':
    main()
