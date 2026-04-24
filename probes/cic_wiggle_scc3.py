#!/usr/bin/env python3
"""
CIC Exploration 12c: Forced SCC via all valid config sequences.

Key insight: single-wiggle words don't close under incrementing transitions!
Ternary non-wiggle procs fire 2 times: state = 2 mod 3 ≠ 0. Need involutory transitions.

State sequences for each proc:
  Binary (fire 2 times): 0→1→0. Deterministic.
  Ternary non-wiggle (fire 2 times): 0→x→0, x ∈ {1,2}. 2 choices.
  Ternary wiggle (fire 3 times): 0→x→y→0 with x≠0, y≠x, y≠0.
    x=1 → y=2. x=2 → y=1. 2 choices.

Total config sequences: 2^(#ternary procs).
For n=9, k=3 binary: 2^6 = 64 sequences.

For each: compute configs, extract forced entries, check overlap + SCC.
"""

from itertools import product as iproduct
from collections import Counter, defaultdict
import sys


def generate_wiggle_words(n, binary_positions):
    """Generate single-wiggle words (|W|=2 sweep + one bounce)."""
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
    """Get firing count for each proc."""
    fc = [0] * n
    for p in word:
        fc[p] += 1
    return fc


def enumerate_state_sequences(n, ms, fire_counts):
    """
    Enumerate all valid state sequences for each proc.

    For proc p with m=ms[p] states and k=fire_counts[p] firings:
    State sequence: s_0=0, s_1, ..., s_k=0
    where each s_{i+1} ≠ s_i and s_k = s_0 = 0.

    Returns list of dicts: seq[p] = [s_0, s_1, ..., s_k]
    """
    # For each proc, enumerate valid sequences
    proc_sequences = {}
    for p in range(n):
        m = ms[p]
        k = fire_counts[p]
        seqs = []

        def dfs_seq(seq, remaining):
            if remaining == 0:
                if seq[-1] == 0:  # must return to initial
                    seqs.append(list(seq))
                return
            current = seq[-1]
            for next_val in range(m):
                if next_val != current:
                    # If this is the last step, must go to 0
                    if remaining == 1 and next_val != 0:
                        continue
                    # Can't end at 0 too early if more steps remain
                    seq.append(next_val)
                    dfs_seq(seq, remaining - 1)
                    seq.pop()

        dfs_seq([0], k)
        proc_sequences[p] = seqs

    return proc_sequences


def compute_configs(word, n, ms, state_seqs):
    """
    Given state sequences for each proc, compute the config at each time step.

    state_seqs: dict p -> [s_0, s_1, ..., s_k] where k = fire_counts[p]
    Config at time t: (state_seqs[0][fc_0(t)], state_seqs[1][fc_1(t)], ...)
    where fc_p(t) = number of times p has fired before time t.
    """
    L = len(word)
    fc = [0] * n  # current fire counts

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
    """Check if configs form a valid cycle (all distinct, closes)."""
    if configs[-1] != configs[0]:
        return False
    cycle_configs = configs[:L]
    return len(set(cycle_configs)) == L


def extract_entries_and_check(word, n, ms, configs):
    """Extract forced entries from a valid cycle and check overlap + SCC."""
    L = len(word)
    cycle_configs = configs[:L]
    good_set = set(cycle_configs)

    # Check overlap
    overlap_procs = []
    for p in range(n):
        mover_ctx = set()
        nonmover_ctx = set()
        for i in range(L):
            c = cycle_configs[i]
            ctx = (c[(p - 1) % n], c[p], c[(p + 1) % n])
            if word[i] == p:
                mover_ctx.add(ctx)
            else:
                nonmover_ctx.add(ctx)
        if mover_ctx & nonmover_ctx:
            overlap_procs.append(p)

    if overlap_procs:
        return {'blocked': True, 'reason': 'overlap', 'procs': overlap_procs}

    # Extract entries
    all_entries = {}
    mover_entries = {}
    binary_mover = {}

    for i in range(L):
        c = cycle_configs[i]
        c_next = cycle_configs[(i + 1) % L]
        mover = word[i]

        key = (mover, c[(mover-1)%n], c[mover], c[(mover+1)%n])
        all_entries[key] = c_next[mover]
        mover_entries[key] = c_next[mover]
        if ms[mover] == 2:
            binary_mover[key] = c_next[mover]

        for j in range(n):
            if j != mover:
                key2 = (j, c[(j-1)%n], c[j], c[(j+1)%n])
                all_entries[key2] = c[j]

    # Check SCC with Tarjan
    has_scc, sccs = check_scc_tarjan(ms, n, good_set, all_entries)
    has_scc_m, sccs_m = check_scc_tarjan(ms, n, good_set, mover_entries)
    has_scc_b, sccs_b = check_scc_tarjan(ms, n, good_set, binary_mover)

    return {
        'blocked': has_scc,
        'reason': 'scc' if has_scc else 'none',
        'scc_all': has_scc,
        'scc_mover': has_scc_m,
        'scc_binary': has_scc_b,
        'scc_sizes': [len(s) for s in sccs] if sccs else [],
        'n_mover': len(mover_entries),
        'n_entries': len(all_entries),
        'overlap_procs': [],
    }


def check_scc_tarjan(ms, n, good_set, required):
    """SCC check using Tarjan's algorithm."""
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = set(c for c in all_configs if c not in good_set)

    # Build adjacency
    adj = defaultdict(set)
    for config in non_good:
        for j in range(n):
            Lj = config[(j-1) % n]
            Sj = config[j]
            Rj = config[(j+1) % n]
            key = (j, Lj, Sj, Rj)
            if key in required and required[key] != Sj:
                new_config = list(config)
                new_config[j] = required[key]
                new_config = tuple(new_config)
                if new_config in non_good:
                    adj[config].add(new_config)

    # Tarjan
    index_counter = [0]
    stack = []
    lowlink = {}
    index = {}
    on_stack = set()
    sccs = []

    def strongconnect(v):
        index[v] = index_counter[0]
        lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack.add(v)
        for w in adj.get(v, set()):
            if w not in index:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], index[w])
        if lowlink[v] == index[v]:
            scc = []
            while True:
                w = stack.pop()
                on_stack.discard(w)
                scc.append(w)
                if w == v:
                    break
            if len(scc) > 1:
                sccs.append(scc)

    # Use iterative Tarjan to avoid recursion limit
    sys.setrecursionlimit(100000)
    for v in non_good:
        if v not in index:
            strongconnect(v)

    return len(sccs) > 0, sccs


def main():
    print("CIC Exploration 12c: All-Config-Sequence SCC Analysis")
    print("=" * 70)

    # PART 1: Analyze state sequence space
    print("\nPART 1: State Sequence Enumeration")
    print("-" * 70)

    configs_to_test = [
        (7, [0, 2, 4], [2, 3, 2, 3, 2, 3, 3]),
        (8, [0, 3, 6], [2, 3, 3, 2, 3, 3, 2, 3]),
        (9, [0, 3, 6], [2, 3, 3, 2, 3, 3, 2, 3, 3]),
    ]

    for n, bp, ms in configs_to_test:
        words = generate_wiggle_words(n, bp)
        if not words:
            print(f"  n={n}: 0 wiggle words")
            continue

        w = words[0]  # take first word
        fc = get_fire_counts(w, n)
        proc_seqs = enumerate_state_sequences(n, ms, fc)

        total_combos = 1
        for p in range(n):
            ns = len(proc_seqs[p])
            total_combos *= ns
            if ns > 1:
                print(f"  n={n} proc {p} (m={ms[p]}, fires={fc[p]}): "
                      f"{ns} sequences: {proc_seqs[p][:3]}{'...' if ns > 3 else ''}")

        print(f"  n={n}: Total combinations = {total_combos}")

    # PART 2: For each word × state sequence combo, check overlap + SCC
    print("\n\nPART 2: Full Analysis — All Words × All State Sequences")
    print("-" * 70)

    for n, bp, ms in configs_to_test:
        words = generate_wiggle_words(n, bp)
        if not words:
            continue

        print(f"\n  n={n} bp={bp} ms={ms}")
        print(f"  {len(words)} wiggle words")

        total_combos_checked = 0
        total_valid = 0
        total_overlap = 0
        total_scc = 0
        total_scc_mover = 0
        total_scc_binary = 0
        total_unblocked = 0

        unblocked_details = []

        for w_idx, w in enumerate(words):
            fc = get_fire_counts(w, n)
            proc_seqs = enumerate_state_sequences(n, ms, fc)

            # Generate all combinations
            seq_lists = [proc_seqs[p] for p in range(n)]

            for combo in iproduct(*seq_lists):
                total_combos_checked += 1
                state_seqs = {p: combo[p] for p in range(n)}

                configs = compute_configs(w, n, ms, state_seqs)
                L = len(w)

                if not check_valid_cycle(configs, L):
                    continue

                total_valid += 1

                result = extract_entries_and_check(w, n, ms, configs)

                if result.get('reason') == 'overlap':
                    total_overlap += 1
                elif result.get('scc_all'):
                    total_scc += 1
                    if result.get('scc_mover'):
                        total_scc_mover += 1
                    if result.get('scc_binary'):
                        total_scc_binary += 1
                else:
                    total_unblocked += 1
                    if len(unblocked_details) < 3:
                        unblocked_details.append({
                            'word': w,
                            'state_seqs': {p: list(combo[p]) for p in range(n)},
                            'result': result,
                        })

        blocked = total_overlap + total_scc
        tag = '✓' if total_unblocked == 0 and total_valid > 0 else '✗'
        print(f"  Combos checked: {total_combos_checked}")
        print(f"  Valid cycles: {total_valid}")
        print(f"  Overlap: {total_overlap}")
        print(f"  SCC (all entries): {total_scc}")
        print(f"    SCC (mover only): {total_scc_mover}")
        print(f"    SCC (binary mover): {total_scc_binary}")
        print(f"  Unblocked: {total_unblocked} {tag}")

        if unblocked_details:
            for d in unblocked_details[:2]:
                print(f"\n  UNBLOCKED: word={d['word']}")
                for p, seq in sorted(d['state_seqs'].items()):
                    if ms[p] > 2:
                        print(f"    proc {p}: {seq}")
                print(f"    result: {d['result']}")

    # PART 3: Exploration 11 actual survivors
    print("\n\nPART 3: Exploration 11 Survivors")
    print("-" * 70)

    survivors = [
        ([0,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,2,1], 9, [0,3,6]),
        ([0,8,7,6,5,4,3,2,1,0,8,7,6,5,4,5,4,3,2,1], 9, [0,3,6]),
        ([0,8,7,6,5,4,3,2,1,0,8,7,8,7,6,5,4,3,2,1], 9, [0,3,6]),
        ([0,7,6,5,4,3,2,1,0,7,6,5,4,5,4,3,2,1], 8, [0,3,6]),
    ]

    for w, n_val, bp_val in survivors:
        ms_val = [2 if i in set(bp_val) else 3 for i in range(n_val)]

        mc = Counter(w)
        fair = all(mc.get(p, 0) >= 2 for p in range(n_val))
        bpar = all(mc.get(b, 0) % 2 == 0 for b in bp_val)
        if not (fair and bpar):
            print(f"  SKIP: {w[:10]}...")
            continue

        fc = get_fire_counts(w, n_val)
        proc_seqs = enumerate_state_sequences(n_val, ms_val, fc)
        seq_lists = [proc_seqs[p] for p in range(n_val)]

        total_combos = 1
        for p in range(n_val):
            total_combos *= len(proc_seqs[p])

        total_valid = 0
        total_blocked = 0
        total_overlap = 0
        total_scc = 0

        for combo in iproduct(*seq_lists):
            state_seqs = {p: combo[p] for p in range(n_val)}
            configs = compute_configs(w, n_val, ms_val, state_seqs)
            L = len(w)

            if not check_valid_cycle(configs, L):
                continue

            total_valid += 1
            result = extract_entries_and_check(w, n_val, ms_val, configs)

            if result.get('reason') == 'overlap':
                total_overlap += 1
                total_blocked += 1
            elif result.get('scc_all'):
                total_scc += 1
                total_blocked += 1

        tag = '✓' if total_blocked == total_valid and total_valid > 0 else '✗'
        print(f"  n={n_val} {w[:12]}...: combos={total_combos}, "
              f"valid={total_valid}, overlap={total_overlap}, "
              f"scc={total_scc}, unblocked={total_valid-total_blocked} {tag}")

    # PART 4: Binary-only analysis
    print("\n\nPART 4: What do binary mover entries look like?")
    print("-" * 70)

    # For a single-wiggle word, binary procs fire exactly twice.
    # Binary state is deterministic: 0→1→0.
    # The contexts at binary firings are determined by neighbor states.
    # The mover entries are: f_b(L_up, 0, R_up) = 1 and f_b(L_down, 1, R_down) = 0.
    # These are FULLY determined (transition-function-independent for binary).
    # The non-mover entries at binary: f_b(L, S, R) = S (stay).

    # Question: which (L, S, R) contexts appear as non-mover at binary procs?
    # If any non-mover context matches a mover context → overlap (contradiction).

    n, bp = 9, [0, 3, 6]
    ms = [2 if i in set(bp) else 3 for i in range(n)]
    words = generate_wiggle_words(n, bp)

    for w in words[:3]:
        fc = get_fire_counts(w, n)
        proc_seqs = enumerate_state_sequences(n, ms, fc)
        seq_lists = [proc_seqs[p] for p in range(n)]

        print(f"\n  Word: {w}")

        # For each valid state sequence combo
        for combo in iproduct(*seq_lists):
            state_seqs = {p: combo[p] for p in range(n)}
            configs = compute_configs(w, n, ms, state_seqs)
            L = len(w)

            if not check_valid_cycle(configs, L):
                continue

            cycle_configs = configs[:L]

            # Show binary contexts
            seq_desc = {p: combo[p] for p in range(n) if ms[p] > 2}
            print(f"    State seqs: {seq_desc}")

            for b in bp:
                mover_ctxs = []
                nonmover_ctxs = []
                for t in range(L):
                    c = cycle_configs[t]
                    ctx = (c[(b-1)%n], c[b], c[(b+1)%n])
                    if w[t] == b:
                        c_next = cycle_configs[(t+1)%L]
                        mover_ctxs.append((ctx, c_next[b]))
                    else:
                        nonmover_ctxs.append(ctx)

                mover_set = set(ctx for ctx, _ in mover_ctxs)
                nonmover_set = set(nonmover_ctxs)
                overlap = mover_set & nonmover_set

                print(f"      Binary {b}: mover={mover_ctxs}, "
                      f"overlap={'YES '+str(overlap) if overlap else 'no'}")

            break  # just show first valid combo

    sys.stdout.flush()


if __name__ == "__main__":
    main()
