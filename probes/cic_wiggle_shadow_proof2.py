#!/usr/bin/env python3
"""
CIC Exploration 13b: Waterfall structure and MNU for wiggle words.

The sweep shadow proof used:
1. Waterfall g_j[i] = fire count of proc j at the time proc i fires
2. MNU: each (proc, L_state, S_state, R_state) context is unique across all mover steps
3. Shadow offset: defined as a simple function of the waterfall

For wiggle words: the waterfall is "almost triangular" with perturbations at
the wiggle procs. MNU should still hold.

This script:
1. Compute the waterfall matrix for wiggle words
2. Verify MNU for all wiggle words at n=7..12
3. Compare waterfall to pure sweep
4. Identify the shadow offset formula
"""

from itertools import product as iproduct
from collections import Counter
import sys


def generate_wiggle_words(n, binary_positions):
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


def compute_waterfall(word, n):
    """
    Compute waterfall matrix g[j][i] = fire count of proc j just BEFORE
    the i-th firing step (step t where word[t] is the mover).

    Returns g[j][t] for j=0..n-1, t=0..L-1.
    """
    L = len(word)
    fc = [0] * n
    g = [[0] * L for _ in range(n)]

    for t in range(L):
        for j in range(n):
            g[j][t] = fc[j]
        fc[word[t]] += 1

    return g


def check_mnu(word, n, ms, state_seqs):
    """
    Check Mover Neighborhood Uniqueness:
    Each mover step has unique (proc, L_state, S_state, R_state).

    state_seqs[p] = [s_0, s_1, ..., s_k] where k = fire_count[p].
    State of proc p after j firings = state_seqs[p][j].
    """
    L = len(word)
    g = compute_waterfall(word, n)

    contexts = set()
    for t in range(L):
        p = word[t]
        left = (p - 1) % n
        right = (p + 1) % n

        # State of each proc at time t = state_seqs[proc][fire_count_before_t]
        L_state = state_seqs[left][g[left][t]]
        S_state = state_seqs[p][g[p][t]]
        R_state = state_seqs[right][g[right][t]]

        ctx = (p, L_state, S_state, R_state)
        if ctx in contexts:
            return False, ctx  # MNU violation
        contexts.add(ctx)

    return True, None


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


def main():
    print("CIC Exploration 13b: Waterfall + MNU for Wiggle Words")
    print("=" * 70)

    # PART 1: Waterfall matrix visualization
    print("\nPART 1: Waterfall Matrix")
    print("-" * 70)

    n, bp = 8, [0, 3, 6]
    bs = set(bp)

    # Pure sweep
    sweep = [i % n for i in range(2 * n)]
    g_sweep = compute_waterfall(sweep, n)
    print(f"\n  Pure CW sweep: {sweep}")
    print(f"  Waterfall g[j][t] (fire count of j before step t):")
    print(f"  {'':>4}", end="")
    for t in range(len(sweep)):
        print(f" t={t:2d}", end="")
    print()
    for j in range(n):
        bt = 'B' if j in bs else 'T'
        print(f"  j={j}({bt})", end="")
        for t in range(len(sweep)):
            marker = '*' if sweep[t] == j else ' '
            print(f"  {g_sweep[j][t]:2d}{marker}", end="")
        print()

    # Wiggle word
    words = generate_wiggle_words(n, bp)
    w = words[0]
    g_wig = compute_waterfall(w, n)
    print(f"\n  Wiggle word: {w}")
    print(f"  Waterfall g[j][t]:")
    print(f"  {'':>4}", end="")
    for t in range(len(w)):
        print(f" t={t:2d}", end="")
    print()
    for j in range(n):
        bt = 'B' if j in bs else 'T'
        print(f"  j={j}({bt})", end="")
        for t in range(len(w)):
            marker = '*' if w[t] == j else ' '
            print(f"  {g_wig[j][t]:2d}{marker}", end="")
        print()

    # PART 2: MNU verification
    print("\n\nPART 2: MNU Verification")
    print("-" * 70)

    for n, bp in [(7, [0, 2, 4]), (8, [0, 3, 6]), (9, [0, 3, 6]),
                  (10, [0, 4, 7]), (11, [0, 4, 8]), (12, [0, 4, 8])]:
        bs = set(bp)
        words = generate_wiggle_words(n, bp)
        if not words:
            print(f"  n={n}: 0 words")
            continue

        for m_nonbin in [3, 4]:
            ms = [2 if i in bs else m_nonbin for i in range(n)]
            total = 0
            mnu_pass = 0
            mnu_fail = 0

            for w in words:
                fc = [0] * n
                for p in w:
                    fc[p] += 1
                proc_seqs = enumerate_state_sequences(n, ms, fc)
                sl = [proc_seqs[p] for p in range(n)]

                for combo in iproduct(*sl):
                    ss = {p: combo[p] for p in range(n)}
                    total += 1
                    ok, viol = check_mnu(w, n, ms, ss)
                    if ok:
                        mnu_pass += 1
                    else:
                        mnu_fail += 1
                        if mnu_fail <= 3:
                            print(f"    MNU FAIL: n={n} m={m_nonbin} word={w} "
                                  f"violation at {viol}")

            tag = '✓' if mnu_fail == 0 else '✗'
            print(f"  n={n} m_nonbin={m_nonbin}: {mnu_pass}/{total} MNU pass {tag}")
        sys.stdout.flush()

    # PART 3: Waterfall difference (wiggle - sweep)
    print("\n\nPART 3: Waterfall Perturbation Analysis")
    print("-" * 70)

    for n, bp in [(7, [0, 2, 4]), (8, [0, 3, 6]), (9, [0, 3, 6])]:
        bs = set(bp)
        words = generate_wiggle_words(n, bp)
        if not words:
            continue

        # Find a CW wiggle word
        for w in words:
            # Check if CW: first step goes from 0 to 1
            if len(w) > 1 and (w[1] - w[0]) % n == 1:
                break
        else:
            w = words[0]

        # Pure CW sweep
        sweep = [i % n for i in range(2 * n)]
        g_sweep = compute_waterfall(sweep, n)
        g_wig = compute_waterfall(w, n)

        # Find wiggle procs
        fc = [0] * n
        for p in w:
            fc[p] += 1
        wiggle_procs = [p for p in range(n) if fc[p] == 3]

        print(f"\n  n={n} bp={bp} wiggle={wiggle_procs}")
        print(f"  Sweep: {sweep} (L={len(sweep)})")
        print(f"  Wiggle: {w} (L={len(w)})")

        # The wiggle word has L=2n+2 steps, sweep has 2n.
        # Can't directly compare waterfalls (different lengths).
        # Instead: compare the fire count profiles at each proc's firing times.

        # For each proc p, list the fire counts of neighbors at p's firing times.
        print(f"\n  Fire count profiles at each proc's firing times:")
        for p in range(n):
            left = (p - 1) % n
            right = (p + 1) % n
            bt = 'B' if p in bs else ('W' if p in wiggle_procs else 'T')

            # Sweep firings
            sweep_times = [t for t in range(len(sweep)) if sweep[t] == p]
            sweep_profiles = [(g_sweep[left][t], g_sweep[p][t], g_sweep[right][t])
                              for t in sweep_times]

            # Wiggle firings
            wig_times = [t for t in range(len(w)) if w[t] == p]
            wig_profiles = [(g_wig[left][t], g_wig[p][t], g_wig[right][t])
                            for t in wig_times]

            print(f"    Proc {p}({bt}): sweep={sweep_profiles}, wiggle={wig_profiles}")

    # PART 4: Context pattern — what makes MNU work?
    print("\n\nPART 4: Context Pattern Analysis")
    print("-" * 70)

    n, bp = 9, [0, 3, 6]
    bs = set(bp)
    ms = [2 if i in bs else 3 for i in range(n)]
    words = generate_wiggle_words(n, bp)
    w = words[0]

    fc = [0] * n
    for p in w:
        fc[p] += 1
    proc_seqs = enumerate_state_sequences(n, ms, fc)
    sl = [proc_seqs[p] for p in range(n)]

    # Take first valid state sequence
    for combo in iproduct(*sl):
        ss = {p: combo[p] for p in range(n)}
        ok, _ = check_mnu(w, n, ms, ss)
        if ok:
            break

    g = compute_waterfall(w, n)

    print(f"  n={n} word={w}")
    print(f"  State seqs: {dict((p, combo[p]) for p in range(n) if ms[p] > 2)}")
    print(f"\n  Step-by-step mover contexts:")
    print(f"  {'t':>3} {'mover':>5} {'type':>4} {'L_fc':>4} {'S_fc':>4} {'R_fc':>4} "
          f"{'L_st':>4} {'S_st':>4} {'R_st':>4}")

    for t in range(len(w)):
        p = w[t]
        left = (p - 1) % n
        right = (p + 1) % n
        bt = 'B' if p in bs else 'T'

        L_fc = g[left][t]
        S_fc = g[p][t]
        R_fc = g[right][t]

        L_st = ss[left][L_fc]
        S_st = ss[p][S_fc]
        R_st = ss[right][R_fc]

        print(f"  {t:3d} {p:5d} {bt:>4} {L_fc:4d} {S_fc:4d} {R_fc:4d} "
              f"{L_st:4d} {S_st:4d} {R_st:4d}")

    # PART 5: Non-mover contexts at binary procs — what do they see?
    print("\n\nPART 5: Binary Non-Mover Contexts")
    print("-" * 70)

    print(f"  For each binary proc, show ALL (L_st, S_st, R_st) contexts:")
    print(f"  (mover contexts are marked with *, non-mover with .)")
    print()

    for b in bp:
        left = (b - 1) % n
        right = (b + 1) % n
        print(f"  Binary {b} (L={left}, R={right}):")

        for t in range(len(w)):
            L_fc = g[left][t]
            S_fc = g[b][t]
            R_fc = g[right][t]
            L_st = ss[left][L_fc]
            S_st = ss[b][S_fc]
            R_st = ss[right][R_fc]

            marker = '*' if w[t] == b else '.'
            print(f"    t={t:2d} {marker} ({L_st},{S_st},{R_st})  "
                  f"fc=({L_fc},{S_fc},{R_fc})  mover={w[t]}")

    # PART 6: Key question — can we prove MNU analytically?
    print("\n\nPART 6: MNU Analytical Argument")
    print("-" * 70)

    # For MNU: need each (proc, L_st, S_st, R_st) unique.
    # For binary: S_st ∈ {0,1}, so (proc, L_st, S_st, R_st) has ≤ 2 possible S values.
    # Binary fires twice → 2 contexts. If S_st differs (0 and 1), we need (L_st, R_st)
    # to be different from all non-mover contexts at the same binary proc.
    #
    # For ternary non-wiggle: S_st ∈ {0, x}, fires twice.
    # For ternary wiggle: S_st ∈ {0, x, y}, fires thrice.
    #
    # MNU requires: no two mover steps at the same proc have the same (L_st, S_st, R_st).
    # For binary with 2 firings: S_st = 0 and S_st = 1 → automatically distinct in S.
    # So binary MNU is trivially satisfied (different S values).
    #
    # For ternary non-wiggle with 2 firings: S_st = 0 and S_st = x.
    # Need (L_st_1, R_st_1) ≠ (L_st_2, R_st_2) OR x ≠ 0 suffices (distinct S).
    # Since x ∈ {1,2} ≠ 0: ternary non-wiggle MNU trivially satisfied.
    #
    # For ternary wiggle with 3 firings: S_st = 0, x, y (all distinct for m=3).
    # So all 3 contexts have different S → MNU trivially satisfied!
    #
    # WAIT: This means MNU is TRIVIALLY TRUE for wiggle words!
    # Each proc fires with a different S_state at each firing (because the state
    # sequence is a permutation of {0, 1, ..., fire_count-1} mod m).

    print("  MNU ANALYSIS:")
    print("  For any proc p firing k times with state sequence [s_0, s_1, ..., s_k]:")
    print("  At firing j, S_state = s_j.")
    print("  If all s_0, ..., s_{k-1} are distinct (mod m), MNU is trivially satisfied.")
    print()
    print("  State sequences for single-wiggle words (m=3):")
    print("    Binary (k=2): [0, 1, 0] → s_0=0, s_1=1. Distinct. ✓")
    print("    Ternary non-wiggle (k=2): [0, x, 0] → s_0=0, s_1=x. x≠0 → distinct. ✓")
    print("    Ternary wiggle (k=3): [0, x, y, 0] → s_0=0, s_1=x, s_2=y. All distinct (m=3). ✓")
    print()
    print("  Therefore: MNU holds TRIVIALLY for all single-wiggle words with m ≥ 3.")
    print("  This is because each proc's state sequence has all-distinct intermediate values.")
    print()

    # Verify this claim
    print("  Verification: all intermediate states distinct?")
    for n_val, bp_val in [(7, [0, 2, 4]), (8, [0, 3, 6]), (9, [0, 3, 6])]:
        bs_val = set(bp_val)
        for m_val in [3, 4, 5]:
            ms_val = [2 if i in bs_val else m_val for i in range(n_val)]
            ws = generate_wiggle_words(n_val, bp_val)
            if not ws:
                continue
            all_distinct = True
            for w_val in ws:
                fc_val = [0] * n_val
                for p in w_val:
                    fc_val[p] += 1
                ps_val = enumerate_state_sequences(n_val, ms_val, fc_val)
                for p in range(n_val):
                    for seq in ps_val[p]:
                        intermediate = seq[:-1]  # [s_0, s_1, ..., s_{k-1}]
                        if len(intermediate) != len(set(intermediate)):
                            all_distinct = False
                            print(f"    NOT distinct: n={n_val} m={m_val} proc={p} seq={seq}")
            if all_distinct:
                print(f"    n={n_val} m={m_val}: all intermediate states distinct ✓")

    print()
    print("  CONCLUSION: MNU for wiggle words follows from the fact that")
    print("  each proc's intermediate states are all distinct.")
    print("  This is EXACTLY the same argument as for sweep words.")
    print("  No waterfall analysis needed for MNU!")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
