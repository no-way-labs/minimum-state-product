#!/usr/bin/env python3
"""
RA12 Context Match Verification: Verify the exact palindromic context matching.

For the canonical palindromic walk [0,1,...,n-1, n-2,...,1,0, n-1]:
  CW phase: steps 0..n-1 → movers 0,1,...,n-1
  CCW phase: steps n..2n-1 → movers n-2,n-3,...,0,n-1

Wait, that's not quite right. Let me work out the canonical walk precisely.

Canonical palindromic walk for n=5:
  [0, 1, 2, 3, 4, 3, 2, 1, 0, 4]
  Step 0: mover 0, CW (0→1)
  Step 1: mover 1, CW (1→2)
  Step 2: mover 2, CW (2→3)
  Step 3: mover 3, CW (3→4)
  Step 4: mover 4, CCW (4→3)
  Step 5: mover 3, CCW (3→2)
  Step 6: mover 2, CCW (2→1)
  Step 7: mover 1, CCW (1→0)
  Step 8: mover 0, CCW (0→4)
  Step 9: mover 4, CW (4→0)

The turnaround is at step 3→4 (proc 3 fires CW, then proc 4 fires CCW).

For the context match at proc j during CW non-mover step and CCW mover step:
  CW non-mover step for j: when j+1 fires CW (step j+1), j is non-mover.
  CCW mover step for j: when j fires CCW (step 2n-2-j for our walk).

Let me compute this precisely and verify context match.
"""

from itertools import product as iproduct


def step_dir(word, t, n):
    L = len(word)
    curr = word[t]
    nxt = word[(t + 1) % L]
    d = (nxt - curr) % n
    return 1 if d == 1 else (-1 if d == n - 1 else 0)


def enumerate_state_sequences(m, k):
    if k == 0:
        return [[0]]
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


def build_configs(word, n, ms, combo):
    """Build config sequence from state-sequence combo."""
    L = len(word)
    ss = {p: combo[p] for p in range(n)}
    fcc = [0] * n
    configs = [tuple(ss[p][0] for p in range(n))]
    for t in range(L):
        fcc[word[t]] += 1
        configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
    return configs


def main():
    print("=" * 70)
    print("RA12 Context Match: Detailed palindromic context verification")
    print("=" * 70)

    for n in [5, 7, 9]:
        print(f"\n{'='*60}")
        print(f"n = {n}")
        print(f"{'='*60}")

        # Canonical palindromic walk: [0,1,...,n-1, n-2,...,1, 0, n-1]
        # This goes CW: 0→1→...→n-1, then CCW: n-1→n-2→...→0, then CW: 0→n-1
        # Wait, that gives:
        # word = [0, 1, 2, ..., n-1, n-2, ..., 1, 0, n-1]
        # Length = n + (n-2) + 2 = 2n. Good.
        #
        # Actually let's compute step by step:
        # pos sequence: 0, 1, 2, ..., n-1, n-2, ..., 1, 0, n-1, 0 (back to start)
        # movers: word[t] = pos[t], word goes 0,1,...,n-1,n-2,...,1,0,n-1
        # Hmm, word = positions visited. Let me just use the known walk.

        # The walk [0, 1, ..., n-1, n-2, ..., 1, 0, n-1] has:
        # word[0] = 0, word[1] = 1, ..., word[n-1] = n-1
        # word[n] = n-2, word[n+1] = n-3, ..., word[2n-3] = 1, word[2n-2] = 0, word[2n-1] = n-1
        word = list(range(n)) + list(range(n-2, 0, -1)) + [0, n-1]
        assert len(word) == 2 * n
        print(f"Canonical walk: {word}")

        # Show step structure
        for t in range(len(word)):
            d = step_dir(word, t, n)
            print(f"  step {t}: mover={word[t]}, dir={'CW' if d==1 else 'CCW'}")

        # Identify CW and CCW steps for each proc
        cw_step = {}  # proc → step where it fires CW
        ccw_step = {}  # proc → step where it fires CCW
        for t in range(len(word)):
            p = word[t]
            d = step_dir(word, t, n)
            if d == 1:
                cw_step[p] = t
            else:
                ccw_step[p] = t

        print(f"\nCW steps: {cw_step}")
        print(f"CCW steps: {ccw_step}")

        # For each interior proc j (not turnaround), identify:
        # - CW non-mover step: when right(j) fires CW (j is non-mover)
        # - CCW mover step: when j fires CCW (j is mover)
        # Then check context match.

        # The turnaround procs: the proc at the CW→CCW transition
        # In our walk: step n-2 is CW (mover=n-2→n-1), step n-1 is CW (mover=n-1→...)
        # Wait, step n-1: word[n-1] = n-1, word[n] = n-2. dir = (n-2 - (n-1)) % n = n-3. Not 1 or n-1 for n>4.
        # Hmm, let me recalculate.
        # word[n-1] = n-1, word[n] = n-2.
        # d = (n-2 - (n-1)) % n = (-1) % n = n-1.  That's CCW!
        # So step n-1: mover = n-1, dir = CCW.
        # step n-2: word[n-2] = n-2, word[n-1] = n-1. d = (n-1-(n-2))%n = 1. CW!
        # So the CW→CCW transition is between step n-2 (CW) and step n-1 (CCW).
        # Turnaround at proc n-1.

        # Second turnaround: step 2n-3: word[2n-3] = 1, word[2n-2] = 0. d = (0-1)%n = n-1. CCW.
        # step 2n-2: word[2n-2] = 0, word[2n-1] = n-1. d = (n-1-0)%n = n-1. CCW!
        # Hmm, that's also CCW. So no second CW→CCW transition.
        # step 2n-1: word[2n-1] = n-1, word[0] = 0. d = (0-(n-1))%n = (1-n)%n = 1. CW!
        # So step 2n-1 is CW. The CCW→CW transition is between step 2n-2 (CCW) and step 2n-1 (CW).
        # Turnaround at proc 0.

        # So turnaround procs are 0 and n-1 (the endpoints of the arc).
        # Interior procs: 1, 2, ..., n-2.

        interior = list(range(1, n-1))
        print(f"\nInterior procs: {interior}")

        # For ALL sub-threshold multisets, verify context match at interior procs
        if n == 5:
            test_ms_list = [
                [2, 2, 2, 3, 3],  # consecutive at 0,1,2
                [2, 3, 2, 3, 2],  # non-consecutive
            ]
        elif n == 7:
            test_ms_list = [
                [2, 2, 2, 3, 3, 3, 3],
                [2, 3, 2, 3, 2, 3, 3],
            ]
        else:
            test_ms_list = [
                [2, 2, 2, 3, 3, 3, 3, 3, 3],
                [2, 3, 2, 3, 2, 3, 3, 3, 3],
            ]

        for ms in test_ms_list:
            print(f"\n  ms = {ms}")
            binary_pos = [i for i in range(n) if ms[i] == 2]
            interior_binary = [b for b in binary_pos if b in interior]
            print(f"  binary: {binary_pos}, interior binary: {interior_binary}")

            fc = [0] * n
            for p in word:
                fc[p] += 1

            proc_seqs = {}
            for p in range(n):
                proc_seqs[p] = enumerate_state_sequences(ms[p], fc[p])

            sl = [proc_seqs[p] for p in range(n)]
            L = len(word)

            total_valid = 0
            context_match_count = 0
            context_mismatch_count = 0
            ec_from_match = 0

            for combo in iproduct(*sl):
                configs = build_configs(word, n, ms, combo)
                if configs[-1] != configs[0]:
                    continue
                if len(set(configs[:L])) != L:
                    continue
                total_valid += 1

                # For each interior proc j with right(j) binary:
                for j in interior:
                    rj = (j + 1) % n
                    if ms[rj] != 2:
                        continue

                    # CW non-mover step for j: when right(j) fires CW
                    # right(j) = j+1 fires CW at cw_step[j+1]
                    t_cw = cw_step.get(rj)
                    if t_cw is None:
                        continue

                    # CCW mover step for j: when j fires CCW
                    t_ccw = ccw_step.get(j)
                    if t_ccw is None:
                        continue

                    # Config at CW step (before right(j) fires)
                    c_cw = configs[t_cw]
                    # Config at CCW step (before j fires)
                    c_ccw = configs[t_ccw]

                    # Context of j at CW step
                    lj = (j - 1) % n
                    ctx_cw = (c_cw[lj], c_cw[j], c_cw[rj])

                    # Context of j at CCW step
                    ctx_ccw = (c_ccw[lj], c_ccw[j], c_ccw[rj])

                    if ctx_cw == ctx_ccw:
                        context_match_count += 1
                        # j is non-mover at t_cw, mover at t_ccw
                        # Non-mover: f(ctx) = S = c_cw[j]
                        # Mover: f(ctx) != S → EC!
                        # But only if j actually fires (changes value) at t_ccw
                        next_val_j = configs[t_ccw + 1][j] if t_ccw + 1 < len(configs) else configs[0][j]
                        if next_val_j != c_ccw[j]:
                            ec_from_match += 1
                    else:
                        context_mismatch_count += 1

            print(f"  Valid combos: {total_valid}")
            print(f"  Context matches (j interior, right(j) binary): {context_match_count}")
            print(f"  Context mismatches: {context_mismatch_count}")
            print(f"  EC from palindromic match: {ec_from_match}")
            if context_match_count > 0:
                print(f"  MATCH RATE: {context_match_count}/{context_match_count + context_mismatch_count} = "
                      f"{100*context_match_count/(context_match_count + context_mismatch_count):.1f}%")

            # Also check: for interior binary procs themselves (not left(binary))
            # Check if j is binary and the context at j's CW-nonmover and CCW-mover match
            print(f"\n  Checking context match at interior binary procs directly:")
            for combo in iproduct(*sl):
                configs = build_configs(word, n, ms, combo)
                if configs[-1] != configs[0]:
                    continue
                if len(set(configs[:L])) != L:
                    continue

                for b in interior_binary:
                    # j = b: check if context at CW non-mover step matches CCW mover step
                    # CW non-mover step for b: when right(b) fires CW
                    rb = (b + 1) % n
                    t_cw = cw_step.get(rb)
                    t_ccw = ccw_step.get(b)
                    if t_cw is None or t_ccw is None:
                        continue

                    c_cw = configs[t_cw]
                    c_ccw = configs[t_ccw]
                    lb = (b - 1) % n

                    ctx_cw = (c_cw[lb], c_cw[b], c_cw[rb])
                    ctx_ccw = (c_ccw[lb], c_ccw[b], c_ccw[rb])

                    if ctx_cw != ctx_ccw:
                        print(f"    MISMATCH at binary proc {b}: CW_ctx={ctx_cw}, CCW_ctx={ctx_ccw}")
                        print(f"    CW step {t_cw} config: {c_cw}")
                        print(f"    CCW step {t_ccw} config: {c_ccw}")
                        # Which component mismatched?
                        if c_cw[lb] != c_ccw[lb]:
                            print(f"      L mismatch: left({b})={lb}, ms[{lb}]={ms[lb]}")
                        if c_cw[b] != c_ccw[b]:
                            print(f"      S mismatch: proc {b}, ms[{b}]={ms[b]}")
                        if c_cw[rb] != c_ccw[rb]:
                            print(f"      R mismatch: right({b})={rb}, ms[{rb}]={ms[rb]}")
                break  # one combo check suffices

    print("\nDONE")


if __name__ == "__main__":
    main()
