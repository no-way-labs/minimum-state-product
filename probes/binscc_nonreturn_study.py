#!/usr/bin/env python3
"""binscc_nonreturn_study.py — Study the 4% of cycles with non-return conflict.

These cycles have entry conflict but NO proc returns to its start context.
What mechanism creates their conflict?
"""

import sys
from collections import Counter, defaultdict
import time


def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= 6 and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
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
        first = list(start)
        first[p] = (first[p] + 1) % ms[p]
        dfs([p], [1 if i == p else 0 for i in range(n)], tuple(first))
    return results


def build_cycle(ms, n, word):
    ell = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:ell])) != ell:
        return None
    return configs[:ell]


def check_return_conflict(ms, n, word, cycle):
    ell = len(cycle)
    for p in range(n):
        mL = (p - 1) % n
        mR = (p + 1) % n
        m_p = ms[p]
        p_steps = [s for s in range(ell) if word[s] == p]
        if len(p_steps) < m_p:
            continue
        for ri in range(0, len(p_steps), m_p):
            if ri + m_p > len(p_steps):
                break
            first_step = p_steps[ri]
            last_step = p_steps[ri + m_p - 1]
            c_first = cycle[first_step]
            first_ctx = (c_first[mL], c_first[p], c_first[mR])
            if ri + m_p < len(p_steps):
                next_p = p_steps[ri + m_p]
            else:
                next_p = p_steps[0]
            step = (last_step + 1) % ell
            while step != next_p:
                if word[step] != p:
                    c = cycle[step]
                    ctx = (c[mL], c[p], c[mR])
                    if ctx == first_ctx:
                        return True
                step = (step + 1) % ell
    return False


def main():
    n, ms = 5, [2, 3, 2, 3, 2]
    print(f"n={n} ms={ms}")
    print("Studying non-return conflict cycles\n")

    words = enumerate_mover_words(ms, n, 21)
    print(f"{len(words)} mover words")

    nonreturn = []

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue
        ell = len(cycle)

        rc = check_return_conflict(ms, n, word, cycle)
        if rc:
            continue

        # Has entry conflict?
        has_conflict = False
        conflict_info = []
        for p in range(n):
            mL = (p - 1) % n
            mR = (p + 1) % n
            mover_set = set()
            nonmover_set = set()
            mover_steps = {}
            nm_steps = defaultdict(list)
            for step in range(ell):
                c = cycle[step]
                ctx = (c[mL], c[p], c[mR])
                if word[step] == p:
                    mover_set.add(ctx)
                    mover_steps[ctx] = step
                else:
                    nonmover_set.add(ctx)
                    nm_steps[ctx].append(step)
            ov = mover_set & nonmover_set
            if ov:
                has_conflict = True
                for ctx in ov:
                    conflict_info.append((p, ctx, mover_steps[ctx],
                                          nm_steps[ctx]))

        if has_conflict:
            nonreturn.append((word, cycle, conflict_info))

    print(f"Non-return conflict cycles: {len(nonreturn)}")

    # Analyze lengths
    lengths = Counter(len(w) for w, _, _ in nonreturn)
    print(f"Length distribution: {dict(sorted(lengths.items()))}")

    # Analyze WHERE conflict occurs
    proc_counter = Counter()
    for _, _, cinfo in nonreturn:
        procs_with = set(p for p, _, _, _ in cinfo)
        for p in procs_with:
            proc_counter[p] += 1
    print(f"Conflict at proc: {dict(sorted(proc_counter.items()))}")

    # The key: what relationship between mover and nonmover steps?
    print("\nDetailed mechanism for first 10:")
    for word, cycle, cinfo in nonreturn[:10]:
        ell = len(cycle)
        print(f"\n  word len={ell}")
        for p, ctx, m_step, nm_steps_list in cinfo[:2]:
            print(f"    P{p} ctx={ctx}: "
                  f"mover@{m_step} nonmover@{nm_steps_list[:3]}")

            # What's the mover at the nonmover step?
            for ns in nm_steps_list[:2]:
                firer = word[ns]
                print(f"      step {ns}: firer=P{firer}, "
                      f"dist_from_p={min(abs(firer-p), n-abs(firer-p))}")

    # KEY ANALYSIS: for non-return cycles, is the conflict context a
    # DIFFERENT mover context from the first firing?
    print("\n\nKEY: Is conflict via CROSS-ROUND context matching?")
    print("(Mover at round 2 matches nonmover from round 1, or vice versa)")

    cross_round = 0
    same_round = 0

    for word, cycle, cinfo in nonreturn:
        ell = len(cycle)
        for p, ctx, m_step, nm_steps_list in cinfo:
            mL = (p - 1) % n
            mR = (p + 1) % n
            # Find ALL mover steps for p
            all_m_steps = [s for s in range(ell) if word[s] == p]
            m_p = ms[p]

            # Which round does the mover step belong to?
            m_round = all_m_steps.index(m_step) // m_p

            # Which round do nonmover steps belong to?
            # A nonmover step is between round boundaries
            for ns in nm_steps_list:
                # Find which round contains this nonmover step
                # Round i spans from all_m_steps[i*m_p] to
                # all_m_steps[(i+1)*m_p - 1]
                nr = -1
                num_rounds = len(all_m_steps) // m_p
                for r in range(num_rounds):
                    start = all_m_steps[r * m_p]
                    end = all_m_steps[min((r + 1) * m_p - 1,
                                          len(all_m_steps) - 1)]
                    # Check if ns is in this round's span
                    if start <= ns <= end:
                        nr = r
                        break
                    # Wrap-around case
                    if start > end:
                        if ns >= start or ns <= end:
                            nr = r
                            break

                if nr == m_round:
                    same_round += 1
                else:
                    cross_round += 1

    print(f"  Same round: {same_round}")
    print(f"  Cross round: {cross_round}")

    # PART 2: For non-return cycles, check inter-round state differences
    print("\n\nPART 2: INTER-ROUND STATE TRACKING")
    print("For non-return conflict: p's context at mover step matches")
    print("a nonmover step, but p didn't 'return' (full cycle context")
    print("didn't reappear). How?\n")

    # The conflict means: at mover step k, p sees (L, S, R).
    # At nonmover step j, p sees same (L, S, R).
    # But p didn't return to start context after completing a round.
    # This means: the matching comes from a DIFFERENT state of p's round.
    # Example: p fires at s=0 with (L1,0,R1), then at s=1 with (L2,1,R2).
    # Later p is nonmover at state 0 with (L1,0,R1) — but this happened
    # BEFORE p's return (p is still mid-round from a LATER round).

    # Actually: check if the conflict is always at binary procs
    bin_only = 0
    tern_only = 0
    both = 0
    for word, cycle, cinfo in nonreturn:
        at_bin = any(ms[p] == 2 for p, _, _, _ in cinfo)
        at_tern = any(ms[p] > 2 for p, _, _, _ in cinfo)
        if at_bin and at_tern:
            both += 1
        elif at_bin:
            bin_only += 1
        else:
            tern_only += 1
    print(f"Conflict at: binary only={bin_only}, "
          f"ternary only={tern_only}, both={both}")

    # For the binary conflicts: is it always UP/DOWN overlap?
    up_down_overlap = 0
    up_nm_overlap = 0
    down_nm_overlap = 0
    for word, cycle, cinfo in nonreturn:
        ell = len(cycle)
        for p, ctx, m_step, nm_steps_list in cinfo:
            if ms[p] != 2:
                continue
            # Is the mover S=0 (UP) or S=1 (DOWN)?
            if ctx[1] == 0:
                up_nm_overlap += 1
            else:
                down_nm_overlap += 1

    print(f"Binary conflict: UP context as nonmover={up_nm_overlap}, "
          f"DOWN context as nonmover={down_nm_overlap}")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
